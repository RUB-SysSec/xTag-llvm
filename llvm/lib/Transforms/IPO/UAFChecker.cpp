#define DF_PTR_BITS  (34U)
#define DF_MTAG_BITS (4U)
#define DF_TAG_GRANULARITY_SHIFT (4)

#define DF_SHADOW_OFFSET_MASK ((1ULL << (DF_PTR_BITS - DF_TAG_GRANULARITY_SHIFT)) - 1)
#define DF_HEAP_MASK          ((1ULL << (DF_PTR_BITS + DF_MTAG_BITS)) - 1)

// perlbench needs this to be false as they pass invalidated pointers
// across function bondaries
#define VERIFY_CALL_ARGS true
#define LOOSE_POINTER_ARGS true

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/IntrinsicsX86.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ModuleSummaryIndex.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Demangle/Demangle.h"

#include "llvm/IR/Verifier.h"

#include <iostream>
#include <unordered_map>
#include <unordered_set>

#include <sys/file.h>


using namespace llvm;

namespace {
  class UAFChecker : public FunctionPass {

    public:

      static char ID;
      UAFChecker(const ModuleSummaryIndex* _summaryIndex) : FunctionPass(ID),
                                                            summaryIndex(_summaryIndex) { }

      bool runOnFunction(Function &F) override;

    private:
      const ModuleSummaryIndex* summaryIndex;
  };
}


char UAFChecker::ID = 0;


FunctionPass *
llvm::createUAFCheckerPass(const ModuleSummaryIndex* summaryIndex) {
  return new UAFChecker(summaryIndex);
}



static GlobalVariable *getOrInsertGlobal(Module &M, StringRef Name, Type *Ty) {
  GlobalVariable *GV = dyn_cast_or_null<GlobalVariable>(M.getNamedValue(Name));
  if (GV) {
    return GV;
  }
  return new GlobalVariable(M, Ty, true, GlobalVariable::ExternalLinkage,
                            nullptr, Name);
}


static Function* getOrInsertReporter(Module &M) {
  Type* voidTy = Type::getVoidTy(M.getContext());
  FunctionType *reporterTy = FunctionType::get(voidTy, false);
  return Function::Create(reporterTy, Function::ExternalWeakLinkage, "_df_report_violation", &M);
}


static bool call_might_free(CallBase* ci, const ModuleSummaryIndex* summaryIndex) {
  Function* callee = ci->getCalledFunction();
  if (!callee) {
    return true;
  }
  if (callee->doesNotFreeMemory()) {
    return false;
  }
  if (ci->getIntrinsicID() != Intrinsic::not_intrinsic) {
    return false;
  }

  if (callee->hasName() && summaryIndex) {
    ValueInfo VI = summaryIndex->getValueInfo(callee->getGUID());
    if (VI) {
      auto sl = VI.getSummaryList();
      if (sl.size()) {
        GlobalValueSummary* gvs = summaryIndex->getGlobalValueSummary(*callee);
        if (gvs) {
          FunctionSummary* fs = dyn_cast<FunctionSummary>(gvs);
          if (fs && fs->fflags().NoFree) {
            //llvm::errs() << "LTOnofree " << *ci << "\n";
            return false;
          }
        }
      }
    }
  }

  // we might add these?
  // @__cxa_allocate_exception
  // @__cxa_throw
  // @__cxa_begin_catch
  // @__cxa_rethrow
  // @__cxa_begin_catch
  // @__cxa_end_catch

  return true;
}

static bool is_skipped(Function& F) {
  StringRef sref = F.getName();

  // firefox allowlist to make it not crashy
  if (sref.find("_ZN16SkMallocPixelRefD", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("SkPath", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("SkPathEdgeIter", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("SkMakePixel", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("SkPixelRef", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("elementsRaw", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("DisplayItemClipChain", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("GetContainingPaintedLayerData", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("lerp_u8", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("LZ4HC_", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("LZ4_compressHC_continue_generic", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("ptr_at_xy", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("LZ4_saveDictHC", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("LZ4_resetStreamHC_fast", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("LZ4HC_compress_hashChain", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("CacheIndexEntryAutoManage", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("returnAddress", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("DestroyThreadPrivate", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("EventStateManager", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("sqlite3StrAccumEnlarge", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("XDRBuffer", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("emitThisEnvironmentCallee", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("GetPrefValue", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("RemoveModifiedFramesAndRects", 0) != StringRef::npos) {
    return true;
  }

  // SPEC2017 gcc
  if (sref.find("_cpp_clean_line", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("c_parser_postfix_expression_after_primary", 0) != StringRef::npos) {
    return true;
  }

  // SPEC2017 xalanc
  if (sref.find("_ZN11xalanc_1_1018XPathFunctionTable12DestroyTableEv", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("_ZSt8for_eachIPPKN11xalanc_1_108FunctionENS0_13DeleteFunctorIS1_EEET0_T_S8_S7_", 0) != StringRef::npos) {
    return true;
  }

  // SPEC2017 perlbenc
  if (sref.find("Perl_sv_force_normal_flags", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("Perl_sv_catpvn_flags", 0) != StringRef::npos) {
    return true;
  }

  return false;
}

bool is_skipped_call(CallBase* ci) {
  switch (ci->getIntrinsicID()) {
    case Intrinsic::memset:
      return false;
    case Intrinsic::memcpy:
      return false;
    case Intrinsic::memmove:
      return false;
    case Intrinsic::not_intrinsic:
      // non-intrinsics will be handled outside the switch
      break;
    default:
      // all other intrinsics are skipped
      return true;
  }

  // some functions take pointers to invalid memory regions but do
  // not deref them. this is unusual behavior we need to allowlist
  Function* callee = ci->getCalledFunction();
  if (!callee) {
    return false;
  }

  StringRef sref = callee->getName();

  // SPEC2017 gcc
  if (sref.find("vn_nary_op_lookup_pieces", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("vn_nary_op_insert_pieces", 0) != StringRef::npos) {
    return true;
  }
  if (sref.find("operation_could_trap_helper_p", 0) != StringRef::npos) {
    return true;
  }

  return false;
}


static bool vtable_in_tbaa_metadata(Value* value) {
  Instruction* insn = dyn_cast<Instruction>(value);
  if (!insn) {
    return false;
  }

  SmallVector<std::pair<unsigned, MDNode *>, 8> MDs;
  insn->getAllMetadata(MDs);
  bool isVtable = false;
  for (auto& md: MDs) {
    if (md.second->getNumOperands() == 0) {
      // maybe a bug in llvm? isTBAAVtableAccess crashes if 0 operands present
      continue;
    }
    if (md.second->isTBAAVtableAccess()) {
      isVtable = true;
      break;
    }
  }
  return isVtable;
}


static bool is_vtable_load_tbaa(LoadInst* loadInst) {
 Value* pointer = loadInst->getPointerOperand();
 if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(pointer)) {
   // might include an offset computation
   pointer = gep->getPointerOperand();
 }
 if (LoadInst* def = dyn_cast<LoadInst>(pointer)) {
   return vtable_in_tbaa_metadata(def);
 }
 else {
   return false;
 }
}

static bool is_vtable_load_heuristic(LoadInst* loadInst) {
  bool callFound = false;
  for (auto iter = loadInst->user_begin(); iter != loadInst->user_end(); ++iter) {
    Value* i = *iter;
    if (CallBase* callInst = dyn_cast<CallBase>(i)) {
      if (callInst->getIntrinsicID() != Intrinsic::not_intrinsic) {
        continue;
      }
      if (callInst->getCalledValue() == loadInst) {
        callFound = true;
        break;
      }
      else {
        return false;
      }
    }
    else {
      return false;
    }
  }

  if (!callFound) {
    return false;
  }

  Value* pointer = loadInst->getPointerOperand();
  if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(pointer)) {
    // might include an offset computation
    pointer = gep->getPointerOperand();
  }
  return isa<LoadInst>(pointer);
}

static bool is_vtable_load(LoadInst* loadInst) {
  if (is_vtable_load_tbaa(loadInst)) {
    return true;
  }
  if (is_vtable_load_heuristic(loadInst)) {
    return true;
  }
  return false;
}


class BBPtrState {
public:
  std::unordered_set<Value*> inMustUsed;
  std::unordered_set<Value*> inMayUsed;
  std::unordered_set<Value*> outMustUsed;
  std::unordered_set<Value*> outMayUsed;

  std::unordered_set<Value*> uses;
  std::unordered_set<Value*> usesOrBasedOn;

  std::list<Instruction*> ptrProp;
};

class BasedOnTree {
public:
  BasedOnTree(Function& F);
  BasedOnTree(const BasedOnTree& o) : pointerGroups(o.pointerGroups),
                                      lookup(o.lookup),
                                      roots(o.roots) {};

  Value* getPointerBase(Value* pointer) {
    auto search = lookup.find(pointer);
    // find, if not found return pointer
    if (search == lookup.end()) {
      return pointer;
    }
    else {
      // otherwise return tree base
      return search->second.first;
    }
  }

  const std::unordered_set<Value*> getPointerGroup(Value* pointer) {
    auto search = lookup.find(pointer);
    // find, if not found return pointer
    if (search == lookup.end()) {
      std::unordered_set<Value*> self;
      self.insert(pointer);
      return self;
    }
    else {
      return *search->second.second;
    }
  }

  const std::unordered_set<Value*>& getRoots () {
    return roots;
  }

  void dump();

private:
  std::vector<std::unordered_set<Value*>> pointerGroups;
  std::unordered_map<Value*, std::pair<Value*, std::unordered_set<Value*>*>> lookup;
  std::unordered_set<Value*> roots;
};


BasedOnTree::BasedOnTree(Function& F) {
  std::unordered_map<Value*, Value*> pointerToBase;
  std::vector<PHINode*> phiNodes;

  for (auto &BB : F) {
    for (BasicBlock::iterator i = BB.begin(), ie = BB.end(); i != ie; ++i) {
      Value *base, *derived;
      base = derived = nullptr;
      if (GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(&*i)) {
        base = gepInst->getPointerOperand();
        derived = gepInst;
      }
      else if (BitCastInst* bitcastInst = dyn_cast<BitCastInst>(&*i)) {
        if (!bitcastInst->getType()->isPointerTy()) {
          continue;
        }
        base = bitcastInst->getOperand(0);
        derived = bitcastInst;
      }
      else if (CallBase* ci = dyn_cast<CallBase>(&*i)) {
        // if a function returns one of its arguments we can find
        // another equivalency

        if (!ci->getType()->isPointerTy()) {
          continue;
        }
        Function* callee = ci->getCalledFunction();
        if (!callee) {
          continue;
        }

        for (Argument& arg: callee->args()) {
          if (!arg.getType()->isPointerTy()) {
            continue;
          }
          if (arg.hasReturnedAttr()) {
            derived = ci;
            base = ci->getArgOperand(arg.getArgNo());
            break;
          }
        }
      }
      else if (IntToPtrInst* inttoptr = dyn_cast<IntToPtrInst>(&*i)) {
        Value* op = inttoptr->getOperand(0);
        if (op->getType()->isIntegerTy(64)) {
          base = op;
          derived = inttoptr;
        }
      }
      else if (PtrToIntInst* ptrtoint = dyn_cast<PtrToIntInst>(&*i)) {
        base = ptrtoint->getOperand(0);
        derived = ptrtoint;
      }
      else if (PHINode* phiNode = dyn_cast<PHINode>(&*i)) {
        if (phiNode->getType()->isPointerTy()) {
          phiNodes.push_back(phiNode);
        }
      }
      else {
        continue;
      }

      if (base != derived) {
        pointerToBase[derived] = base;
      }
    }
  }

  // TODO: suboptimal runtime for long chains
  std::unordered_map<Value*, Value*> localLookup;
  for (auto& p2b: pointerToBase) {
    Value* pointer = p2b.first;
    Value* base = p2b.second;

    while (true) {
      auto search = pointerToBase.find(base);
      if (search == pointerToBase.end()) {
        break;
      }
      else {
        base = search->second;
      }
    }
    localLookup[pointer] = base;
  }

  // sometimes PHINodes form circles, we'd like to resolve them
  // to find the base of the allocation
  std::unordered_map<PHINode*, Value*> resolvedPHIs;
  for (PHINode* phiNode: phiNodes) {
    if (resolvedPHIs.find(phiNode) != resolvedPHIs.end()) {
      continue;
    }

    Value* externalValue = nullptr;
    std::unordered_set<PHINode*> seenPHIs;
    std::unordered_set<PHINode*> worklist;
    worklist.insert(phiNode);

    bool failed = false;
    while (!worklist.empty()) {
      std::unordered_set<PHINode*> newWorklist;
      for (PHINode* phi: worklist) {
        if (seenPHIs.find(phi) != seenPHIs.end()) {
          continue;
        }
        newWorklist.erase(phi);
        seenPHIs.insert(phi);

        for (unsigned i = 0; i < phi->getNumIncomingValues(); i++) {
          Value* ivalue = phi->getIncomingValue(i);
          auto search = localLookup.find(ivalue);
          if (search != localLookup.end()) {
            ivalue = search->second;
          }

          if (PHINode* newPHI = dyn_cast<PHINode>(ivalue)) {
            newWorklist.insert(newPHI);
          }
          //else if (isa<Constant>(ivalue) && cast<Constant>(ivalue)->isNullValue()) {
          //  // we can safely add null pointers
          //}
          else if (externalValue == nullptr) {
            externalValue = ivalue;
          }
          else if (externalValue == ivalue) {
            // fine
          }
          else {
            failed = true;
            break;
          }
        }
        if (failed) {
          break;
        }
      }
      if (failed) {
        break;
      }
      worklist = std::move(newWorklist);
    }

    if (!failed && externalValue) {
      for (PHINode* phi: seenPHIs) {
        resolvedPHIs[phi] = externalValue;
      }
    }
  }

  for (auto& resolved: resolvedPHIs) {
    Value* derived = resolved.first;
    Value* base = resolved.second;
    //llvm::errs() << "resolved phi " << *derived << " to " << *base << "\n";
    pointerToBase[derived] = base;
  }

  std::unordered_map<Value*, std::unordered_set<Value*>*> rootToGroup;
  for (auto& D: pointerToBase) {
    Value* base = D.second;
    if (pointerToBase.find(base) != pointerToBase.end()) {
      // not a root
      continue;
    }
    if (roots.find(base) != roots.end()) {
      // we already have a group
      continue;
    }
    roots.insert(base);
    pointerGroups.emplace_back();
  }

  int i = 0;
  for (Value* root: roots) {
    auto& group = pointerGroups[i];
    group.insert(root);
    rootToGroup[root] = &group;
    lookup[root] = std::make_pair(root, &group);
    i++;
  }

  // TODO: suboptimal runtime for long chains
  for (auto& p2b: pointerToBase) {
    Value* pointer = p2b.first;
    Value* base = p2b.second;

    while (true) {
      auto search = pointerToBase.find(base);
      if (search == pointerToBase.end()) {
        break;
      }
      else {
        base = search->second;
      }
    }
    auto group = rootToGroup.find(base)->second;
    group->insert(pointer);
    lookup[pointer] = std::make_pair(base, group);
  }
}

void BasedOnTree::dump() {
  for (Value* root: this->roots) {
    llvm::errs() << *root << "\n";
    for (Value* equiv: getPointerGroup(root)) {
      if (equiv == root) {
        continue;
      }
      llvm::errs() << "-> " << *equiv << "\n";
    }
  }
}


class BBProperties {
public:
  int level;
  bool frees;
  bool stores;
  Instruction* firstStore;

  BBProperties(int _level,
               bool _frees, bool _stores,
               Instruction* _firstStore) : level(_level),
                                           frees(_frees),
                                           stores(_stores),
                                           firstStore(_firstStore) {};

  BBProperties(const BBProperties& o) : level(o.level),
                                        frees(o.frees),
                                        stores(o.stores),
                                        firstStore(o.firstStore) {};
};


/* For each BB, compute whether it:
 * - contains a call to a function that might free() memory
 * - might store to memory (directly or within called functions)
 * - an integer indicating the depth of the BB during DFT
 */
std::unordered_map<BasicBlock*, BBProperties> compute_bb_properties(Function& F,
                                                                    const ModuleSummaryIndex* summaryIndex) {
  std::unordered_map<BasicBlock*, int> bb2level;
  for (auto I = po_begin(&F); I != po_end(&F); ++I) {
    BasicBlock* BB = *I;
    int level = 0;
    for (BasicBlock* Succ: llvm::successors(BB)) {
      auto search = bb2level.find(Succ);
      if (search == bb2level.end()) {
        continue;
      }
      int suc_level = search->second;
      if (suc_level >= level) {
        level = suc_level + 1;
      }
    }
    bb2level[BB] = level;
  }

  std::unordered_map<BasicBlock*, BBProperties> bbProps;
  for (auto &BB : F) {
    bool frees = false;
    bool stores = false;
    Instruction* firstStore = nullptr;
    for (BasicBlock::iterator i = BB.begin(), ie = BB.end(); i != ie; ++i) {
      Instruction* insn = &*i;
      if (isa<StoreInst>(insn)) {
        stores = true;
      }
      else if (CallBase* ci = dyn_cast<CallBase>(insn)) {
        Function* callee = ci->getCalledFunction();
        if (!callee || !callee->onlyReadsMemory()) {
          stores = true;
        }
        if (call_might_free(ci, summaryIndex)) {
          frees = true;
        }
      }
      if (stores && !firstStore)
        firstStore = insn;
    }
    int level = bb2level.find(&BB)->second;
    bbProps.emplace(&BB, BBProperties(level, frees, stores, firstStore));
  }

  return bbProps;
}


std::vector<BasicBlock*> relevantPredecessors(BasicBlock* BB, LoopInfo& LI,
                                              std::unordered_map<BasicBlock*, BBProperties>& bbPropsLookup) {
  // if our BB is a loop header and non of the blocks within the
  // loop frees() => we only need to consider predecessors outside
  // the loop w.r.t. forwards propagation
  std::vector<BasicBlock*> rPreds;

  bool optimized = false;
  if (LI.isLoopHeader(BB)) {
    Loop* loop = LI.getLoopFor(BB);
    Loop* iloop = LI.getLoopFor(BB);
    while (true) {
      Loop* parentLoop = loop->getParentLoop();
      if (!parentLoop) {
        break;
      }
      if (parentLoop->getHeader() != BB) {
        break;
      }
      loop = parentLoop;
    }

    bool frees = false;
    for (BasicBlock* lBB: loop->blocks()) {
      BBProperties& BBProps = bbPropsLookup.find(lBB)->second;
      if (BBProps.frees) {
        frees = true;
        break;
      }
    }

    if (!frees) {
      optimized = true;
      for (BasicBlock* Pred: llvm::predecessors(BB)) {
        if (!loop->contains(Pred) || (loop->getLoopPreheader() == Pred)) {
          rPreds.push_back(Pred);
        }
        else {
        }
      }
      if (rPreds.size() == 0) {
        __builtin_trap();
      }
    }
  }

  // otherwise all predecessors are relevant
  if (!optimized) {
    for (BasicBlock* Pred: llvm::predecessors(BB)) {
      rPreds.push_back(Pred);
    }
  }

  return rPreds;
}


enum CheckedStatus {
  NotChecked = 0,
  MaybeChecked = 1,
  IsChecked = 2
};


/* Identifies unchecked uses pointers
 */
class UncheckedUseAnalysis {
public:
  UncheckedUseAnalysis(Function& F, LoopInfo& LI,
                       BasedOnTree& basedOnTree,
                       std::unordered_map<BasicBlock*, BBProperties>& bbProps);
  // return a vector of uses which are no longer unchecked due to the
  // added check
  void addCheck(Value* pointer, BasicBlock* BB);
  std::vector<std::pair<Value*, BasicBlock*>> getUnchecked();
  CheckedStatus getCheckedStatus(Value* pointer, BasicBlock* BB);
  const std::vector<std::pair<Value*, BasicBlock*>>& getChecks() { return checks; }
  void dump();
  void dump(BasicBlock* BB);

private:
  std::vector<std::pair<Value*, BasicBlock*>> checks;

  std::unordered_set<Value*> unfreeable;
  std::unordered_map<BasicBlock*, BBPtrState> bb2state;
  std::unordered_map<BasicBlock*, BBProperties> bb2props;
  std::unordered_set<BasicBlock*> worklist;
  std::unordered_map<BasicBlock*, std::vector<BasicBlock*>> relevantPreds;

  BasedOnTree basedOnTree;

  void iterate();
  void pointerPropagate(BasicBlock* BB);
  void meet(BasicBlock* BB);
  void transfer(BasicBlock* BB);
};


void UncheckedUseAnalysis::dump(BasicBlock* BB) {
  auto ele = this->bb2state.find(BB);

  llvm::errs() << *ele->first << "\n";
  llvm::errs() << "===in may\n";
  for (Value* v: ele->second.inMayUsed) {
    llvm::errs() << *v << "\n";
  }
  llvm::errs() << "===in must\n";
  for (Value* v: ele->second.inMustUsed) {
    llvm::errs() << *v << "\n";
  }
  llvm::errs() << "===out may\n";
  for (Value* v: ele->second.outMayUsed) {
    llvm::errs() << *v << "\n";
  }
  llvm::errs() << "===out must\n";
  for (Value* v: ele->second.outMustUsed) {
    llvm::errs() << *v << "\n";
  }
  llvm::errs() << "===\n\n";
}

void UncheckedUseAnalysis::dump() {
  for (auto& ele: this->bb2state) {
    dump(ele.first);
  }
}


UncheckedUseAnalysis::UncheckedUseAnalysis(Function& F, LoopInfo& LI,
                                           BasedOnTree& _basedOnTree,
                                           std::unordered_map<BasicBlock*, BBProperties>& _bb2props) :
    bb2props(_bb2props),
    basedOnTree(_basedOnTree) {
  // forwards data flow:
  //
  // init: Unfreeable = Set of all pointers used/defined within this function
  //                    that must pointer to local (AllocInst) or global memory
  //       in_must = Unfreeable
  //       in_may  = empty
  // meet: in_must = intersect(out_must of all successors)
  //       in_may  = intersect(union(out_may of all successors), in_must)
  // transfer (if BB must not free):
  //       out_must = union(in_must, "Used" in this BB)
  //       out_may  = intersect(in_may, out_must)
  // transfer (if BB may free):
  //       out_must = Unfreeable
  //       out_may  = empty

  TargetLibraryInfoWrapperPass TLIWP;
  TargetLibraryInfo& TLI = TLIWP.getTLI(F);

  for (auto& BB : F) {
    this->relevantPreds[&BB] = relevantPredecessors(&BB, LI, _bb2props);
  }

  for (Value* root: this->basedOnTree.getRoots()) {
    if (isa<AllocaInst>(root) || isa<Constant>(root)) {
      // local stack and globals cannot be freed
      for (Value* v: this->basedOnTree.getPointerGroup(root)) {
        this->unfreeable.insert(v);
      }
    }
  }

  for (auto &BB : F) {
    std::unordered_set<Value*> usedValues;
    std::list<Instruction*> ptrProp;
    std::unordered_set<Value*> allocatedValues;

    for (BasicBlock::iterator i = BB.begin(), ie = BB.end(); i != ie; ++i) {
      Instruction* inst = &*i;

      // extract pointers used during BB
      if (LoadInst* loadInst = dyn_cast<LoadInst>(inst)) {
        if (!is_vtable_load(loadInst)) { // we ignore loads from the vtable entirely
          usedValues.insert(loadInst->getPointerOperand());
        }
      }
      else if (StoreInst* storeInst = dyn_cast<StoreInst>(inst)) {
        usedValues.insert(storeInst->getPointerOperand());
      }
      else if (CallBase* callbaseInst = dyn_cast<CallBase>(inst)) {
        if (is_skipped_call(callbaseInst)) {
          continue;
        }

        if (llvm::isAllocationFn(callbaseInst, &TLI, false)) {
          allocatedValues.insert(callbaseInst);
        }

        // TODO is this special case really worth it?
        if (llvm::isFreeCall(callbaseInst, &TLI)) {
          // the free() function in our mimalloc will check whether the
          // pointer is still valid
          continue;
        }

#if VERIFY_CALL_ARGS
        for (auto& arg: callbaseInst->args()) {
          if (arg->getType()->isPointerTy()) {
            usedValues.insert(arg);
          }
        }
#endif
      }

      // extract instructions which require special handling during
      // data flow analysis
      if (inst->getType()->isPointerTy() &&
          (isa<SelectInst>(inst) || isa<PHINode>(inst))) {
        if (basedOnTree.getPointerBase(inst) == inst) {
          ptrProp.push_back(inst);
        }
      }
    }

    // remove all trivially unfreeable pointer uses
    for (auto it = usedValues.begin(); it != usedValues.end(); ) {
      Value* v = *it;
      if (isa<Constant>(v) || isa<AllocaInst>(v) ||
          (this->unfreeable.find(v) != this->unfreeable.end())) {
        it = usedValues.erase(it);
      }
      else {
        it++;
      }
    }

    std::unordered_set<Value*> usedOrBasedOn;
    for (auto& ptr: usedValues) {
      for (Value* v: this->basedOnTree.getPointerGroup(ptr)) {
        usedOrBasedOn.insert(v);
      }
    }

    BBPtrState& bbPtrState = this->bb2state[&BB];
    bbPtrState.uses = std::move(usedValues);
    bbPtrState.usesOrBasedOn = std::move(usedOrBasedOn);
    bbPtrState.ptrProp = std::move(ptrProp);

    for (Value* allocated: allocatedValues) {
      for (Value* allocOrEquiv: this->basedOnTree.getPointerGroup(allocated)) {
        bbPtrState.inMustUsed.insert(allocOrEquiv);
      }
    }

#if VERIFY_CALL_ARGS
    // for the entry point we set the Value*s supplied as args to
    // be safe as well
    if (&BB == &F.getEntryBlock()) {
      for (auto& arg: F.args()) {
        if (arg.getType()->isPointerTy()) {
          for (Value* v: this->basedOnTree.getPointerGroup(&arg)) {
            //llvm::errs() << "adding arg or equiv " << *v << "\n";
            bbPtrState.inMustUsed.insert(v);
          }
        }
      }
    }
#endif
  }

  // initialize worklist with all BBs of function
  for (auto& BB: F) {
    this->worklist.insert(&BB);
  }

  this->iterate();
}


void UncheckedUseAnalysis::pointerPropagate(BasicBlock* BB) {
  BBPtrState& bbPtrState = this->bb2state.find(BB)->second;

  // we can declare the result of select/phi as Used if all inputs are Used
  for (auto it = bbPtrState.ptrProp.begin(); it != bbPtrState.ptrProp.end(); ) {
    Instruction* inst = *it;
    bool allUsed;
    bool anyUsed;

    if (SelectInst* selectInst = dyn_cast<SelectInst>(inst)) {
      Value* tPtr = this->basedOnTree.getPointerBase(selectInst->getTrueValue());
      Value* fPtr = this->basedOnTree.getPointerBase(selectInst->getFalseValue());

      bool tMust = isa<Constant>(tPtr) || isa<AllocaInst>(tPtr) ||
                   (bbPtrState.inMustUsed.find(tPtr) != bbPtrState.inMustUsed.end());
      bool fMust = isa<Constant>(fPtr) || isa<AllocaInst>(fPtr) ||
                   (bbPtrState.inMustUsed.find(fPtr) != bbPtrState.inMustUsed.end());

      allUsed = tMust && fMust;
      anyUsed = tMust || fMust;
    }
    else if (PHINode* phiNode = dyn_cast<PHINode>(inst)) {
      // if all incoming values for a PHI are safe => so is the result
      allUsed = true;
      anyUsed = false;
      for (unsigned i = 0; i < phiNode->getNumIncomingValues(); i++) {
        Value* ivalue = this->basedOnTree.getPointerBase(phiNode->getIncomingValue(i));
        BasicBlock* ibb = phiNode->getIncomingBlock(i);

        if (isa<Constant>(ivalue) || isa<AllocaInst>(ivalue)) {
          anyUsed = true;
          continue;
        }
        auto& phiOutMustUsed = bb2state.find(ibb)->second.outMustUsed;
        if (phiOutMustUsed.find(ivalue) != phiOutMustUsed.end()) {
          anyUsed = true; // could be more liberal by checking inMayUsed as well
        }
        else {
          allUsed = false;
        }
      }
    }
    else {
      llvm::errs() << "should be unreachable?\n";
      __builtin_trap();
    }

    if (allUsed) {
      for (Value* v: this->basedOnTree.getPointerGroup(inst)) {
        bbPtrState.inMustUsed.insert(v);
        bbPtrState.inMayUsed.erase(v);
      }
      it = bbPtrState.ptrProp.erase(it);
    }
    else if (anyUsed) {
      for (Value* v: this->basedOnTree.getPointerGroup(inst)) {
        if (bbPtrState.inMustUsed.find(v) != bbPtrState.inMustUsed.end()) {
          // assert none of the Value*s is in inMustUsed
          llvm::errs() << "insn " << *inst << " not in must used " << *v << "\n";
          __builtin_trap();
        }

        bbPtrState.inMayUsed.insert(v);
      }
      it++;
    }
    else {
      it++;
    }
  }
}

void UncheckedUseAnalysis::meet(BasicBlock* BB) {
  //llvm::errs() << *BB << "\n\n";
  BBPtrState& bbPtrState = this->bb2state.find(BB)->second;
  bool first = true;
  std::unordered_set<Value*> inMust;

  for (BasicBlock *Pred : this->relevantPreds.find(BB)->second) {
    BBPtrState& predState = bb2state.find(Pred)->second;
    for (Value* v: predState.outMustUsed) {
      bbPtrState.inMayUsed.insert(v);
    }
    for (Value* v: predState.outMayUsed) {
      bbPtrState.inMayUsed.insert(v);
    }

    if (first) {
      first = false;
      inMust = predState.outMustUsed;
      continue;
    }

    // intersect inMust with outMustUsed of predecessor
    for (auto it = inMust.begin(); it != inMust.end(); ) {
      if (predState.outMustUsed.find(*it) != predState.outMustUsed.end()) {
        it++;
      }
      else {
        it = inMust.erase(it);
      }
    }
  }

  for (Value* v: inMust) {
    bbPtrState.inMustUsed.insert(v);
  }
  // if a Value* is mustUsed it will not appear in mayUsed
  for (Value* v: bbPtrState.inMustUsed) {
    bbPtrState.inMayUsed.erase(v);
  }
}

void UncheckedUseAnalysis::transfer(BasicBlock* BB) {
  BBProperties& bbProps = this->bb2props.find(BB)->second;

  if (bbProps.frees) {
    // outMustUsed already set to Unfreeable in init
    // outMayUsed still empty
    //llvm::errs() << "no transfer because of free\n";
  }
  else {
    BBPtrState& bbPtrState = this->bb2state.find(BB)->second;

    // outMust
    for (Value* v: bbPtrState.inMustUsed) {
      bbPtrState.outMustUsed.insert(v);
    }
    for (Value* v: bbPtrState.usesOrBasedOn) {
      bbPtrState.outMustUsed.insert(v);
    }
    // outMay
    for (Value* v: bbPtrState.inMayUsed) {
      bbPtrState.outMayUsed.insert(v);
    }
    for (Value* v: bbPtrState.outMustUsed) {
      bbPtrState.outMayUsed.erase(v);
    }
  }
}

void UncheckedUseAnalysis::iterate() {
  while (!this->worklist.empty()) {
    std::unordered_set<BasicBlock*> newWorklist;

    for (auto& BB: this->worklist) {
      newWorklist.erase(BB);
      BBPtrState& bbPtrState = this->bb2state.find(BB)->second;
      size_t nOldOutMustUsed = bbPtrState.outMustUsed.size();
      size_t nOldOutMayUsed  = bbPtrState.outMayUsed.size();

      this->meet(BB);
      this->pointerPropagate(BB);
      this->transfer(BB);

      if (bbPtrState.outMustUsed.size() < bbPtrState.inMustUsed.size()) {
        if (!this->bb2props.find(BB)->second.frees) {
          llvm::errs() << "only freeing blocks should decrease valid ptrs\n";
          __builtin_trap();
        }
      }

      // add successors to worklist if outMust or outMay changed
      if ((bbPtrState.outMustUsed.size() != nOldOutMustUsed) ||
          (bbPtrState.outMayUsed.size()  != nOldOutMayUsed)) {
        for (BasicBlock* Succ: llvm::successors(BB)) {
          newWorklist.insert(Succ);
        }
      }
    }
    this->worklist = std::move(newWorklist);
  }
}


std::vector<std::pair<Value*, BasicBlock*>> UncheckedUseAnalysis::getUnchecked() {
  iterate();

  std::vector<std::pair<Value*, BasicBlock*>> unchecked_uses;
  for (auto& bbstate: this->bb2state) {
    BasicBlock* BB = bbstate.first;
    BBPtrState& bbPtrState = bbstate.second;
    for (Value* v: bbPtrState.uses) {
      if (bbPtrState.inMustUsed.find(v) == bbPtrState.inMustUsed.end()) {
        unchecked_uses.emplace_back(v, BB);
      }
    }
  }

  return unchecked_uses;
}

void UncheckedUseAnalysis::addCheck(Value* pointer, BasicBlock* BB) {
  BBPtrState& bbPtrState = this->bb2state.find(BB)->second;
  auto& pointerGroup = this->basedOnTree.getPointerGroup(pointer);

  for (Value* v: pointerGroup) {
    bbPtrState.inMustUsed.insert(v);
    bbPtrState.inMayUsed.erase(v);
  }

  for (auto it = bbPtrState.ptrProp.begin(); it != bbPtrState.ptrProp.end(); ) {
    Instruction* inst = *it;
    if (pointerGroup.find(inst) != pointerGroup.end()) {
      it = bbPtrState.ptrProp.erase(it);
    }
    else {
      it++;
    }
  }

  this->worklist.insert(BB);
  this->checks.push_back(std::make_pair(pointer, BB));
}

CheckedStatus UncheckedUseAnalysis::getCheckedStatus(Value* pointer, BasicBlock* BB) {
  iterate();

  if (isa<AllocaInst>(pointer) || isa<Constant>(pointer)) {
    return CheckedStatus::IsChecked;
  }

  BBPtrState& bbPtrState = this->bb2state.find(BB)->second;
  if (bbPtrState.inMustUsed.find(pointer) != bbPtrState.inMustUsed.end()) {
    return CheckedStatus::IsChecked;
  }
  else if (bbPtrState.inMayUsed.find(pointer) != bbPtrState.inMayUsed.end()) {
    return CheckedStatus::MaybeChecked;
  }
  else {
    return CheckedStatus::NotChecked;
  }
}

/*
 * move all function calls into a separate BB if the callee might free memory
 */
static void separate_free_calls(Function& F, const ModuleSummaryIndex* summaryIndex) {
  // find all calls that might free
  std::vector<CallBase*> mightFree;

  for (auto &BB : F) {
    for (BasicBlock::iterator i = BB.begin(), ie = BB.end(); i != ie; ++i) {
      if (CallBase* ci = dyn_cast<CallBase>(&*i)) {
        if (call_might_free(ci, summaryIndex)) {
          mightFree.push_back(ci);
        }
      }
    }
  }
  // move them to a separate BasicBlock
  for (auto& ci: mightFree) {
    BasicBlock* newBB = ci->getParent()->splitBasicBlock(ci);
    Instruction* nextInst = ci->getNextNonDebugInstruction();
    if (nextInst && !nextInst->isTerminator()) {
      newBB->splitBasicBlock(nextInst);
    }
  }
}

static void separate_pointer_defs(Function& F) {
  // also handle calls to functions (check whether write to mem only; read only; no access)
  std::vector<BasicBlock*> worklist;
  for (auto &BB : F) {
    worklist.push_back(&BB);
  }

  // if the function contains IntToPtrInst instructions we need to be more
  // conservative as isIntegerTy(64) might be a pointer after all
  bool anyIntToPtr = false;
  for (auto& BB: worklist) {
    for (BasicBlock::iterator i = BB->begin(), ie = BB->end(); i != ie; i++) {
      if (isa<IntToPtrInst>(&*i)) {
        anyIntToPtr = true;
        break;
      }
    }
    if (anyIntToPtr) {
      break;
    }
  }

  for (auto& BB: worklist) {
    Instruction* first_write = nullptr;
    for (BasicBlock::iterator i = BB->begin(), ie = BB->end(); i != ie; ) {
      Instruction* insn = &*i;

      if (isa<StoreInst>(insn)) {
        first_write = first_write ? first_write : insn;
      }
      else if (CallBase* ci = dyn_cast<CallBase>(insn)) {
        Function* callee = ci->getCalledFunction();
        if (!callee || !callee->onlyReadsMemory()) {
          // unknown target or might write to memory
          first_write = first_write ? first_write : insn;
        }
      }

      bool mightDefPtr = insn->getType()->isPointerTy();
      if (!mightDefPtr && anyIntToPtr && insn->getType()->isIntegerTy(64)) {
        for (User* user: insn->users()) {
          if (isa<IntToPtrInst>(user) ||
              isa<SelectInst>(user) ||
              isa<PHINode>(user)) {
            mightDefPtr = true;
            break;
          }
        }
      }

      if (first_write && mightDefPtr) {
        Instruction* pivot;
        if (first_write == insn) {
          if (isa<InvokeInst>(insn)) {
            i++;
            continue;
          }
          pivot = insn->getNextNonDebugInstruction();
        }
        else {
          pivot = insn;
        }

        BB = BB->splitBasicBlock(pivot);
        i = BB->begin(); // i now still points to the current instruction
        ie = BB->end();
        first_write = nullptr;
      }
      else {
        i++;
      }
    }
  }
}

/* - split critical edges
 * - all calls to functions which might free memory are moved to a separate
 *   BasicBlock
 * - after a (potential) memory write (StoreInst, Call*) there is no
 *   further pointer definition within the same BasicBlock
 */
static void normalize_function(Function& F, const ModuleSummaryIndex* summaryIndex) {
  llvm::SplitAllCriticalEdges(F);
  separate_free_calls(F, summaryIndex);
  separate_pointer_defs(F);
}



/*
 * ObjectGroup(P): set of all pointers known to be pointing into the same
 * object/allocation. Pointers generated by BitCast and GEP instructions
 * always point to the same object.
 */

/* for each pointer defined by an instruction and pointers supplied as function
 * arguments we compute the set of BB in which the pointer must be valid.
 * A pointer P is valid in a BasicBlock B if Def(P) dominates B and either:
 * - there is no path from B to a function exit not causing a "Use" of a pointer
 *   within ObjectGroup(P)
 * - all paths to B contain a "Use" of a pointer within ObjectGroup(P)
 *   without calling a function that might free() P.
 *
 * a "Use" of a pointer is defined as being used as address argument to a LoadInst/StoreInst
 * or being passed as an argument to a CallBase.
 *
 * We compute this set using a backwards data flow algorithm for the first
 * condition and extend the generated sets with a forwards data flow algorithm
 * for the second condition.
 */

class PointerValidity {
public:
  PointerValidity(Function& F, DominatorTree& DT, LoopInfo& LI,
                  BasedOnTree& basedOnTree, std::unordered_map<BasicBlock*, BBProperties>& bbPropsLookup);

  bool isPointerValid(Value* pointer, BasicBlock* BB) {
    if (isa<AllocaInst>(pointer) || isa<Constant>(pointer)) {
      return true;
    }
    auto search = validity.find(pointer);
    if (search == validity.end()) {
      return false;
    }
    return search->second.find(BB) != search->second.end();
  }

  void dump();

private:
  std::unordered_map<Value*, std::unordered_set<BasicBlock*>> validity;
};

void PointerValidity::dump() {
  std::unordered_map<BasicBlock*, std::unordered_set<Value*>> bb2vs;

  for (auto& v2bbs: validity) {
    Value* v = v2bbs.first;
    for (BasicBlock* BB: v2bbs.second) {
      bb2vs[BB].insert(v);
    }
  }

  for (auto& ele: bb2vs) {
    BasicBlock* BB = ele.first;
    llvm::errs() << "Validity BB" << *BB << "\n";
    for (Value* v: ele.second) {
      llvm::errs() << "valid: " << *v << "\n";
    }
    llvm::errs() << "=====\n";
  }
}

PointerValidity::PointerValidity(Function& F, DominatorTree& DT, LoopInfo& LI,
                                 BasedOnTree& basedOnTree,
                                 std::unordered_map<BasicBlock*, BBProperties>& bbPropsLookup) {

  std::unordered_set<BasicBlock*> worklist;
  std::unordered_map<BasicBlock*,
                     std::pair<std::unordered_set<Value*>,
                               std::unordered_set<Value*>>> bbToInOut;
  std::unordered_map<BasicBlock*, std::vector<PHINode*>> bb2PHIs;

  // init: OUT = empty; IN = set of pointers that will be "Used" in this BB
  //
  // backwards step (i.e. pointer is valid because it will be "Used" in all successors):
  // meet: OUT = intersection(IN of all successors)
  // transfer: IN += OUT
  //
  // forwards step (i.e. pointer is valid because is was "Used" and cannot be freed):
  // meet: IN += intersection(OUT of all predecessors)
  // transfer: if BB might free memory => nothing
  //           otherwise => OUT += IN
  //
  // note that we also add each pointer within the same BasedOnTree if the
  // pointer is defined within the BB

  // TODO: trace SelectInst?

  // init
  for (auto& BB: F) {
    worklist.insert(&BB);

    bbToInOut[&BB] = std::make_pair(std::unordered_set<Value*>(), std::unordered_set<Value*>());
    auto& in = bbToInOut[&BB].first;
    auto& phis = bb2PHIs[&BB];

    for (BasicBlock::iterator i = BB.begin(), ie = BB.end(); i != ie; ++i) {
      if (CallBase* ci = dyn_cast<CallBase>(&*i)) {
        if (is_skipped_call(ci)) {
          continue;
        }

#if VERIFY_CALL_ARGS
        // all pointer arguments are "Used"
        for (auto& arg: ci->args()) {
          if (arg->getType()->isPointerTy()) {
            in.insert(basedOnTree.getPointerBase(arg));
          }
        }
#endif
      }
      else if (StoreInst* storeInst = dyn_cast<StoreInst>(&*i)) {
        in.insert(basedOnTree.getPointerBase(storeInst->getPointerOperand()));
      }
      else if (LoadInst* loadInst = dyn_cast<LoadInst>(&*i)) {
        in.insert(basedOnTree.getPointerBase(loadInst->getPointerOperand()));
      }
      else if (PHINode* phi = dyn_cast<PHINode>(&*i)) {
        phis.push_back(phi);
      }
    }

    // we remove alloca's and global constants for better performance as
    // as we're not interested in them later
    for (auto it = in.begin(); it != in.end(); ) {
      Value* v = *it;
      if (isa<AllocaInst>(v) || isa<Constant>(v)) {
        it = in.erase(it);
      }
      else {
        it++;
      }
    }

#if VERIFY_CALL_ARGS
    // extend initial BB with argument pointers
    if (&BB == &F.getEntryBlock()) {
      for (auto& arg: F.args()) {
        if (arg.getType()->isPointerTy()) {
          in.insert(&arg);
        }
      }
    }
#endif
  }

  std::unordered_map<BasicBlock*, std::vector<BasicBlock*>> relevantPreds;
  for (BasicBlock* BB: worklist) {
    relevantPreds[BB] = relevantPredecessors(BB, LI, bbPropsLookup);
  }

  while (!worklist.empty()) {
    std::unordered_set<BasicBlock*> newWorklist;
    for (auto& BB: worklist) {
      newWorklist.erase(BB);

      auto& bbProps = bbPropsLookup.find(BB)->second;
      auto& bbIO = bbToInOut.find(BB)->second;
      auto& in = bbIO.first;
      auto& out = bbIO.second;
      size_t nIn = in.size();
      size_t nOut = out.size();

      // backwards meet
      if (BB->getTerminator()->getNumSuccessors() > 0) {
        std::unordered_set<Value*> succIntersect;
        bool first = true;

        for (BasicBlock* Succ: llvm::successors(BB)) {
          auto& succIn = bbToInOut.find(Succ)->second.first;
          if (first) {
            first = false;
            succIntersect = succIn;

            for (PHINode* phinode: bb2PHIs.find(Succ)->second) {
              if (succIn.find(phinode) != succIn.end()) {
                Value* incoming = phinode->getIncomingValueForBlock(BB);
                succIntersect.insert(basedOnTree.getPointerBase(incoming));
              }
            }
            continue;
          }

          for (auto it = succIntersect.begin(); it != succIntersect.end(); ) {
            if (succIn.find(*it) != succIn.end()) {
              it++;
              continue;
            }

            bool foundInPhi = false;
            for (PHINode* phinode: bb2PHIs.find(Succ)->second) {
              if (succIn.find(phinode) != succIn.end()) {
                Value* incoming = phinode->getIncomingValueForBlock(BB);
                Value* incomingBase = basedOnTree.getPointerBase(incoming);
                if (incomingBase == *it) {
                  foundInPhi = true;
                  break;
                }
              }
            }
            if (foundInPhi) {
              it++;
            }
            else {
              it = succIntersect.erase(it);
            }
          }

          if (succIntersect.empty()) {
            break;
          }
        }

        for (Value* v: succIntersect) {
          Instruction* insn = dyn_cast<Instruction>(v);
          if (insn && !DT.dominates(insn->getParent(), BB)) {
            continue;
          }
          out.insert(v);
        }
      }

      // backwards transfer
      for (Value* v: out) {
        if (bbProps.firstStore &&
            (bbProps.firstStore == dyn_cast<Instruction>(v))) {
          // true if the Value is the result of a CallBase at the end
          // of the BasicBlock.
          // in this case the Value must not be propagated as it is not
          // valid at the beginning of the BasicBlock (because it is the
          // result of an Instruction computed in this block).
          continue;
        }
        else {
          in.insert(v);
        }
      }

      // forwards meet
      std::unordered_set<Value*> predIntersect;
      if (BB->hasNPredecessorsOrMore(1)) {
        bool first = true;

        for (BasicBlock* Pred: relevantPreds.find(BB)->second) {
          auto& predOut = bbToInOut.find(Pred)->second.second;
          if (first) {
            first = false;
            predIntersect = predOut;
            continue;
          }

          for(auto it = predIntersect.begin(); it != predIntersect.end(); ) {
            if (predOut.find(*it) != predOut.end()) {
              it++;
            }
            else {
              it = predIntersect.erase(it);
            }
          }
        }
        for (Value* v: predIntersect) {
          in.insert(v);
        }
      }

      // forwards transfer
      if (!bbProps.frees) {
        for (Value* v: in) {
          out.insert(v);
        }
      }

      if ((nIn > in.size()) || (nOut > out.size())) {
        __builtin_trap();
      }

      // update worklist as necessary
      if (nIn != in.size()) {
        for (BasicBlock* Pred: llvm::predecessors(BB)) {
          newWorklist.insert(Pred);
        }
      }
      if (nOut != out.size()) {
        for (BasicBlock* Succ: llvm::successors(BB)) {
          newWorklist.insert(Succ);
        }
      }
    }

    worklist = std::move(newWorklist);
  }

  for (auto& bbIO: bbToInOut) {
    BasicBlock* BB = bbIO.first;
    auto& in = bbIO.second.first;

    for (Value* v: in) {
      for (Value* equivPointer: basedOnTree.getPointerGroup(v)) {
        Instruction* insn = dyn_cast<Instruction>(equivPointer);
        if (insn && !DT.dominates(insn->getParent(), BB)) {
          continue;
        }
        validity[equivPointer].insert(BB);
      }
    }
  }
}


bool try_move_check(Function& F, LoopInfo& LI,
                    BasedOnTree& basedOnTree,
                    PointerValidity& pointerValidity,
                    std::unordered_map<BasicBlock*, BBProperties>& bb2Props,
                    Value* pointer, BasicBlock* BB,
                    std::vector<std::pair<Value*, BasicBlock*>>& movedChecks,
                    bool up, bool allowIntoLoop,
                    bool allowBaseFallback) {

  bool down = !up;
  std::vector<BasicBlock*> candidates;
  unsigned startLoopDepth = LI.getLoopDepth(BB);
  BBProperties& BBProps = bb2Props.find(BB)->second;
  if (down && (BBProps.frees || BBProps.stores)) {
    // if the current block frees we cannot move down as the pointer
    // might no longer be valid
    // if the current block stores we cannot move down as we might
    // write corrupted data to memory
    return false;
  }

  if (up) {
    for (BasicBlock *Pred : llvm::predecessors(BB)) {
      candidates.push_back(Pred);
    }
  }
  else {
    for (BasicBlock* Succ: llvm::successors(BB)) {
      candidates.push_back(Succ);
    }
  }

  if (candidates.size() == 0) {
    // cannot move up from entry nor down from exit
    return false;
  }

  for (BasicBlock* cBB: candidates) {
    BBProperties& cBBProps = bb2Props.find(cBB)->second;
    if (up && cBBProps.frees) {
      return false;
    }
    if (!allowIntoLoop && (LI.getLoopDepth(cBB) > startLoopDepth)) {
      return false;
    }
  }

  std::vector<std::pair<Value*, BasicBlock*>> _movedChecks;
  PHINode* phinode = dyn_cast<PHINode>(pointer);
  if (up && phinode && (phinode->getParent() == BB)) {
    for (BasicBlock* cBB: candidates) {
      Value* incoming = phinode->getIncomingValueForBlock(cBB);
      Value* incomingBase = basedOnTree.getPointerBase(incoming);
      if (isa<AllocaInst>(incomingBase) || isa<Constant>(incomingBase)) {
        continue;
      }
      else if (!pointerValidity.isPointerValid(incoming, cBB)) {
        // TODO this indicates a lack of data flow analysis
        llvm::errs() << "phifail " << *incoming << "\n";
        llvm::errs() << F << "\n";
        // __builtin_trap();
        return false;
      }
      else {
        _movedChecks.push_back(std::make_pair(incoming, cBB));
      }
    }
  }
  else {
    for (BasicBlock* cBB: candidates) {
      if (!pointerValidity.isPointerValid(pointer, cBB)) {
        if (allowBaseFallback) {
          Value* basedOn = basedOnTree.getPointerBase(pointer);
          if (!pointerValidity.isPointerValid(basedOn, cBB)) {
            return false;
          }
          else {
            pointer = basedOn;
          }
        }
        else {
          return false;
        }
      }
      _movedChecks.push_back(std::make_pair(pointer, cBB));
    }
  }

  movedChecks = std::move(_movedChecks);
  return true;
}


bool loop_hoist_check(Function& F, LoopInfo& LI,
                      PointerValidity& pointerValidity,
                      std::unordered_map<BasicBlock*, BBProperties>& bb2Props,
                      Value* pointer, BasicBlock* BB,
                      std::vector<BasicBlock*>& hoisted_checks) {

  Instruction* inst = dyn_cast<Instruction>(pointer);

  // check if there could be a free between preHeader and BB
  //   if true: abort
  // check if pointer must be valid in preHeader:
  //   if yes => candidate
  //   if no  => not a candidate
  //   both cases => attempt to move check in parent and find better candidate

  std::unordered_set<BasicBlock*> processed;
  std::unordered_set<BasicBlock*> worklist;
  std::unordered_set<BasicBlock*> hoisted;

  BasicBlock* bbFrees = nullptr;
  BasicBlock* bbPredFrees = nullptr;
  BasicBlock* bbPointerInv = nullptr;
  int reachedFree = 0;

  worklist.insert(BB);
  while (!worklist.empty()) {
    std::unordered_set<BasicBlock*> newWorklist;

    for (BasicBlock* cBB: worklist) {
      newWorklist.erase(cBB);
      if (processed.find(cBB) != processed.end()) {
        continue;
      }
      processed.insert(cBB);

      Loop* loop = LI.getLoopFor(cBB);
      if (!loop) {
        if (LI.getLoopDepth(cBB) != 0) {
          llvm::errs() << "should be out of loop";
          __builtin_trap();
        }
        hoisted.insert(cBB);
        continue;
      }

      if (LI.isLoopHeader(cBB)) {
        while (true) {
          Loop* parentLoop = loop->getParentLoop();
          if (parentLoop && (parentLoop->getHeader() == cBB)) {
            loop = parentLoop;
          }
          else {
            break;
          }
        }
      }

      bool loop_frees = false;
      for (BasicBlock* lBB: loop->blocks()) {
        BBProperties& bbdata = bb2Props.find(lBB)->second;
        if (bbdata.frees) {
          bbFrees = lBB;
          loop_frees = true;
          reachedFree = 1;
          break;
        }
      }
      if (loop_frees) {
        hoisted.insert(cBB);
        continue;
      }

      BasicBlock* header = loop->getHeader();
      bool suc = true;
      std::vector<BasicBlock*> relevantPredecessors;
      for (BasicBlock *Pred : llvm::predecessors(header)) {
        if (!loop->contains(Pred)) {
          relevantPredecessors.push_back(Pred);
        }
      }

      for (BasicBlock* Pred: relevantPredecessors) {
        BBProperties& bbdata = bb2Props.find(Pred)->second;
        if (bbdata.frees) {
          bbPredFrees = Pred;
          suc = false;
          break;
        }
        if (!pointerValidity.isPointerValid(pointer, Pred)) {
          bbPointerInv = Pred;
          suc = false;
          break;
        }
      }
      if (suc) {
        for (BasicBlock *Pred : relevantPredecessors) {
          if (LI.getLoopDepth(cBB) <= LI.getLoopDepth(Pred)) {
            llvm::errs() << "failed to hoist\n";
            __builtin_trap();
          }
          newWorklist.insert(Pred);
        }
      }
      else {
        hoisted.insert(cBB);
      }
    }

    worklist = std::move(newWorklist);
  }

  unsigned mx = 0;
  for (BasicBlock* hBB: hoisted) {
    hoisted_checks.push_back(hBB);
    unsigned cur = LI.getLoopDepth(hBB);
    mx = cur > mx ? cur : mx;
  }

  return true;
}


bool reduceMaybe(Function& F, LoopInfo& LI,
                 BasedOnTree& basedOnTree,
                 PointerValidity& pointerValidity,
                 UncheckedUseAnalysis& uua,
                 std::unordered_map<BasicBlock*, BBProperties>& bb2Props,
                 Value* pointer, BasicBlock* BB,
                 std::vector<std::pair<Value*, BasicBlock*>>& reducedBlocks) {

  if (uua.getCheckedStatus(pointer, BB) == NotChecked) {
    reducedBlocks.push_back(std::make_pair(pointer, BB));
    return false;
  }

  std::unordered_set<BasicBlock*> worklist, processed, reduced;
  std::unordered_map<BasicBlock*, Value*> bb2val;
  worklist.insert(BB);
  bb2val[BB] = pointer;
  bool reducedAny = false;

  while (!worklist.empty()) {
    std::unordered_set<BasicBlock*> newWorklist;

    for (BasicBlock* cBB: worklist) {
      if (processed.find(cBB) != processed.end()) {
        continue;
      }
      processed.insert(cBB);
      newWorklist.erase(cBB);

      Value* cVal = bb2val.find(cBB)->second;
      auto status = uua.getCheckedStatus(cVal, cBB);
      if (status == NotChecked) {
        reduced.insert(cBB);
      }
      else if (status == IsChecked) {
        reducedAny = true;
        continue;
      }
      else if (status == MaybeChecked) {
        std::vector<std::pair<Value*, BasicBlock*>> movedChecks;
        bool suc = try_move_check(F, LI, basedOnTree, pointerValidity,
                                  bb2Props, cVal, cBB, movedChecks, true, false, LOOSE_POINTER_ARGS);
        if (!suc) {
          reduced.insert(cBB);
        }
        else {
          bool allSingleSucc = true;
          for (auto& movedCheck: movedChecks) {
            BasicBlock* nBB = movedCheck.second;
            if (llvm::succ_size(nBB) != 1) {
              allSingleSucc = false;
              break;
            }
          }

          if (allSingleSucc) {
            for (auto& movedCheck: movedChecks) {
              Value* val = movedCheck.first;
              BasicBlock* nBB = movedCheck.second;
              newWorklist.insert(nBB);
              bb2val[nBB] = val;
            }
          }
          else {
            reduced.insert(cBB);
          }
        }
      }
    }

    worklist = std::move(newWorklist);
  }

  if (reducedAny) {
    for (BasicBlock* rBB: reduced) {
      Value* rVal = bb2val.find(rBB)->second;
      reducedBlocks.push_back(std::make_pair(rVal, rBB));
    }
  }
  else {
    reducedBlocks.push_back(std::make_pair(pointer, BB));
  }

  return reducedAny;
}


struct byLevelComp {
  byLevelComp(std::unordered_map<BasicBlock*, BBProperties>& bb2Props) {
    _bb2Props = &bb2Props;
  }

  bool operator() (std::pair<Value*, BasicBlock*>& o1,
                   std::pair<Value*, BasicBlock*>& o2) {
      int level1 = _bb2Props->find(o1.second)->second.level;
      int level2 = _bb2Props->find(o2.second)->second.level;
      // higher level => closer to the entry node
      return level1 > level2;
  }
  std::unordered_map<BasicBlock*, BBProperties>* _bb2Props;
};

void choose_checks(Function& F, UncheckedUseAnalysis& uua,
                   BasedOnTree& basedOnTree,
                   PointerValidity& pointerValidity,
                   std::unordered_map<BasicBlock*, BBProperties>& bb2Props,
                   LoopInfo& LI) {
  std::vector<std::pair<Value*, BasicBlock*>> unchecked = uua.getUnchecked();
  std::vector<std::pair<Value*, BasicBlock*>> allHoisted;

  // loop hoist check
  for (auto& uc: unchecked) {
    Value* pointer = uc.first;
    Value* basedOn = basedOnTree.getPointerBase(pointer);
    BasicBlock* BB = uc.second;

    std::vector<BasicBlock*> hoisted_checks;
    bool suc = loop_hoist_check(F, LI, pointerValidity, bb2Props, basedOn, BB, hoisted_checks);
    if (suc) {
      for (BasicBlock* hBB: hoisted_checks) {
        allHoisted.push_back(std::make_pair(basedOn, hBB));
      }
    }
    else {
      allHoisted.push_back(std::make_pair(pointer, BB));
    }
  }

  // sort the checks such as the ones more closer to the entry come first
  std::sort(allHoisted.begin(), allHoisted.end(), byLevelComp(bb2Props));

  int state[3] = {0};
  std::unordered_map<BasicBlock*, int> bb2count;

  // get from Maybe to Must + Not if possible
  unsigned reduced = 0;
  std::vector<std::pair<Value*, BasicBlock*>> reducedMaybes;
  std::vector<std::pair<Value*, BasicBlock*>> skippedReadOnlys;

  for (auto& uc: allHoisted) {
    Value* pointer = uc.first;
    BasicBlock* BB = uc.second;
    if (uua.getCheckedStatus(pointer, BB) == IsChecked) {
      continue;
    }

    std::vector<std::pair<Value*, BasicBlock*>> reducedChecks;

    reduceMaybe(F, LI, basedOnTree, pointerValidity,
                uua, bb2Props, pointer, BB, reducedChecks);

    for (auto& reducedCheck: reducedChecks) {
      Value* rVal = reducedCheck.first;
      BasicBlock* rBB = reducedCheck.second;

      if (uua.getCheckedStatus(rVal, rBB) == IsChecked) {
        continue;
      }
      state[uua.getCheckedStatus(rVal, rBB)]++;
      uua.addCheck(rVal, rBB);
      bb2count[rBB]++;
    }
  }
}

Instruction* load_heap_prefix(Function& F) {
  Module& M = *F.getParent();
  LLVMContext &C = M.getContext();
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  PointerType *PInt8Ty = PointerType::get(Int8Ty, 0);

  // check whether we have a weird function we cannot modify
  BasicBlock& entryBlock = F.getEntryBlock();
  if (entryBlock.getFirstInsertionPt() == entryBlock.end()) {
    __builtin_trap();
  }

  GlobalVariable *GVHeap = getOrInsertGlobal(M, "df_heap_start", PInt8Ty);
  GVHeap->setExternallyInitialized(true);
  IRBuilder<> IRBIntr(&*entryBlock.getFirstInsertionPt());
  std::vector<Value*> index;
  index.push_back(ConstantInt::get(Int64Ty, 0));
  Value* ptr = IRBIntr.CreateLoad(IRBIntr.CreateGEP(GVHeap, index));
  return dyn_cast<Instruction>(IRBIntr.CreatePtrToInt(ptr, Int64Ty));
}


std::vector<std::tuple<Value*, Value*, Value*>>
compute_address_and_tag(std::vector<Value*>& ptrs, Value* heapPrefix, Value* shadowArea,
                        Instruction* insertionPoint, LLVMContext &C) {
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);
  IRBuilder<> IRBIntr(insertionPoint);

  std::vector<Type*> rorxArgTys;
  rorxArgTys.push_back(Int64Ty);
  rorxArgTys.push_back(Int64Ty);
  InlineAsm* RorxAsm = InlineAsm::get(FunctionType::get(Int64Ty, rorxArgTys, false),
                                      StringRef("rorxq $2, $1, $0"),
                                      StringRef("=r,r,J"),
                                      /*hasSideEffects=*/false);

  std::vector<Type*> shrxArgTys;
  shrxArgTys.push_back(Int64Ty);
  shrxArgTys.push_back(Int64Ty);
  InlineAsm* ShrxAsm = InlineAsm::get(FunctionType::get(Int64Ty, shrxArgTys, false),
                                      StringRef("shrxq $2, $1, $0"),
                                      StringRef("=r,r,r,~{cc},~{flags}"),
                                      /*hasSideEffects=*/false);

  std::vector<Value*> ptrAsInteg;
  for (Value* v: ptrs) {
    if (v->getType()->isPointerTy()) {
      ptrAsInteg.push_back(IRBIntr.CreatePtrToInt(v, Int64Ty));
    }
    else if (v->getType()->isIntegerTy(64)) {
      ptrAsInteg.push_back(v);
    }
    else {
      __builtin_trap();
    }
  }

  std::vector<Value*> ptrXored;
  for (Value* v: ptrAsInteg) {
    Value* _prefixXored  = IRBIntr.CreateXor(v, heapPrefix);
    ptrXored.push_back(_prefixXored);
  }

  std::vector<Value*> ptrPrefixShifted;
  for (Value* v: ptrXored) {
    Value* _ptrPrefixShifted = IRBIntr.CreateLShr(v, ConstantInt::get(Int64Ty, DF_PTR_BITS));
    ptrPrefixShifted.push_back(_ptrPrefixShifted);
  }

  std::vector<std::tuple<Value*, Value*, Value*>> shadowAndTag;
  Value* allZero = ConstantInt::get(Int64Ty, 0);

  for (unsigned idx = 0; idx < ptrPrefixShifted.size(); idx++) {
    Value* _ptrPrefixShifted = IRBIntr.CreateTrunc(ptrPrefixShifted[idx], Int32Ty);
    Value* prefixAnded = IRBIntr.CreateAnd(_ptrPrefixShifted, ConstantInt::get(Int32Ty, 0x80000000 - (1 << DF_MTAG_BITS)));
    Value* isNonHeap   = IRBIntr.CreateICmpNE(prefixAnded, ConstantInt::get(Int32Ty, 0));

    std::vector<Value*> rorxArgs;
    rorxArgs.push_back(ptrAsInteg[idx]);
    rorxArgs.push_back(ConstantInt::get(Int64Ty, DF_PTR_BITS));
    Value* ptrTag64 = IRBIntr.CreateCall(RorxAsm, rorxArgs);
    Value* ptrTag8  = IRBIntr.CreateTrunc(ptrTag64, Int8Ty);
    Value* tag = IRBIntr.CreateSelect(isNonHeap, ConstantInt::get(Int8Ty, 0), ptrTag8);

    std::vector<Value*> shrxArgs;
    shrxArgs.push_back(ptrTag64);
    shrxArgs.push_back(IRBIntr.CreatePtrToInt(shadowArea, Int64Ty));
    Value* shadOffsetDirty = IRBIntr.CreateCall(ShrxAsm, shrxArgs);
    Value* shadOffset = IRBIntr.CreateSelect(isNonHeap, allZero, shadOffsetDirty);

    std::vector<Value*> indexes;
    indexes.push_back(shadOffset);
    Value* shadPtr = IRBIntr.CreateInBoundsGEP(shadowArea, indexes); // = GVShad[]

    shadowAndTag.push_back(std::make_tuple(ptrs[idx], shadPtr, tag));
  }

  return shadowAndTag;
}


bool get_metadata_hint(Value* p, int& hintIsHeap) {
  if (Instruction* baseinst = dyn_cast<Instruction>(p)) {
    MDNode* ptrAssume = baseinst->getMetadata("UAFCheckerFrequency");
    if (ptrAssume) {
      StringRef sr = cast<MDString>(ptrAssume->getOperand(0))->getString();
      if (sr.equals("assumeTrue")) {
        hintIsHeap = 1;
        return true;
      }
      else if (sr.equals("assumeFalse")) {
        hintIsHeap = -1;
        return true;
      }
      else if (sr.equals("assumeMixed")) {
        hintIsHeap = 0;
        return true;
      }
      else {
        llvm::errs() << "unknown assumption\n";
        __builtin_trap();
      }
    }
  }
  else if (Argument* arg = dyn_cast<Argument>(p)) {
    if (arg->hasAttribute(Attribute::AssumeHeapPointer)) {
      hintIsHeap = 1;
      return true;
    }
    else if (arg->hasAttribute(Attribute::AssumeNonHeapPointer)) {
      hintIsHeap = -1;
      return true;
    }
    else if (arg->hasAttribute(Attribute::AssumeMixedPointer)) {
      hintIsHeap = 0;
      return true;
    }
  }
  else {
    llvm::errs() << "unknown pointer type " << *p << "\n";
    __builtin_trap();
  }

  return false;
}


bool derive_heap_hint(BasedOnTree& basedOnTree, Value* pointer, int& hintIsHeap) {
  if (get_metadata_hint(pointer, hintIsHeap)) {
    return true;
  }

  Value* basedOn = basedOnTree.getPointerBase(pointer);
  if (get_metadata_hint(basedOn, hintIsHeap)) {
    return true;
  }
  if (PHINode* phiNode = dyn_cast<PHINode>(basedOn)) {
    int isHeap = 0;
    int isNonHeap = 0;
    int isMixed = 0;
    for (unsigned i = 0; i < phiNode->getNumIncomingValues(); i++) {
      Value* ivalue = basedOnTree.getPointerBase(phiNode->getIncomingValue(i));
      Constant* cvalue = dyn_cast<Constant>(ivalue);
      int phiHintIsHeap;

      if (cvalue) {
        if (!cvalue->isNullValue()) {
          isNonHeap++;
        }
        // null pointers are just ignored
      }
      else if (!get_metadata_hint(ivalue, phiHintIsHeap)) {
        return false;
      }
      else if (phiHintIsHeap == 1) {
        isHeap++;
      }
      else if (phiHintIsHeap == 0) {
        isMixed++;
      }
      else if (phiHintIsHeap == -1) {
        isNonHeap++;
      }
      else {
        llvm::errs() << "value error\n";
        __builtin_trap();
      }
    }

    int results = 0;
    if (isHeap) {
      results++;
      hintIsHeap = 1;
    }
    if (isNonHeap) {
      results++;
      hintIsHeap = -1;
    }
    if (isMixed) {
      results++;
      hintIsHeap = 0;
    }
    if (results > 1) {
      hintIsHeap = 0;
    }
    return true;
  }
  else {
    // any other way to derive the hint for data we have?
    return false;
  }
  return false;
}



void insert_checks_scalar(Function& F, DominatorTree& DT,
                          LoopInfo& LI,
                          UncheckedUseAnalysis& uua, BasedOnTree& basedOnTree,
                          std::unordered_map<BasicBlock*, BBProperties>& bb2Props) {

  Module& M = *F.getParent();
  LLVMContext &C = M.getContext();
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);
  PointerType *PInt8Ty = PointerType::get(Int8Ty, 0);

  Function *abortIntr    = Intrinsic::getDeclaration(&M, Intrinsic::trap);

  std::vector<Type*> rorxArgTys;
  rorxArgTys.push_back(Int64Ty);
  rorxArgTys.push_back(Int64Ty);
  InlineAsm* RorxAsm = InlineAsm::get(FunctionType::get(Int64Ty, rorxArgTys, false),
                                      StringRef("rorxq $2, $1, $0"),
                                      StringRef("=r,r,J"),
                                      /*hasSideEffects=*/false);

  std::vector<Type*> shrxArgTys;
  shrxArgTys.push_back(Int64Ty);
  shrxArgTys.push_back(Int64Ty);
  InlineAsm* ShrxAsm = InlineAsm::get(FunctionType::get(Int64Ty, shrxArgTys, false),
                                      StringRef("shrxq $2, $1, $0"),
                                      StringRef("=r,r,r,~{cc},~{flags}"),
                                      /*hasSideEffects=*/false);

  Value* heapPrefix = load_heap_prefix(F);
  GlobalVariable *GVShad = getOrInsertGlobal(M, "df_shadow_start", PInt8Ty);
  GVShad->setExternallyInitialized(true);

  IRBuilder<> IRBIntrEntry(&*F.getEntryBlock().getFirstInsertionPt());

  std::vector<Value*> index;
  index.push_back(ConstantInt::get(Int64Ty, 0));
  Value* shadowArea = IRBIntrEntry.CreateLoad(IRBIntrEntry.CreateGEP(GVShad, index));

  std::unordered_map<BasicBlock*, BasicBlock*> bb2ImmDom;
  for (BasicBlock& BB: F) {
    for (auto& cNode: DT.getNode(&BB)->getChildren()) {
      BasicBlock* cBB = cNode->getBlock();
      bb2ImmDom[cBB] = &BB;
    }
  }

  std::unordered_map<BasicBlock*, Instruction*> bb2InsertPoint;
  for (BasicBlock& BB: F) {
    BBProperties& bbProps = bb2Props.find(&BB)->second;
    Instruction* insertionPoint;
    if (!bbProps.firstStore) {
      insertionPoint = BB.getTerminator();
    }
    else {
      insertionPoint = bbProps.firstStore;
    }
    bb2InsertPoint[&BB] = insertionPoint;
  }

  std::unordered_map<BasicBlock*, std::unordered_set<Value*>> BB2Precomp;

  std::unordered_map<BasicBlock*, std::unordered_set<Value*>> BB2AssumeHeapChecks;
  std::unordered_map<BasicBlock*, std::unordered_set<Value*>> BB2AssumeNonHeapChecks;
  std::unordered_map<BasicBlock*, std::unordered_set<Value*>> BB2RegularChecks;
  std::unordered_map<BasicBlock*, std::unordered_set<Value*>> BB2PrecompChecks;

  int Nprecom = 0;
  int NassumeF = 0;
  int NassumeT = 0;
  int Nregular = 0;
  int Nnohint = 0;

  for (auto& check: uua.getChecks()) {
    Value* pointer = check.first;
    BasicBlock* BB = check.second;
    Value* base = basedOnTree.getPointerBase(pointer);

    int hintIsHeap = 0;
    bool hasHint = derive_heap_hint(basedOnTree, pointer, hintIsHeap);

    if (hasHint && hintIsHeap == -1) {
      NassumeF++;
      BB2AssumeNonHeapChecks[BB].insert(pointer);
      continue;
    }

    BasicBlock* definingBB;
    if (isa<Argument>(base)) {
      definingBB = &F.getEntryBlock();
    }
    else if (Instruction* defInst = dyn_cast<Instruction>(base)) {
      definingBB = defInst->getParent();
    }
    else {
      llvm::errs() << "assumption1 violated for " << *base << " " << *BB << "\n";
      llvm::errs() << F << "\n";
      __builtin_trap();
    }

    unsigned bestBBDepth = LI.getLoopDepth(BB);
    BasicBlock* bestBB = BB;
    BasicBlock* curBB  = BB;
    while (bestBBDepth > 0) {
      auto search = bb2ImmDom.find(curBB);
      if (search == bb2ImmDom.end()) {
        break;
      }
      curBB = search->second;

      if (DT.dominates(definingBB, curBB)) {
        unsigned curDepth = LI.getLoopDepth(curBB);
        if (curDepth < bestBBDepth) {
          bestBBDepth = curDepth;
          bestBB = curBB;
        }
      }
      else {
        break;
      }
    }

    if (BB != bestBB) {
      BB2Precomp[bestBB].insert(base);
      BB2PrecompChecks[BB].insert(base);

      // there is a BasicBlock with fulfills:
      // - the allocation is known already (base)
      // - the loop depth is lower than the BasicBlock needing the check
      //
      // => we can precompute a couple of values to speed up the check within
      //    the loop
      Nprecom++;
      continue;
    }

    if (LI.getLoopDepth(definingBB) < LI.getLoopDepth(BB)) {

      curBB = BB;
      while (true) {
        auto search = bb2ImmDom.find(curBB);
        if (search == bb2ImmDom.end()) {
          break;
        }
        curBB = search->second;
        llvm::errs() << "dominated by " << *curBB << "\n";

        if (!DT.dominates(definingBB, curBB)) {
          llvm::errs() << "breaking traversal\n";
        }
      }
      __builtin_trap();
    }

    if (!hasHint) {
      // TODO perf debugging
#if LOOSE_POINTER_ARGS
      BB2AssumeHeapChecks[BB].insert(base);
#else
      BB2AssumeHeapChecks[BB].insert(pointer);
#endif

      Nnohint++;
    }
    else if (hintIsHeap == 1) {
      NassumeT++;
#if LOOSE_POINTER_ARGS
      BB2AssumeHeapChecks[BB].insert(base);
#else
      BB2AssumeHeapChecks[BB].insert(pointer);
#endif
    }
    else if (hintIsHeap == 0) {
      Nregular++;
#if LOOSE_POINTER_ARGS
      BB2RegularChecks[BB].insert(base);
#else
      BB2RegularChecks[BB].insert(pointer);
#endif
    }
    else {
      llvm::errs() << "unknown hint\n";
      __builtin_trap();
    }
  }

  std::unordered_map<BasicBlock*, std::vector<std::tuple<Value*, Value*, Value*>>> BB2AddrAndTag;
  for (auto& ele: BB2Precomp) {
    // precompute shadow address + expected tag
    BasicBlock* BB = ele.first;
    std::vector<Value*> ptrs;
    for (Value* ptr: ele.second) {
      ptrs.push_back(ptr);
    }

    auto addrAndTag = compute_address_and_tag(ptrs, heapPrefix, shadowArea, bb2InsertPoint[BB], C);
    BB2AddrAndTag[BB] = addrAndTag;
  }

  std::vector<BasicBlock*> tBBs;
  for (BasicBlock& BB: F) {
    tBBs.push_back(&BB);
  }

  for (BasicBlock* BB: tBBs) {
    Instruction* insertionPoint = bb2InsertPoint.find(BB)->second;

    auto nsearch = BB2AssumeNonHeapChecks.find(BB);
    if (nsearch != BB2AssumeNonHeapChecks.end()) {
      auto& checks = nsearch->second;
      for (Value* v: checks) {
        IRBuilder<> IRBIntr(insertionPoint);

        Value* ptrAsInteg = nullptr;
        if (v->getType()->isPointerTy()) {
          ptrAsInteg = IRBIntr.CreatePtrToInt(v, Int64Ty);
        }
        else if (v->getType()->isIntegerTy(64)) {
          ptrAsInteg = v;
        }
        else {
          __builtin_trap();
        }

        Value* ptrXored   = IRBIntr.CreateXor(ptrAsInteg, heapPrefix);
        Value* ptrShifted = IRBIntr.CreateLShr(ptrXored, ConstantInt::get(Int64Ty, DF_PTR_BITS + DF_MTAG_BITS));
        Value* hopeFalse  = IRBIntr.CreateICmpEQ(ptrShifted, ConstantInt::get(Int64Ty, 0));

        MDNode *weight = MDBuilder(C).createBranchWeights(1, 100000);
        Instruction* fallbackBBStart = llvm::SplitBlockAndInsertIfThen(hopeFalse, insertionPoint, false, weight);

        // contrary to our assumptions, we got a heap pointer. we need to verify the tag matches
        // or kill the execution
        IRBIntr.SetInsertPoint(fallbackBBStart);
        Instruction* term = fallbackBBStart->getParent()->getTerminator();

        std::vector<Value*> rorxArgs;
        rorxArgs.push_back(ptrAsInteg);
        rorxArgs.push_back(ConstantInt::get(Int64Ty, DF_PTR_BITS));
        Value* ptrTag64 = IRBIntr.CreateCall(RorxAsm, rorxArgs);
        Value* ptrTag8  = IRBIntr.CreateTrunc(ptrTag64, Int8Ty);

	std::vector<Value*> shrxArgs;
        shrxArgs.push_back(ptrTag64);
        shrxArgs.push_back(IRBIntr.CreatePtrToInt(shadowArea, Int64Ty));
        Value* shadOffset = IRBIntr.CreateCall(ShrxAsm, shrxArgs);

        std::vector<Value*> indexes;
        indexes.push_back(shadOffset);
        Value* shadPtr   = IRBIntr.CreateInBoundsGEP(shadowArea, indexes); // = GVShad[]
        Value* shadTag8  = IRBIntr.CreateLoad(shadPtr);
        hopeFalse        = IRBIntr.CreateICmpNE(ptrTag8, shadTag8);

        BranchInst* br    = IRBIntr.CreateBr(insertionPoint->getParent());
        term->eraseFromParent();

        Instruction* killBBStart = llvm::SplitBlockAndInsertIfThen(hopeFalse, br, true, weight);

        IRBIntr.SetInsertPoint(killBBStart);

        InlineAsm* EmptyAsm = InlineAsm::get(FunctionType::get(IRBIntr.getVoidTy(), false),
					     StringRef(""), StringRef(""), /*hasSideEffects=*/true);
        IRBIntr.CreateCall(EmptyAsm, {});

        std::vector<Value*> noArgs;
        IRBIntr.CreateCall(abortIntr, noArgs);
      }
    }

    auto asearch = BB2AssumeHeapChecks.find(BB);
    if (asearch != BB2AssumeHeapChecks.end()) {
      auto& checks = asearch->second;
      for (Value* v: checks) {
        IRBuilder<> IRBIntr(insertionPoint);

        Value* ptrAsInteg = nullptr;
        if (v->getType()->isPointerTy()) {
          ptrAsInteg = IRBIntr.CreatePtrToInt(v, Int64Ty);
        }
        else if (v->getType()->isIntegerTy(64)) {
          ptrAsInteg = v;
        }
        else {
          __builtin_trap();
        }

        std::vector<Value*> rorxArgs;
        rorxArgs.push_back(ptrAsInteg);
        rorxArgs.push_back(ConstantInt::get(Int64Ty, DF_PTR_BITS));
        Value* ptrTag64 = IRBIntr.CreateCall(RorxAsm, rorxArgs);
        Value* ptrTag8  = IRBIntr.CreateTrunc(ptrTag64, Int8Ty);

	std::vector<Value*> shrxArgs;
        shrxArgs.push_back(ptrTag64);
        shrxArgs.push_back(IRBIntr.CreatePtrToInt(shadowArea, Int64Ty));
        Value* shadOffset = IRBIntr.CreateCall(ShrxAsm, shrxArgs);

        std::vector<Value*> indexes;
        indexes.push_back(shadOffset);
        Value* shadPtr   = IRBIntr.CreateInBoundsGEP(shadowArea, indexes); // = GVShad[]
        Value* shadTag8  = IRBIntr.CreateLoad(shadPtr);
        Value* hopeFalse = IRBIntr.CreateICmpNE(ptrTag8, shadTag8);

        MDNode *weight = MDBuilder(C).createBranchWeights(1, 100000);
        Instruction* fallbackBBStart = llvm::SplitBlockAndInsertIfThen(hopeFalse, insertionPoint, false, weight);

        // there is a tag mismatch but our pointer might be to stack/global, i.e.
        // our profiling data lead us to a false assumption => verify that we're out of heap
        // and recover.
        IRBIntr.SetInsertPoint(fallbackBBStart);
        Instruction* term = fallbackBBStart->getParent()->getTerminator();
        Value* ptrXored   = IRBIntr.CreateXor(ptrAsInteg, heapPrefix);
        Value* ptrShifted = IRBIntr.CreateLShr(ptrXored, ConstantInt::get(Int64Ty, DF_PTR_BITS + DF_MTAG_BITS));
        hopeFalse         = IRBIntr.CreateICmpEQ(ptrShifted, ConstantInt::get(Int64Ty, 0));
        BranchInst* br    = IRBIntr.CreateBr(insertionPoint->getParent());
        term->eraseFromParent();

        Instruction* killBBStart = llvm::SplitBlockAndInsertIfThen(hopeFalse, br, true, weight);

        IRBIntr.SetInsertPoint(killBBStart);
        InlineAsm* EmptyAsm = InlineAsm::get(FunctionType::get(IRBIntr.getVoidTy(), false),
					     StringRef(""), StringRef(""), /*hasSideEffects=*/true);
        IRBIntr.CreateCall(EmptyAsm, {});

        std::vector<Value*> noArgs;
        IRBIntr.CreateCall(abortIntr, noArgs);
      }
    }

    auto psearch = BB2PrecompChecks.find(BB);
    if (psearch != BB2PrecompChecks.end()) {
      auto& checks = psearch->second;

      for (Value* v: checks) {
        IRBuilder<> IRBIntr(insertionPoint);

        // search for the block computing base/tag
        BasicBlock* domTrav = BB;
        Value* shadowAddr = nullptr;
        Value* tag = nullptr;
        while (!shadowAddr) {
          auto search = BB2AddrAndTag.find(domTrav);
          if (search != BB2AddrAndTag.end()) {
            for (auto& AddrAndTag: search->second) {
              //llvm::errs() << "mismatch " << *v << " " << *std::get<0>(AddrAndTag) << "\n";
              if (std::get<0>(AddrAndTag) == v) {
                shadowAddr = std::get<1>(AddrAndTag);
                tag        = std::get<2>(AddrAndTag);
                break;
              }
            }
          }

          auto domSearch = bb2ImmDom.find(domTrav);
          if (domSearch == bb2ImmDom.end()) {
            break;
          }
          domTrav = domSearch->second;
        }
        if (!shadowAddr || !tag) {
          llvm::errs() << "assumption2 for value " << *v << "\n";
          __builtin_trap();
        }

        Value* shadTag8    = IRBIntr.CreateLoad(shadowAddr);
        Value* tagMismatch = IRBIntr.CreateICmpNE(shadTag8, tag);

        MDNode *weight = MDBuilder(C).createBranchWeights(1, 100000);
        Instruction* killBBStart = llvm::SplitBlockAndInsertIfThen(tagMismatch, insertionPoint, true, weight);

        IRBIntr.SetInsertPoint(killBBStart);

        InlineAsm* EmptyAsm = InlineAsm::get(FunctionType::get(IRBIntr.getVoidTy(), false),
					     StringRef(""), StringRef(""), /*hasSideEffects=*/true);
        IRBIntr.CreateCall(EmptyAsm, {});

        std::vector<Value*> noArgs;
        IRBIntr.CreateCall(abortIntr, noArgs);
      }
    }

    Value* mismatchReduced = nullptr;

    auto rsearch = BB2RegularChecks.find(BB);
    if (rsearch != BB2RegularChecks.end()) {
      auto& checks = rsearch->second;

      IRBuilder<> IRBIntr(insertionPoint);
      std::vector<Value*> ptrAsInteg;
      for (Value* v: checks) {

        if (v->getType()->isPointerTy()) {
          ptrAsInteg.push_back(IRBIntr.CreatePtrToInt(v, Int64Ty));
        }
        else if (v->getType()->isIntegerTy(64)) {
          ptrAsInteg.push_back(v);
        }
        else {
          llvm::errs() << "assumption 456\n";
          __builtin_trap();
        }
      }

      std::vector<Value*> ptrGranRem;
      for (Value* v: ptrAsInteg) {
        ptrGranRem.push_back(IRBIntr.CreateLShr(v, ConstantInt::get(Int64Ty, DF_TAG_GRANULARITY_SHIFT)));
      }

      std::vector<Value*> shadOffset;
      for (Value* v: ptrGranRem) {
        shadOffset.push_back(IRBIntr.CreateAnd(v, ConstantInt::get(Int64Ty, DF_SHADOW_OFFSET_MASK)));
      }

      std::vector<Value*> shadTag32;
      for (Value* v: shadOffset) {
        std::vector<Value*> indexes;
        indexes.push_back(v);
        Value* shadPtr   = IRBIntr.CreateInBoundsGEP(shadowArea, indexes); // = GVShad[]

        Value* _shadTag8  = IRBIntr.CreateLoad(shadPtr);
        Value* _shadTag32 = IRBIntr.CreateZExt(_shadTag8, Int32Ty);

        shadTag32.push_back(_shadTag32);
      }

      std::vector<Value*> ptrXored;
      for (Value* v: ptrAsInteg) {
        Value* _prefixXored  = IRBIntr.CreateXor(v, heapPrefix);
        ptrXored.push_back(_prefixXored);
      }

      std::vector<Value*> ptrPrefixShifted;
      for (Value* v: ptrXored) {
        Value* _ptrPrefixShifted = IRBIntr.CreateLShr(v, ConstantInt::get(Int64Ty, DF_PTR_BITS));
        ptrPrefixShifted.push_back(_ptrPrefixShifted);
      }

      std::vector<Value*> maskAndVal;
      for (Value* v: ptrPrefixShifted) {
        Value* prefixAnded = IRBIntr.CreateAnd(v, ConstantInt::get(Int64Ty, 0x80000000 - (1 << DF_MTAG_BITS)));
        Value* isNonHeap   = IRBIntr.CreateICmpNE(prefixAnded, ConstantInt::get(Int64Ty, 0));
        Value* _maskAndVal = IRBIntr.CreateSelect(isNonHeap,
                                                  ConstantInt::get(Int32Ty, 0),
                                                  ConstantInt::get(Int32Ty, (1 << DF_MTAG_BITS) - 1));
        maskAndVal.push_back(_maskAndVal);
      }

      std::vector<Value*> dirtyTagXored;
      for (unsigned idx = 0; idx < shadTag32.size(); idx++) {
        Value* _shadTag32 = shadTag32[idx];
        Value* _ptrPrefixShifted   = ptrPrefixShifted[idx];
        Value* _ptrPrefixShifted32 = IRBIntr.CreateTrunc(_ptrPrefixShifted, Int32Ty);

        Value* _dirtyTagXored  = IRBIntr.CreateXor(_ptrPrefixShifted32, _shadTag32);
        dirtyTagXored.push_back(_dirtyTagXored);
      }

      std::vector<Value*> tagMismatch;
      for (unsigned idx = 0; idx < dirtyTagXored.size(); idx++) {
        Value* _dirtyTagXored = dirtyTagXored[idx];
        Value* _maskAndVal = maskAndVal[idx];
        Value* _tagMismatch =  IRBIntr.CreateAnd(_dirtyTagXored, _maskAndVal);
        tagMismatch.push_back(_tagMismatch);
      }

      for (Value* v: tagMismatch) {
        if (!mismatchReduced) {
          mismatchReduced = v;
        }
        else {
          mismatchReduced = IRBIntr.CreateOr(mismatchReduced, v);
        }
      }
    }

    if (mismatchReduced == nullptr) {
      continue;
    }

    IRBuilder<> IRBIntr(insertionPoint);
    Value* hopeFalse = IRBIntr.CreateICmpNE(mismatchReduced, ConstantInt::get(Int32Ty, 0));

    MDNode *weight = MDBuilder(C).createBranchWeights(1, 100000);
    Instruction* fallbackBBStart = llvm::SplitBlockAndInsertIfThen(hopeFalse, insertionPoint, true, weight);

    IRBIntr.SetInsertPoint(fallbackBBStart);
    std::vector<Value*> noArgs;
    IRBIntr.CreateCall(abortIntr, noArgs);
  }
}


bool UAFChecker::runOnFunction(Function &F) {
  if (F.isDeclaration()) {
    return false;
  }

  // some functions are skipped by name to make firefox work
  if (is_skipped(F)) {
    return false;
  }

  normalize_function(F, this->summaryIndex);

  DominatorTree DT(F);
  LoopInfo LI(DT);
  BasedOnTree basedOnTree(F);

  auto bbProps = compute_bb_properties(F, this->summaryIndex);


  PointerValidity pointerValidity(F, DT, LI, basedOnTree, bbProps);

  UncheckedUseAnalysis uua(F, LI, basedOnTree, bbProps);
  choose_checks(F, uua, basedOnTree, pointerValidity, bbProps, LI);
  insert_checks_scalar(F, DT, LI, uua, basedOnTree, bbProps);

  // we create many redundant BBs, try to remove some
  // to reduce memory consumption
  std::vector<BasicBlock*> BBs;
  for (BasicBlock& BB: F) {
    BBs.push_back(&BB);
  }
  for (BasicBlock* BB: BBs) {
    MergeBlockIntoPredecessor(BB);
  }

  return true;
}


void profilerEvalOnFunction(Function& F) {
  Module& M = *F.getParent();
  LLVMContext &C = M.getContext();
  MDNode* MDassumeT  = MDNode::get(C, MDString::get(C, "assumeTrue"));
  MDNode* MDassumeF  = MDNode::get(C, MDString::get(C, "assumeFalse"));
  MDNode* MDassumeU  = MDNode::get(C, MDString::get(C, "assumeMixed"));

  for (auto& BB: F) {
    for (BasicBlock::iterator i = BB.begin(), ie = BB.end(); i != ie; ++i) {
      SelectInst* selectInst = dyn_cast<SelectInst>(&*i);
      if (!selectInst) {
        continue;
      }
      if (!selectInst->getMetadata("UAFCheckerProfilePointer")) {
        continue;
      }
      uint64_t trueVal, falseVal;
      if (!selectInst->extractProfMetadata(trueVal, falseVal)) {
        continue;
      }
      if (trueVal == 0 && falseVal == 0) {
        continue;
      }

      int isHeap;
      if (trueVal > 0 && falseVal == 0) {
        isHeap = 1;
      }
      else if (trueVal == 0 && falseVal > 0) {
        isHeap = -1;
      }
      else if (falseVal * 1000 / trueVal == 0) {
        isHeap = 1;
      }
      else if (trueVal * 1000 / falseVal == 0) {
        isHeap = -1;
      }
      else {
        isHeap = 0;
      }

      ICmpInst* cmpInst = dyn_cast<ICmpInst>(selectInst->getCondition());
      if (!cmpInst) {
        continue;
      }
      BinaryOperator* binOp = dyn_cast<BinaryOperator>(cmpInst->getOperand(0));
      if (!binOp || binOp->getOpcode() != Instruction::LShr) {
        continue;
      }

      binOp = dyn_cast<BinaryOperator>(binOp->getOperand(0));
      if (!binOp || binOp->getOpcode() != Instruction::Xor) {
        continue;
      }

      Value* ptrDef = nullptr;
      Value* ptrAsInteg = binOp->getOperand(0);
      if (PtrToIntInst* ptrtoint = dyn_cast<PtrToIntInst>(ptrAsInteg)) {
        ptrDef = ptrtoint->getPointerOperand();
      }
      else if (ptrAsInteg->getType()->isIntegerTy(64)) {
        ptrDef = ptrAsInteg;
      }
      else {
        continue;
      }

      // ptrDef can be either of pointer type or an integer which
      // is used in one (or multiple) IntToPtrInst

      if (Instruction* ptrCreation = dyn_cast<Instruction>(ptrDef)) {
        if (isHeap == 1) {
          ptrCreation->setMetadata("UAFCheckerFrequency", MDassumeT);
        }
        else if (isHeap == 0) {
          ptrCreation->setMetadata("UAFCheckerFrequency", MDassumeU);
        }
        else if (isHeap == -1) {
          ptrCreation->setMetadata("UAFCheckerFrequency", MDassumeF);
        }
      }
      else if (Argument* arg = dyn_cast<Argument>(ptrDef)) {
        if (isHeap == 1) {
          arg->addAttr(Attribute::AssumeHeapPointer);
        }
        else if (isHeap == 0) {
          arg->addAttr(Attribute::AssumeMixedPointer);
        }
        else if (isHeap == -1) {
          arg->addAttr(Attribute::AssumeNonHeapPointer);
        }
      }
      else {
        llvm::errs() << "whoopsi dupsi we got a: " << F.getName() << " " << *ptrDef << "\n";
      }
    }
  }
}


void profilerRunOnFunction(Function& F) {
  std::vector<Value*> ptrVals;
  for (auto& BB: F) {
    for (BasicBlock::iterator i = BB.begin(), ie = BB.end(); i != ie; ++i) {
      Instruction* inst = &*i;
      if (!inst->getType()->isPointerTy()) {
        continue;
      }

      if (isa<LoadInst>(inst) ||
          isa<CallBase>(inst) ||
          isa<ExtractValueInst>(inst) ||
          isa<PHINode>(inst) ||
          isa<SelectInst>(inst)) {
        ptrVals.push_back(inst);
      }
      else if (IntToPtrInst* inttoptr = dyn_cast<IntToPtrInst>(inst)) {
        ptrVals.push_back(inttoptr->getOperand(0));
      }
      else if (isa<AllocaInst>(inst) ||
               isa<BitCastInst>(inst) ||
               isa<GetElementPtrInst>(inst)) {
        continue;
      }
      else {
        llvm::errs() << "unknown pointer definition: " << *inst << "\n";
      }
    }
  }
  for (Argument& arg: F.args()) {
    if (!arg.getType()->isPointerTy()) {
      continue;
    }
    ptrVals.push_back(&arg);
  }

  if (ptrVals.empty()) {
    return;
  }

  Module& M = *F.getParent();
  LLVMContext &C = M.getContext();
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);

  Instruction* heapPrefix = load_heap_prefix(F);
  MDNode* N = MDNode::get(C, MDString::get(C, ""));

  for (Value* ptrVal: ptrVals) {
    Instruction* insertionPoint = nullptr;

    if (isa<Argument>(ptrVal)) {
      insertionPoint = heapPrefix->getNextNonDebugInstruction();
    }
    else if (InvokeInst* invoke = dyn_cast<InvokeInst>(ptrVal)) {
      BasicBlock* normalBB = invoke->getNormalDest();
      if (normalBB->hasNPredecessorsOrMore(2)) {
        // if the pointer is used it must pass through a PHINode anyways
        continue;
      }
      insertionPoint = &*normalBB->getFirstInsertionPt();
    }
    else if (PHINode* phinode = dyn_cast<PHINode>(ptrVal)) {
      insertionPoint = &*phinode->getParent()->getFirstInsertionPt();
    }
    else if (Instruction* inst = dyn_cast<Instruction>(ptrVal)) {
      insertionPoint = inst->getNextNonDebugInstruction();
    }
    else {
      __builtin_trap();
    }

    IRBuilder<> IRBIntr(insertionPoint);
    Value* ptrAsInteg = nullptr;
    if (ptrVal->getType()->isIntegerTy()) {
      if (!ptrVal->getType()->isIntegerTy(64)) {
        // we currently don't support other integers; implementing
        // needs support in the pattern matching of
        // profilerEvalOnFunction as well
        continue;
      }
      ptrAsInteg = ptrVal;
    }
    else if (ptrVal->getType()->isPointerTy()) {
      ptrAsInteg = IRBIntr.CreatePtrToInt(ptrVal, Int64Ty);
    }
    else {
      __builtin_trap();
    }
    Value* ptrXored   = IRBIntr.CreateXor(ptrAsInteg, heapPrefix);
    Value* ptrShifted = IRBIntr.CreateLShr(ptrXored,
                                           ConstantInt::get(Int64Ty, DF_PTR_BITS + DF_MTAG_BITS));
    Value* isHeap     = IRBIntr.CreateICmpEQ(ptrShifted, ConstantInt::get(Int64Ty, 0));
    // this select is trivially dead and just inserted so it can get
    // picked up by the profiler instrumentation generation which runs
    // immediately after this pass. thus we can collect profiling information
    // whether a pointer usually points into our special heap region
    Value* select = IRBIntr.CreateSelect(isHeap,
                                         ConstantInt::get(Int64Ty, 1),
                                         ConstantInt::get(Int64Ty, 0));
    Instruction* selectInst = dyn_cast<SelectInst>(select);
    selectInst->setMetadata("UAFCheckerProfilePointer", N);
  }
}


namespace {
  class UAFProfiler : public FunctionPass {

    public:
      static char ID;
      UAFProfiler(bool _addInstrumentation) : FunctionPass(ID),
                                              addInstrumentation(_addInstrumentation) { }
      bool runOnFunction(Function &F) override;

    private:
      bool addInstrumentation;
  };
}

char UAFProfiler::ID = 0;

FunctionPass *
llvm::createUAFProfilerPass(bool addInstrumentation) {
  return new UAFProfiler(addInstrumentation);
}

bool UAFProfiler::runOnFunction(Function& F) {
  if (F.isDeclaration()) {
    return false;
  }

  if (addInstrumentation) {
    profilerRunOnFunction(F);
    return true;
  }
  else {
    profilerEvalOnFunction(F);
    return false;
  }
}
