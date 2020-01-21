//===------------------------- IdentifyFunctionLoops.cpp -------------------------===//
//
//                     The LLVM Compiler Infrastructure
// 
// This file is distributed under the Università della Svizzera italiana (USI) 
// Open Source License.
//
// Author         : Georgios Zacharopoulos 
// Date Started   : April, 2019
//
//===----------------------------------------------------------------------===//
//
// This file identifies Functions and Loops within the functions of an
// application.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/RegionPass.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/RegionIterator.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BlockFrequencyInfoImpl.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Transforms/Utils/Local.h"
#include <string>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <algorithm>
#include "llvm/IR/CFG.h"
#include "../Identify.h" // Common Header file for all RegionSeeker Passes.
//#include "IdentifyFunctionLoops.h"

#define DEBUG_TYPE "IdentifyFunctionLoops"

using namespace llvm;

namespace {

  struct IdentifyFunctionLoops : public FunctionPass {
    static char ID; // Pass Identification, replacement for typeid

    std::vector<Loop *> Loops_list; // Global Loop List

    IdentifyFunctionLoops() : FunctionPass(ID) {}

    // Function Identifier
    //
    bool runOnFunction(Function &F) override {

      LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
      ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
      std::string Function_Name = F.getName();

      Loops_list.clear(); // Clear the Loops List


      errs() << "\n\n\tFunction Name is : " << Function_Name << "\n";
      errs() << "   **********************************************" << '\n';

     
      getLoopsOfFunction(&F, LI, SE);


      return false;
    }

    // Loops Identifier of a given function. (if any loops)
    //
    void getLoopsOfFunction (Function *F, LoopInfo &LI, ScalarEvolution &SE ) {

      for(Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB) {

        BasicBlock *CurrentBlock = &*BB;

        // Iterate inside the Loop.
        if (Loop *L = LI.getLoopFor(CurrentBlock)) {
           if (find_loop(Loops_list, L) == -1) { // If Loop not in our list
              Loops_list.push_back(L);

              errs() << "\n     Num of Back Edges     : " << L->getNumBackEdges() << "\n";
              errs() << "     Loop Depth            : " << L->getLoopDepth() << "\n";
              errs() << "     Backedge Taken Count  : " << *SE.getBackedgeTakenCount(L) << '\n';
              errs() << "     Loop iterations       : " << SE.getSmallConstantTripCount(L) << "\n\n";

          }
        }
      } // End of for

    }


    virtual void getAnalysisUsage(AnalysisUsage& AU) const override {
              
        AU.addRequired<LoopInfoWrapperPass>();
        AU.addRequiredTransitive<ScalarEvolutionWrapperPass>();
        // AU.addRequired<RegionInfoPass>();
        AU.addRequired<DependenceAnalysis>();
        // AU.addRequiredTransitive<RegionInfoPass>();      
        // AU.addRequired<BlockFrequencyInfoWrapperPass>();
        AU.setPreservesAll();
    } 
  };
}

char IdentifyFunctionLoops::ID = 0;
static RegisterPass<IdentifyFunctionLoops> X("IdentifyFunctionLoops", "Identify Loops within Functions");
