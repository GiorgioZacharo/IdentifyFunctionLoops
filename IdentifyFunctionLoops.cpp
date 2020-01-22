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

      getInputFunction(&F);
      gatherLoadsandStores(&F);
      getLoopsOfFunction(&F, LI, SE);


      return false;
    }

    // Loops Identifier of a given function. (if any loops)
    //
    void getLoopsOfFunction (Function *F, LoopInfo &LI, ScalarEvolution &SE ) {

      long unsigned int NumberOfInstructions = 0;

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

        else { // No loops
          for(BasicBlock::iterator BI = CurrentBlock->begin(), BE = CurrentBlock->end(); BI != BE; ++BI)
            NumberOfInstructions++;
        }
      } // End of for
      errs() << "   ----------------------------------------------" << '\n';
      errs() << " Number of Instructions (Loops Excluded) : " << NumberOfInstructions << "\n";
      errs() << "   ----------------------------------------------" << '\n';
    }

  // START 
  // IMPORT FROM ACCELSEEKER FUNCTIONS
  //
  //
  bool structNameIsValid(llvm::Type *type) {

    if (type->getStructName() == "struct._IO_marker")
      return 0;
    if (type->getStructName() == "struct._IO_FILE")
      return 0;


    return 1;
  }

  // Gather the data of the Array type.
  //
  long int getTypeArrayData(llvm::Type *type) {

    long int array_data=0;
    int TotalNumberOfArrayElements = 1;

    while (type->isArrayTy()) {

      llvm::Type *array_type    = type->getArrayElementType();
      int NumberOfArrayElements     = type->getArrayNumElements();
      int SizeOfElement           = array_type->getPrimitiveSizeInBits();

     errs() << "\n\t Array " << *array_type << " "  << NumberOfArrayElements<< " " << SizeOfElement  << " \n ";

      TotalNumberOfArrayElements *= NumberOfArrayElements;

      if (SizeOfElement) {
        array_data = TotalNumberOfArrayElements * SizeOfElement;
        return array_data ;
      }
      else
        type = array_type;
    }
    return array_data;  
  }

  long int getTypeData(llvm::Type *type){

    long int arg_data =0;

    if ( type->isPointerTy()){
      errs() << "\n\t Pointer Type!  " << " \n --------\n";


      llvm::Type *Pointer_Type = type->getPointerElementType();
      arg_data+=getTypeData(Pointer_Type);
    }

    // Struct Case
    else if ( type->isStructTy()) {

      long int struct_data=0;
      unsigned int NumberOfElements = type->getStructNumElements();

      for (int i=0; i<NumberOfElements; i++){

        llvm::Type *element_type = type->getStructElementType(i);
        errs() << "\n\t Struct -- Arg: " << i << " " << *element_type << " "
            << type->getStructName() << " \n ";

        if (structNameIsValid(type))
          struct_data +=  getTypeData(element_type);
  
      }
      arg_data = struct_data;
      //return arg_data;    
    }

    // Scalar Case
    else if ( type->getPrimitiveSizeInBits()) {
      //errs() << "\n\t Primitive Size  " <<  type->getPrimitiveSizeInBits()  << " \n ";
      arg_data = type->getPrimitiveSizeInBits();
      //return arg_data;

    }
 
    // Vector Case
    else if ( type->isVectorTy()) {
      //errs() << "\n\t Vector  " <<  type->getPrimitiveSizeInBits()  << " \n ";
      arg_data = type->getPrimitiveSizeInBits();
      //return arg_data;
    }


    // Array Case
    else if(type->isArrayTy()) {
      arg_data = getTypeArrayData(type);
      //errs() << "\n\t Array Data " << arg_data << " \n ";
      //return arg_data;
    }

    return arg_data;
  }

    // Input from parameter List.
    //
    //
    long int getInputFunction(Function *F) {
      long  int InputData = 0; // Bits
      long int InputDataBytes = 0; // Bytes

      int arg_index=0;

      Function::ArgumentListType & Arg_List = F->getArgumentList();

      for (Function::arg_iterator AB = Arg_List.begin(), AE = Arg_List.end(); AB != AE; ++AB){

        llvm::Argument *Arg = &*AB;
        llvm::Type *Arg_Type = Arg->getType();




        errs() << "\n\n Argument : " << arg_index << "  --->  " << *AB << " -- " << *Arg_Type  << " --  \n ";

        long int InputDataOfArg = getTypeData(Arg_Type);
        errs() << "\n\n Argument : " << arg_index << "  -- Input Data --  " << InputDataOfArg<< " \n "; 

        InputData += InputDataOfArg;
        arg_index++;

       }

       errs() << "\n\n Total Input Data Bits :  " << InputData << " \n ";
       InputDataBytes = InputData/8; 
       errs() << "\n\n Total Input Data Bytes :  " << InputDataBytes << " \n ";

      return InputDataBytes;
    }

    // Gather Stores and Loads from Functions
    //
    //
    void gatherLoadsandStores(Function *F) {
      long unsigned int NumberOfInstructions = 0;

      // BlockFrequencyInfo *BFI = &getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI(); 


      for(Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB) {
        BasicBlock *CurrentBlock = &*BB;

        // float BBFreqFloat = static_cast<float>(static_cast<float>(BFI->getBlockFreq(CurrentBlock).getFrequency()) / static_cast<float>(BFI->getEntryFreq()));
        // int EntryFuncFreq = getEntryCount(F);
        // float BBFreq = BBFreqFloat * static_cast<float>(EntryFuncFreq);

        errs() << " BB Name :  " << CurrentBlock->getName() << " \n ";
        // errs() << " Entry Freq :  " << EntryFuncFreq << " \n ";
        // errs() << " BB Freq :  " << BBFreqFloat << " \n ";
        // errs() << " BB Total Freq :  " << BBFreq << " \n ";

        // Iterate inside the basic block.
        for(BasicBlock::iterator BI = CurrentBlock->begin(), BE = CurrentBlock->end(); BI != BE; ++BI) {

          // Load Info
          if(LoadInst *Load = dyn_cast<LoadInst>(&*BI)) {

            llvm::Type *LoadType = Load->getType();
            // llvm::Type *Ptr_LoadType = NULL;

            if ( LoadType->isPointerTy()) {
              llvm::Type *Ptr_LoadType = LoadType->getPointerElementType();

               if (Ptr_LoadType->isStructTy() || Ptr_LoadType->isArrayTy() || Ptr_LoadType->isVectorTy()) {
                  errs() << "\t" << *Load << "\t"  << *Load->getType() << "\t\t" << "\n";
                  getTypeData(LoadType);
                }
            }

            //errs() << "\t" << *Load << "\t"  << *Load->getType() << "\t\t" << "\n";

           
              // errs() << "\t" << *Load << "\t"  << *Load->getType() << "\t\t" << getTypeData(LoadType) << "\n";

          }

            //int InputLoad = Load->getType()->getPrimitiveSizeInBits();
          NumberOfInstructions++;
        } // End of BB For
      } // End of Function For
      errs() << "   ----------------------------------------------" << '\n';
      errs() << " Number of Instructions : " << NumberOfInstructions << "\n";
      errs() << "   ----------------------------------------------" << '\n';
    }
          

    // END 
    // IMPORT FROM ACCELSEEKER FUNCTIONS



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
