//===------------------------- IdentifyFunctionLoops.h -------------------------===//
//
//                     The LLVM Compiler Infrastructure
// 
// This file is distributed under the Università della Svizzera italiana (USI) 
// Open Source License.
//
// Author         : Georgios Zacharopoulos 
// Date Started   : June, 2018
//
//===----------------------------------------------------------------------===//
//
// This file identifies Functions and Loops within the functions of an
// application.
//
//===----------------------------------------------------------------------===//


  int find_function(std::vector<Function *> list, Function *F) {

    for (unsigned i = 0; i < list.size(); i++)
      if (list[i] == F)
        return i;
    
    return -1;
  }


