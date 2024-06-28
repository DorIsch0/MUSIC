#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include <iostream>
#include <fstream>

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "../include/Function.h" // some versions seem to not include the insert function, so I just pasted it from an older version into this custom Function.h file
//#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"

#include "midi2code.h"
#include "inputLLHeaderFile.h"

using namespace std;
using namespace llvm;

int DEBUGLVL=0; /*
  0: no debug output
  1: print every arg you got along the translation process from midi to inter plus the resulting inter code at the end of the translation stage
  2: same as 1 plus print the list of notes at the start of the program, and every time you want to get an arg print which type, and every time you got a token print the sum of that token,
     and in the compilation stage print which line gets parsed everytime a line gets parsed
  3: same as 2 plus print the list of notes in every call of getToken
  */

Value* getSomethingValue(string);
Value* getVarVal(string);
Type* getType(string);

void parsePrt(string);
void parsePrtS(string);
void parseSubPrt(Value*);
void parseSubPrtS(Value*);

string subStrTo(string s,char d,unsigned from=0){
  unsigned idx=from;
  for(;idx<s.length()&&s.at(idx)!=d;idx++);
  return s.substr(from,idx-from);
}

int exitCode=0;

void error(string s,int ec=-1){
  exitCode=ec;
  fprintf(stderr,"Error: %s\n",s.c_str());
}

unique_ptr<LLVMContext> ctx;
unique_ptr<IRBuilder<>> builder;
unique_ptr<Module> mdl;
unique_ptr<legacy::FunctionPassManager> fpm;

bool prtUsed=false,inpUsed=false,mallocFnsUsed=false;

Function* mallocFn;Function* memmoveFn;Function* freeFn;
Function* printfFn;Function* getcFn;Function* strtolFn;Function* strtodFn;

void initMallocFns(){
  mallocFnsUsed=true;
  Type* i[]={Type::getInt64Ty(*ctx)};
  mallocFn=Function::Create(FunctionType::get(Type::getInt8PtrTy(*ctx),i,false),Function::ExternalLinkage,"malloc",mdl.get());
  Type* j[]={Type::getInt8PtrTy(*ctx)};
  freeFn=Function::Create(FunctionType::get(Type::getVoidTy(*ctx),j,false),Function::ExternalLinkage,"free",mdl.get());
  Type* k[]={Type::getInt8PtrTy(*ctx),Type::getInt8PtrTy(*ctx),Type::getInt64Ty(*ctx)};
  memmoveFn=Function::Create(FunctionType::get(Type::getInt8PtrTy(*ctx),k,false),Function::ExternalLinkage,"memmove",mdl.get());
}

struct dynArrIR{ // no get or set because that's just some GEP and  load or store action, doesn't need to be in a seperate fn
                 // no remove because that's just pop and ignoring the return
  string typeString;
  StructType* type;
  string subTypeS;
  Type* subType;
  Function* create;
  Function* resize;
  Function* append;
  Function* insert;
  Function* pop;
  Function* destroy;
  Function* copy;
  Function* concat;
};

map<string,dynArrIR> dynArrTypes;

Value* getTypeSize(Type* t,BasicBlock* bb){
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  tmp->SetInsertPoint(bb);
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),1)};
  Value* tempForSize=tmp->CreateGEP(t,ConstantPointerNull::get(PointerType::getUnqual(t)),idcs,"tempForSize");
  return tmp->CreatePtrToInt(tempForSize,Type::getInt64Ty(*ctx),"sizeOfType");
}

Value* createEntryAlloca(Function* f,Type* t,string name="alloca"){
  IRBuilder<> tmp(&f->getEntryBlock(),f->getEntryBlock().begin());
  return tmp.CreateAlloca(t,nullptr,name);
}

Function* makeDynArrCreate(dynArrIR* dair){ // create(&darr,capac)
  StructType* t=dair->type;Type* st=dair->subType;
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  Type* args[]={PointerType::getUnqual(t),Type::getInt64Ty(*ctx)};
  Function* f=Function::Create(FunctionType::get(Type::getVoidTy(*ctx),args,false),Function::ExternalLinkage,dair->typeString+"_create",mdl.get());
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",f);
  tmp->SetInsertPoint(bb);
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
  Value* sp=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"sp");
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
  Value* lp=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"lp");
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),2);
  Value* cp=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"cp");
  tmp->CreateStore(ConstantInt::get(Type::getInt64Ty(*ctx),0),lp);
  tmp->CreateStore(&f->args().begin()[1],cp);
  Value* args_[]={tmp->CreateMul(&f->args().begin()[1],getTypeSize(st,bb))};
  tmp->CreateStore(tmp->CreateBitCast(tmp->CreateCall(mallocFn,args_,"mallocCall"),PointerType::getUnqual(st)),sp);
  tmp->CreateRet(nullptr);
  
  verifyFunction(*f);
  fpm->run(*f);
  return f;
}

Function* makeDynArrResize(dynArrIR* dair){ // resize(&darr,capac)
  StructType* t=dair->type;Type* st=dair->subType;
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  Type* args[]={PointerType::getUnqual(t),Type::getInt64Ty(*ctx)};
  Function* f=Function::Create(FunctionType::get(Type::getVoidTy(*ctx),args,false),Function::ExternalLinkage,dair->typeString+"_resize",mdl.get());
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",f);
  tmp->SetInsertPoint(bb);
  Value* bs=getTypeSize(st,bb);
  Value* args1[]={tmp->CreateMul(&f->args().begin()[1],bs,"bytes")};
  Value* newPointer=tmp->CreateCall(mallocFn,args1,"newPointer");
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),1)};
  Value* ncpy=tmp->CreateMul(bs,tmp->CreateLoad(Type::getInt64Ty(*ctx),tmp->CreateGEP(t,&f->args().begin()[0],idcs,"lenPointer"),"len"));
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),0);
  Value* odpp=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"oldPointerP");
  Value* oldPointeri8=tmp->CreateBitCast(tmp->CreateLoad(PointerType::getUnqual(st),odpp,"oldPointer"),Type::getInt8PtrTy(*ctx),"oldPointeri8");
  Value* args2[]={newPointer,oldPointeri8,ncpy};
  tmp->CreateCall(memmoveFn,args2,"memmove");
  Value* args3[]={oldPointeri8};
  tmp->CreateCall(freeFn,args3);
  tmp->CreateStore(tmp->CreateBitCast(newPointer,PointerType::getUnqual(st),"newPointerSTPointer"),odpp);
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),2);
  tmp->CreateStore(&f->args().begin()[1],tmp->CreateGEP(t,&f->args().begin()[0],idcs,"capacPointer"));
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
  Value* lenP=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"lenP");
  Value* len=tmp->CreateLoad(Type::getInt64Ty(*ctx),lenP,"len");
  tmp->CreateStore(tmp->CreateSelect(tmp->CreateICmpUGT(len,&f->args().begin()[1],"lenGTCapac"),&f->args().begin()[1],len,"newLen"),lenP);
  tmp->CreateRet(nullptr);
  verifyFunction(*f);
  fpm->run(*f);
  return f;
}

Function* makeDynArrAppend(dynArrIR* dair){ // append(&darr,el)
  StructType* t=dair->type;Type* st=dair->subType;
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  Type* args[]={PointerType::getUnqual(t),st};
  Function* f=Function::Create(FunctionType::get(Type::getVoidTy(*ctx),args,false),Function::ExternalLinkage,dair->typeString+"_append",mdl.get());
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",f);
  tmp->SetInsertPoint(bb);
  
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),1)};
  Value* lenP=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"lenP");
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),2);
  Value* capacP=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"capacP");
  Value* len=tmp->CreateLoad(Type::getInt64Ty(*ctx),lenP,"len");
  Value* capac=tmp->CreateLoad(Type::getInt64Ty(*ctx),capacP,"capac");
  BasicBlock* increaseSize=BasicBlock::Create(*ctx,"increaseSize",f);
  BasicBlock* afterIncreasing=BasicBlock::Create(*ctx,"afterIncreasing");
  tmp->CreateCondBr(tmp->CreateICmpEQ(len,capac,"needToIncrease"),increaseSize,afterIncreasing);
  tmp->SetInsertPoint(increaseSize);
  Value* args1[]={&f->args().begin()[0],tmp->CreateMul(capac,ConstantInt::get(Type::getInt64Ty(*ctx),2),"newCapac")};
  tmp->CreateCall(dair->resize,args1);
  tmp->CreateBr(afterIncreasing);
  f->insert(f->end(),afterIncreasing);
  tmp->SetInsertPoint(afterIncreasing);
  tmp->CreateStore(tmp->CreateAdd(len,ConstantInt::get(Type::getInt64Ty(*ctx),1),"newLen"),lenP);
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),0);
  Value* idcs1[]={len};
  tmp->CreateStore(&f->args().begin()[1],tmp->CreateGEP(st,tmp->CreateLoad(PointerType::getUnqual(st),tmp->CreateGEP(t,&f->args().begin()[0],idcs,"dataPP"),"dataP"),idcs1,"offsP"));
  tmp->CreateRet(nullptr);
  verifyFunction(*f);
  fpm->run(*f);
  return f;
}

Function* makeDynArrInsert(dynArrIR* dair){ // insert(&darr,el,idx)
  StructType* t=dair->type;Type* st=dair->subType;
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  Type* args[]={PointerType::getUnqual(t),st,Type::getInt64Ty(*ctx)};
  Function* f=Function::Create(FunctionType::get(Type::getVoidTy(*ctx),args,false),Function::ExternalLinkage,dair->typeString+"_insert",mdl.get());
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",f);
  tmp->SetInsertPoint(bb);
  
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),1)};
  Value* lenP=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"lenP");
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),2);
  Value* capacP=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"capacP");
  Value* len=tmp->CreateLoad(Type::getInt64Ty(*ctx),lenP,"len");
  Value* capac=tmp->CreateLoad(Type::getInt64Ty(*ctx),capacP,"capac");
  BasicBlock* increaseSize=BasicBlock::Create(*ctx,"increaseSize",f);
  BasicBlock* afterIncreasing=BasicBlock::Create(*ctx,"afterIncreasing");
  tmp->CreateCondBr(tmp->CreateICmpEQ(len,capac,"needToIncrease"),increaseSize,afterIncreasing);
  tmp->SetInsertPoint(increaseSize);
  Value* args1[]={&f->args().begin()[0],tmp->CreateMul(capac,ConstantInt::get(Type::getInt64Ty(*ctx),2),"newCapac")};
  tmp->CreateCall(dair->resize,args1);
  tmp->CreateBr(afterIncreasing);
  f->insert(f->end(),afterIncreasing);
  tmp->SetInsertPoint(afterIncreasing);
  Value* newLen=tmp->CreateAdd(len,ConstantInt::get(Type::getInt64Ty(*ctx),1),"newLen");
  tmp->CreateStore(newLen,lenP);
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),0);
  Value* dataPP=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"dataPP");
  Value* dataP=tmp->CreateLoad(PointerType::getUnqual(st),dataPP,"dataP");
  Value* idcs1[]={&f->args().begin()[2]};
  Value* insertPointP=tmp->CreateGEP(st,dataP,idcs1,"insertPointP");
  idcs1[0]=tmp->CreateAdd(&f->args().begin()[2],ConstantInt::get(Type::getInt64Ty(*ctx),1));
  Value* afterInsertPointP=tmp->CreateGEP(st,dataP,idcs1,"afterInsertPointP");
  Value* args2[]={tmp->CreateBitCast(afterInsertPointP,Type::getInt8PtrTy(*ctx)),
                  tmp->CreateBitCast(insertPointP,Type::getInt8PtrTy(*ctx)),
                  tmp->CreateMul(getTypeSize(st,bb),tmp->CreateSub(len,&f->args().begin()[2],"numToShift"))};
  tmp->CreateCall(memmoveFn,args2);
  tmp->CreateStore(&f->args().begin()[1],insertPointP);
  tmp->CreateRet(nullptr);
  verifyFunction(*f);
  fpm->run(*f);
  return f;
}

Function* makeDynArrPop(dynArrIR* dair){ // pop(&darr,idx)
  StructType* t=dair->type;Type* st=dair->subType;
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  Type* args[]={PointerType::getUnqual(t),Type::getInt64Ty(*ctx)};
  Function* f=Function::Create(FunctionType::get(st,args,false),Function::ExternalLinkage,dair->typeString+"_pop",mdl.get());
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",f);
  tmp->SetInsertPoint(bb);
  
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),1)};
  Value* lenP=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"lenP");
  Value* len=tmp->CreateLoad(Type::getInt64Ty(*ctx),lenP,"len");
  Value* newLen=tmp->CreateSub(len,ConstantInt::get(Type::getInt64Ty(*ctx),1),"newLen");
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),0);
  Value* dataP=tmp->CreateLoad(PointerType::getUnqual(st),tmp->CreateGEP(t,&f->args().begin()[0],idcs,"dataPP"),"dataP");
  Value* idcs1[]={&f->args().begin()[1]};
  Value* dataToPopP=tmp->CreateGEP(st,dataP,idcs1,"dataToPopP");
  Value* dataToPop=tmp->CreateLoad(st,dataToPopP,"dataToPop");
  idcs1[0]=tmp->CreateAdd(&f->args().begin()[1],ConstantInt::get(Type::getInt64Ty(*ctx),1));
  Value* afterDataToPopP=tmp->CreateGEP(st,dataP,idcs1,"afterDataToPopP");
  tmp->CreateStore(newLen,lenP);
  Value* args1[]={tmp->CreateBitCast(dataToPopP,Type::getInt8PtrTy(*ctx)),
                  tmp->CreateBitCast(afterDataToPopP,Type::getInt8PtrTy(*ctx)),
                  tmp->CreateMul(getTypeSize(st,bb),tmp->CreateSub(newLen,&f->args().begin()[1],"numToShift"))};
  tmp->CreateCall(memmoveFn,args1);
  tmp->CreateRet(dataToPop);
  verifyFunction(*f);
  fpm->run(*f);
  return f;
}

Function* makeDynArrDestroy(dynArrIR* dair){ // destroy(&darr)
  StructType* t=dair->type;Type* st=dair->subType;
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  Type* args[]={PointerType::getUnqual(t)};
  Function* f=Function::Create(FunctionType::get(Type::getVoidTy(*ctx),args,false),Function::ExternalLinkage,dair->typeString+"_destroy",mdl.get());
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",f);
  tmp->SetInsertPoint(bb);
  
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
  Value* dataP=tmp->CreateLoad(PointerType::getUnqual(st),tmp->CreateGEP(t,&f->args().begin()[0],idcs),"dataP");
  tmp->CreateCall(freeFn,tmp->CreateBitCast(dataP,Type::getInt8PtrTy(*ctx)));
  tmp->CreateRet(nullptr);
  verifyFunction(*f);
  fpm->run(*f);
  return f;
}

Function* makeDynArrCopy(dynArrIR* dair){ // copy(&dest,&src); dest should either be the same as source or not have to be created yet
  StructType* t=dair->type;Type* st=dair->subType;
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  Type* args[]={PointerType::getUnqual(t),PointerType::getUnqual(t)};
  Function* f=Function::Create(FunctionType::get(Type::getVoidTy(*ctx),args,false),Function::ExternalLinkage,dair->typeString+"_copy",mdl.get());
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",f);
  tmp->SetInsertPoint(bb);
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
  Value* destsp=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"destsp");
  Value* srcsp=tmp->CreateGEP(t,&f->args().begin()[1],idcs,"srcsp");
  Value* destspv=tmp->CreateLoad(PointerType::getUnqual(st),destsp);
  Value* srcspv=tmp->CreateLoad(PointerType::getUnqual(st),srcsp);
  Value* same=tmp->CreateICmpEQ(destspv,srcspv,"sameDarr");
  BasicBlock* bbNoJmp=BasicBlock::Create(*ctx,"continue",f);
  BasicBlock* bbRet=BasicBlock::Create(*ctx,"ret");
  tmp->CreateCondBr(same,bbRet,bbNoJmp);
  tmp->SetInsertPoint(bbNoJmp);
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
  Value* destlp=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"destlp");
  Value* srclp=tmp->CreateGEP(t,&f->args().begin()[1],idcs,"srclp");
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),2);
  Value* destcp=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"destcp");
  Value* srccp=tmp->CreateGEP(t,&f->args().begin()[1],idcs,"srccp");
  Value* len=tmp->CreateLoad(Type::getInt64Ty(*ctx),srclp,"srcl");
  tmp->CreateStore(len,destlp);
  Value* capac=tmp->CreateLoad(Type::getInt64Ty(*ctx),srccp,"srcc");
  tmp->CreateStore(capac,destcp);
  Value* typeSize=getTypeSize(st,bb);
  Value* args_[]={tmp->CreateMul(capac,typeSize)};
  Value* newPtr=tmp->CreateCall(mallocFn,args_,"mallocCall");
  tmp->CreateStore(tmp->CreateBitCast(newPtr,PointerType::getUnqual(st)),destsp);
  Value* oldPtr=tmp->CreateBitCast(srcspv,Type::getInt8PtrTy(*ctx),"oldPtri8");
  Value* args2[]={newPtr,oldPtr,tmp->CreateMul(len,typeSize)};
  tmp->CreateCall(memmoveFn,args2,"memmove");
  f->insert(f->end(),bbRet);
  tmp->CreateBr(bbRet);
  tmp->SetInsertPoint(bbRet);
  tmp->CreateRet(nullptr);
  
  verifyFunction(*f);
  fpm->run(*f);
  return f;
}

Function* makeDynArrConcat(dynArrIR* dair){ // concat(&dest,&left,&right)
  StructType* t=dair->type;Type* st=dair->subType;
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  Type* args[]={PointerType::getUnqual(t),PointerType::getUnqual(t),PointerType::getUnqual(t)};
  Function* f=Function::Create(FunctionType::get(Type::getVoidTy(*ctx),args,false),Function::ExternalLinkage,dair->typeString+"_concat",mdl.get());
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",f);
  tmp->SetInsertPoint(bb);
  Value* args_[]={&f->args().begin()[0],&f->args().begin()[1]};
  tmp->CreateCall(dair->copy,args_);
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),1)};
  Value* llp=tmp->CreateGEP(t,&f->args().begin()[1],idcs,"llp");
  Value* rlp=tmp->CreateGEP(t,&f->args().begin()[2],idcs,"rlp");
  Value* destlp=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"destlp");
  Value* ll=tmp->CreateLoad(Type::getInt64Ty(*ctx),llp,"ll");
  Value* rl=tmp->CreateLoad(Type::getInt64Ty(*ctx),rlp,"rl");
  Value* newLenAndCap=tmp->CreateAdd(ll,rl);
  args_[1]=newLenAndCap;
  tmp->CreateCall(dair->resize,args_);
  idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),0);
  Value* destDataPP=tmp->CreateGEP(t,&f->args().begin()[0],idcs,"destDataPP");
  Value* rDataPP=tmp->CreateGEP(t,&f->args().begin()[2],idcs,"rDataPP");
  Value* destDataP=tmp->CreateLoad(PointerType::getUnqual(st),destDataPP,"destDataP");
  Value* idcs1={ll};
  Value* destDataPOff=tmp->CreateGEP(st,destDataP,idcs1,"destDataPOff");
  Value* destDataPOffi8=tmp->CreateBitCast(destDataPOff,Type::getInt8PtrTy(*ctx),"destDataPOffi8");
  Value* rDataPi8=tmp->CreateBitCast(tmp->CreateLoad(PointerType::getUnqual(st),rDataPP),Type::getInt8PtrTy(*ctx),"rDataPi8");
  Value* args2[]={destDataPOffi8,rDataPi8,tmp->CreateMul(rl,getTypeSize(st,bb))};
  tmp->CreateCall(memmoveFn,args2,"memmove");
  tmp->CreateStore(newLenAndCap,destlp);
  tmp->CreateRet(nullptr);
  
  verifyFunction(*f);
  fpm->run(*f);
  return f;
}

void makeDynArrType(string t){
  if(!mallocFnsUsed)initMallocFns();
  dynArrIR dair;
  dair.typeString=t;
  string subTypeS=t.substr(5,t.length()-6);
  dair.subTypeS=subTypeS;
  dair.subType=getType(subTypeS);
  Type* els[]={PointerType::getUnqual(dair.subType),Type::getInt64Ty(*ctx),Type::getInt64Ty(*ctx),Type::getInt1Ty(*ctx)};
  dair.type=StructType::get(*ctx,els,false);
  dair.create=makeDynArrCreate(&dair);
  dair.resize=makeDynArrResize(&dair);
  dair.append=makeDynArrAppend(&dair);
  dair.insert=makeDynArrInsert(&dair);
  dair.pop=makeDynArrPop(&dair);
  dair.destroy=makeDynArrDestroy(&dair);
  dair.copy=makeDynArrCopy(&dair);
  dair.concat=makeDynArrConcat(&dair);
  dynArrTypes[t]=dair;
}

dynArrIR getDynArrIR(string t){
  if(dynArrTypes.count(t)==0){
    makeDynArrType(t);
  }
  return dynArrTypes[t];
}

dynArrIR getDynArrIRByType(Type* t){ // assumes that this type already exists
  for(auto &i:dynArrTypes){
    if(i.second.type==t)return i.second;
  }
}

Value* dynArrGet(Value* darr,Value* idx){
  dynArrIR dair=getDynArrIRByType(darr->getType());
  Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),dair.type);//builder->CreateAlloca(dair.type);
  builder->CreateStore(darr,alloca);
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
  Value* dataP=builder->CreateLoad(PointerType::getUnqual(dair.subType),builder->CreateGEP(dair.type,alloca,idcs),"dynArrGet_dataP");
  Value* idcs1[]={idx};
  Value* ptr2ret=builder->CreateGEP(dair.subType,dataP,idcs1,"dynArrGet_ptr2res");
  return builder->CreateLoad(dair.subType,ptr2ret,"dynArrGet_res");
}

Value* dynArrLen(Value* darr){
  dynArrIR dair=getDynArrIRByType(darr->getType());
  Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),dair.type);//builder->CreateAlloca(dair.type);
  builder->CreateStore(darr,alloca);
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),1)};
  return builder->CreateLoad(Type::getInt64Ty(*ctx),builder->CreateGEP(dair.type,alloca,idcs),"dynArrLen_len");
}

void dynArrSet(Value* darr,Value* idx,Value* data){
  dynArrIR dair=getDynArrIRByType(darr->getType());
  Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),dair.type);//builder->CreateAlloca(dair.type);
  builder->CreateStore(darr,alloca);
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
  Value* idcs1[]={idx};
  Value* ptr2Dest=builder->CreateGEP(dair.subType,builder->CreateLoad(PointerType::getUnqual(dair.subType),builder->CreateGEP(dair.type,alloca,idcs,"dynArrSet_dataPP"),"dynArrSet_dataP"),idcs1,"dynArrSet_ptr2Dest");
  builder->CreateStore(data,ptr2Dest);
}

BasicBlock* mainBB;
Function* actFn;
bool outOfMainFn=false;

struct varInfo{
  string type;
  Value* val;
};

vector<map<string,varInfo>> vars;
vector<map<string,varInfo>> varsMem;
map<string,BasicBlock*> lbls;
map<string,BasicBlock*> lblsMem;
map<string,Function*> fns;

varInfo getVarInfo(string name){
  for(auto &s:vars)if(s.count(name))return s[name];
  return varInfo{"",nullptr};
}

void printVars(){
  for(auto i:vars){for(auto j:i)cout << j.first<<",";cout << ";";}cout<<endl;
}

void initModule(){
  InitializeNativeTarget();
  InitializeNativeTargetAsmPrinter();
  InitializeNativeTargetAsmParser();
  ctx=make_unique<LLVMContext>();
  mdl=std::make_unique<Module>("main",*ctx);
  fpm=make_unique<legacy::FunctionPassManager>(mdl.get());
  fpm->add(createInstructionCombiningPass());
  fpm->add(createReassociatePass());
  fpm->add(createGVNPass());
  fpm->add(createCFGSimplificationPass());
  fpm->doInitialization();
  builder=make_unique<IRBuilder<>>(*ctx);
}

string getSubTypeSFromTypeS(string ts){
  unsigned idx=3;
  for(;ts.at(idx)!='(';idx++);
  idx++;
  return ts.substr(idx,ts.length()-idx-1);
}

string getTypeS(Type* t){
  if(t->isIntegerTy()){
    return "i"+to_string(t->getIntegerBitWidth());
  }if(t->isFloatTy()){
    return "f32";
  }if(t->isDoubleTy()){
    return "f64";
  }if(t->isPointerTy()){
    return "ptr("+getTypeS(static_cast<PointerType*>(t)->getPointerElementType())+")";
  }if(t->isArrayTy()){
    auto at=static_cast<ArrayType*>(t);
    return "arr!"+to_string(at->getNumElements())+"("+getTypeS(at->getElementType())+")";
  }if(t->isStructTy()){
    auto st=static_cast<StructType*>(t);
    if(st->getElementType(st->getNumElements()-1)->isIntegerTy(1)){
      return "darr("+getTypeS(st->getElementType(0)->getPointerElementType())+")";
    }
    string ret="coll{";
    for(unsigned i=0;i<st->getNumElements()-1;i++){ // num elements -1 because last entry of coll is i8
      ret+=getTypeS(st->getElementType(i))+",";
    }
    ret+="}";return ret;
  }
}

Type* getType(string ts){
  if(ts=="isize"||ts=="usize"){return Type::getInt64Ty(*ctx);} // TODO: actually make size types useful
  if(ts.at(0)=='i'||ts.at(0)=='u')return Type::getIntNTy(*ctx,stoi(ts.substr(1))); // also differentiate i-types and u-types
  if(ts=="f32")return Type::getFloatTy(*ctx);
  if(ts=="f64")return Type::getDoubleTy(*ctx);
  if(ts.substr(0,3)=="ptr"){
    return PointerType::getUnqual(getType(ts.substr(4,ts.length()-5)));
  }
  if(ts.substr(0,3)=="arr"){
    string lenS=subStrTo(ts,'(',4);
    unsigned len=stoi(lenS);
    return ArrayType::get(getType(ts.substr(5+lenS.length(),ts.length()-6-lenS.length())),len);
  }
  if(ts.substr(0,4)=="coll"){
    vector<Type*> subtypes;
    unsigned p=5,lastEnd=4;
    while(ts.at(p)!='}'){
      // get the next typeString - note that subcolls are a problem we need to deal with
      unsigned lvl=0;
      char a=ts.at(p);
      while(lvl>0||a!=','){
        if(a=='{')lvl++;
        else if(a=='}')lvl--;
        a=ts.at(++p);
      }
      subtypes.push_back(getType(ts.substr(lastEnd+1,p-lastEnd-1)));
      lastEnd=p++;
    }
    subtypes.push_back(Type::getInt8Ty(*ctx));
    return StructType::get(*ctx,subtypes);
  }
  if(ts.substr(0,4)=="darr"){
    return getDynArrIR(ts).type;
  }
  error("unknown type "+ts);
  return nullptr;
}

Value* getNull(string ts){
  Type* t=getType(ts);
  if(t->isIntegerTy())return ConstantInt::get(t,0);
  if(t->isFloatingPointTy())return ConstantFP::get(t,0);
  if(t->isPointerTy())return ConstantPointerNull::get(static_cast<PointerType*>(t));
  if(t->isArrayTy()){
    ArrayType* at=static_cast<ArrayType*>(t);
    uint64_t n=at->getNumElements();
    if(ts.find("darr")==string::npos)return ConstantAggregateZero::get(t);
    Value* arr=createEntryAlloca(builder->GetInsertBlock()->getParent(),t,"newArrP");
    unsigned p=0;for(;ts.at(p)!='(';p++);p++;
    string sts=ts.substr(p,ts.length()-p-1);
    for(unsigned i=0;i<n;i++){
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt64Ty(*ctx),i)};
      builder->CreateStore(getNull(sts),builder->CreateGEP(t,arr,idcs));
    }
    return builder->CreateLoad(t,arr,"newArr");
  }
  if(t->isStructTy()){
    if(ts.find("darr")==string::npos)return ConstantAggregateZero::get(t);
    if(ts.substr(0,4)=="darr"){
      Value* args[]={createEntryAlloca(builder->GetInsertBlock()->getParent(),getDynArrIR(ts).type,"newDarr"),ConstantInt::get(Type::getInt64Ty(*ctx),2)};
      return builder->CreateCall(getDynArrIR(ts).create,args,"initNewDarr");
    }
    Value* coll=createEntryAlloca(builder->GetInsertBlock()->getParent(),t,"newCollP");
    unsigned p=5,lastEnd=4,i=0;
    while(ts.at(p)!='}'){
      unsigned lvl=0;
      char a=ts.at(p);
      while(lvl>0||a!=','){
        if(a=='{')lvl++;
        else if(a=='}')lvl--;
        a=ts.at(++p);
      }
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),i)};
      builder->CreateStore(getNull(ts.substr(lastEnd+1,p-lastEnd-1)),builder->CreateGEP(t,coll,idcs));
      lastEnd=p++;
      i++;
    }
    return builder->CreateLoad(t,coll,"newColl");
  }
  error("Unknown type when trying to get null value");
  return nullptr;
}

Value* getLitVal(string ts,string ls){
  Type* t=getType(ts);
  if(ts.substr(0,4)=="darr"){
    Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),t,"newDynArrP");
    Value* args[]={alloca,ConstantInt::get(Type::getInt64Ty(*ctx),2)};
    builder->CreateCall(getDynArrIR(ts).create,args);
    return builder->CreateLoad(t,alloca,"newDynArr");
  }
  if(t->isIntegerTy())return ConstantInt::get(t,stoi(ls),ts.at(0)=='i');
  if(t->isFloatingPointTy())return ConstantFP::get(t,stod(ls));
  if(t->isPointerTy()||t->isArrayTy())return getNull(ts);
  if(t->isStructTy()){
    Value* empty=createEntryAlloca(builder->GetInsertBlock()->getParent(),t,"tmpStructP");
    vector<Value*> vals;
    unsigned start=0;
    while(start<ls.length()){
      unsigned end=start,lvl=0;
      char c=ls.at(end);
      while(lvl!=0||c!=','){
        if(c=='{'||c=='[')lvl++;
        if(c=='}'||c==']')lvl--;
        c=ls.at(++end);
      }
      vals.push_back(getSomethingValue(ls.substr(start,end-start)));
      start=end+1;
    }
    for(unsigned i=0;i<vals.size();i++){
      Value* idcs[]={ConstantInt::get(IntegerType::get(*ctx,64),0),ConstantInt::get(IntegerType::get(*ctx,32),i)};
      Value* field=builder->CreateGEP(t,empty,idcs,"field");
      builder->CreateStore(vals.at(i),field);
    }
    Value* filled=builder->CreateLoad(t,empty,"tmpStruct");
    return filled;
  }
  error("Unknown type when trying to parse literal");
  return nullptr;
}

Value* getSomethingValue(string s){ // only for literals and existing vars; assumes that s is non-empty
  switch(s.at(0)){
  case 'v':{
    return getVarVal(s);
  }case 'l':{
    string ts=subStrTo(s,'[',1);
    if(ts.empty())error("type missing in literal");
    unsigned start=ts.length()+2,end=start,lvl=0;
    char c=s.at(end);
    while(c!=']'||lvl!=0){
      switch(c){case '[':lvl++;break;case ']':lvl--;break;default:;}
      c=s.at(++end);
    }
    string ls=s.substr(start,end-start);
    return getLitVal(ts,ls);
  }default:
    error("something is neither variable nor literal");
    return nullptr;
  }
}

string getSomethingTypeStr(string s){
  switch(s.at(0)){
  case 'v':{
    varInfo vi=getVarInfo(s);
    if(!vi.val)error("somethings variable could not be resolved");
    return vi.type;
  }case 'l':{
    return subStrTo(s,'[',1);
  }default:
    error("something is neither variable nor literal");
    return nullptr;
  }
}

Value* getVarVal(string v){
  varInfo vi=getVarInfo(v);
  if(vi.val){
    Value* val=builder->CreateLoad(getType(vi.type),vi.val,v+"Val");
    return val;
  }else{
    error("variable "+v+" not initialized when trying to get its value");
    return nullptr;
  }
}

Value* getVarRef(string v,string ts,bool createGlobal=false){ // tries to resolve v and on failure creates it
                                                              // asserts that the value in v is no longer needed, i.e. it destroys any darr in it
  varInfo vi=getVarInfo(v);
  if(vi.val){
    return vi.val;
  }else{
    Type* t=getType(ts);
    Function* fp=builder->GetInsertBlock()->getParent();
    IRBuilder<> tmp(&fp->getEntryBlock(),fp->getEntryBlock().begin());
    Value* alloca=createGlobal?
      new GlobalVariable(*mdl,t,false,GlobalValue::CommonLinkage,Constant::getNullValue(t),v)
    : createEntryAlloca(tmp.GetInsertBlock()->getParent(),t,v);
    if(ts.at(0)=='d'){
      Value* args[]={alloca,ConstantInt::get(Type::getInt64Ty(*ctx),2)};
      builder->CreateCall(getDynArrIR(ts).create,args);
    }
    (createGlobal?vars[0]:vars.back())[v]=varInfo{ts,alloca};
    return alloca;
  }
}

void parseStr(string a){
  string fs=subStrTo(a,' ');
  if(fs.empty())error("source missing in str");
  string ts=subStrTo(a,' ',fs.length()+1);
  if(ts.empty())error("destination missing in str");
  if(ts.at(0)!='v')error("destination is no variable in str");
  Value* fsv=getSomethingValue(fs);
  Value* tvv=getVarRef(ts,getSomethingTypeStr(fs));
  if(getVarInfo(ts).type.at(0)=='d'){
    Type* t=fsv->getType();
    Value* alloca=createEntryAlloca(actFn,t,"str_darr_alloca");
    builder->CreateStore(fsv,alloca);
    Value* args[]={tvv,alloca};
    builder->CreateCall(getDynArrIRByType(t).copy,args);
    return;
  }
  StoreInst* si=builder->CreateStore(fsv,tvv);
}

void initPrintfFn(){
  prtUsed=true;
  Type* i[]={Type::getInt8PtrTy(*ctx)};
  printfFn=Function::Create(FunctionType::get(Type::getInt32Ty(*ctx),i,true),Function::ExternalLinkage,"printf",mdl.get());
}

/*// from https://stackoverflow.com/questions/22239801/how-to-load-llvm-bitcode-file-from-an-ifstream
unique_ptr<Module> loadModule(ifstream &stream,LLVMContext &context)
{
  if(!stream)
  {
    cerr << "error after open stream" << endl;
    return 0;
  }
  // load bitcode
  string ir((istreambuf_iterator<char>(stream)),(istreambuf_iterator<char>()));
  // parse it
  SMDiagnostic error;
  unique_ptr<Module> module=parseIR(MemoryBuffer::getMemBuffer(StringRef(ir)),error,context);
  if(!module)
  {
    string what;
    raw_string_ostream os(what);
    error.print("error after ParseIR()",os);
    cerr << what;
  }
  return module;
}*/

void initInpFns(){
  inpUsed=true;
  SMDiagnostic error;
  unique_ptr<Module> inputMdl=parseIR(MemoryBufferRef(StringRef(INPUTLLSTR),StringRef("input.c")),error,*ctx);
  GlobalVariable* exstdin=static_cast<GlobalVariable*>(inputMdl->getNamedValue("stdin"));
  GlobalVariable* instdinP=new GlobalVariable(*mdl,exstdin->getValueType(),exstdin->isConstant(),exstdin->getLinkage(),nullptr,exstdin->getName(),nullptr,exstdin->getThreadLocalMode(),exstdin->getType()->getAddressSpace());
  instdinP->copyAttributesFrom(exstdin);
  Type* filePtrType=static_cast<PointerType*>(exstdin->getType())->getPointerElementType();
  Type* i0[]={filePtrType};
  Function* pureGetcFn=Function::Create(FunctionType::get(Type::getInt32Ty(*ctx),i0,false),Function::ExternalLinkage,"getc",mdl.get());
  getcFn=Function::Create(FunctionType::get(Type::getInt32Ty(*ctx),vector<Type*>(),false),Function::ExternalLinkage,"getcWrapper",mdl.get());
  unique_ptr<IRBuilder<>> tmp=make_unique<IRBuilder<>>(*ctx);
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",getcFn);
  tmp->SetInsertPoint(bb);
  Value* instdin=tmp->CreateLoad(filePtrType,instdinP);
  Value* args[]={instdin};
  Value* ret=tmp->CreateCall(pureGetcFn,args);
  tmp->CreateRet(ret);
  verifyFunction(*getcFn);
  fpm->run(*getcFn);
  
  Type* i[]={Type::getInt8PtrTy(*ctx),PointerType::getUnqual(Type::getInt8PtrTy(*ctx)),Type::getInt32Ty(*ctx)};
  strtolFn=Function::Create(FunctionType::get(Type::getInt64Ty(*ctx),i,false),Function::ExternalLinkage,"strtol",mdl.get());
  Type* i1[]={Type::getInt8PtrTy(*ctx),PointerType::getUnqual(Type::getInt8PtrTy(*ctx))};
  strtodFn=Function::Create(FunctionType::get(Type::getDoubleTy(*ctx),i1,false),Function::ExternalLinkage,"strtod",mdl.get());
}

Value* getLine(){
  if(!inpUsed)initInpFns();
  dynArrIR dair=getDynArrIR("darr(i8)");
  Value* lineP=createEntryAlloca(actFn,dair.type,"input_lineP");
  Value* args[]={lineP,ConstantInt::get(Type::getInt64Ty(*ctx),2)};
  builder->CreateCall(dair.create,args);
  BasicBlock* loopStart=BasicBlock::Create(*ctx,"input_loopStart",actFn);
  BasicBlock* loopCont=BasicBlock::Create(*ctx,"input_loopCont");
  BasicBlock* loopEnd=BasicBlock::Create(*ctx,"input_loopEnd");
  builder->CreateBr(loopStart);
  builder->SetInsertPoint(loopStart);
  Value* c=builder->CreateCall(getcFn,vector<Value*>());
  Value* cisnl=builder->CreateICmpEQ(c,ConstantInt::get(Type::getInt32Ty(*ctx),'\n'),"input_charIsNewline");
  builder->CreateCondBr(cisnl,loopEnd,loopCont);
  actFn->insert(actFn->end(),loopCont);
  builder->SetInsertPoint(loopCont);
  Value* args1[]={lineP,builder->CreateTrunc(c,Type::getInt8Ty(*ctx))};
  builder->CreateCall(dair.append,args1);
  builder->CreateBr(loopStart);
  actFn->insert(actFn->end(),loopEnd);
  builder->SetInsertPoint(loopEnd);
  return builder->CreateLoad(dair.type,lineP);
}

void createPrintf(string fmts,vector<Value*> va){
  Value* fmtsv=ConstantDataArray::getString(*ctx,fmts);
  Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),fmtsv->getType(),"fmts");
  builder->CreateStore(fmtsv,alloca);
  Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt64Ty(*ctx),0)};
  Value* fmtsi8pv=builder->CreateGEP(fmtsv->getType(),alloca,idcs,"fmtsi8p");
  vector<Value*> a;
  a.push_back(fmtsi8pv);
  a.insert(a.end(),va.begin(),va.end());
  builder->CreateCall(printfFn,a,"prtCall");
}

void parseSubPrt(Value* sv){
  Type* st=sv->getType();
  vector<Value*> va;
  if(st->isIntegerTy()){ // TODO: differentiate between signed and unsigned (%d gives negative numbers for unsigned values that are too large)
    va.push_back(builder->CreateSExtOrTrunc(sv,Type::getInt64Ty(*ctx)));
    createPrintf("%lld",va);
  }else if(st->isFloatingPointTy()){
    va.push_back(sv->getType()->isFloatTy()?builder->CreateFPExt(sv,Type::getDoubleTy(*ctx)):sv);
    createPrintf("%f",va);
  }else if(st->isPointerTy()){
    va.push_back(sv);
    createPrintf("%p",va);
  }else if(st->isArrayTy()){
    ArrayType* sat=static_cast<ArrayType*>(st);
    Value* ne=ConstantInt::get(Type::getInt64Ty(*ctx),sat->getNumElements());
    Type* t=sat->getElementType();
    Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),st,"prtArrAlloca");
    builder->CreateStore(sv,alloca);
    createPrintf("[",vector<Value*>());
    BasicBlock* preBB=builder->GetInsertBlock();
    Function* f=preBB->getParent();
    BasicBlock* condBB=BasicBlock::Create(*ctx,"prtArrCheck",f);
    builder->CreateBr(condBB);
    builder->SetInsertPoint(condBB);
    PHINode* i=builder->CreatePHI(Type::getInt64Ty(*ctx),2,"prtArrRunning");
    i->addIncoming(ConstantInt::get(Type::getInt64Ty(*ctx),0),preBB);
    Value* checkPassed=builder->CreateICmpULT(i,ne,"prtArrCheckPassed");
    BasicBlock* bodyBB=BasicBlock::Create(*ctx,"prtArrBody",f);
    BasicBlock* contBB=BasicBlock::Create(*ctx,"prtArrCont");
    builder->CreateCondBr(checkPassed,bodyBB,contBB);
    builder->SetInsertPoint(bodyBB);
    Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),i};
    Value* ptr2actEl=builder->CreateGEP(st,alloca,idcs,"prtArrGEP2actEl");
    Value* actEl=builder->CreateLoad(sat->getElementType(),ptr2actEl,"prtArrActEl");
    parseSubPrt(actEl);
    bodyBB=builder->GetInsertBlock();
    Value* nexti=builder->CreateAdd(i,ConstantInt::get(Type::getInt64Ty(*ctx),1),"prtArrRunningNext");
    createPrintf(",",vector<Value*>());
    builder->CreateBr(condBB);
    f->insert(f->end(),contBB);
    builder->SetInsertPoint(contBB);
    i->addIncoming(nexti,bodyBB);
    createPrintf("]",vector<Value*>());
  }else if(st->isStructTy()){
    StructType* sst=static_cast<StructType*>(st);
    unsigned ne=sst->getNumElements();
    if(sst->getElementType(ne-1)->isIntegerTy(1)){
      Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),st,"prtDarrAlloca");
      builder->CreateStore(sv,alloca);
      createPrintf("[",vector<Value*>());
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
      Value* darrDataP=builder->CreateLoad(sst->getElementType(0),builder->CreateGEP(st,alloca,idcs),"prtDarr_dataP");
      idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
      Value* ne=builder->CreateLoad(Type::getInt64Ty(*ctx),builder->CreateGEP(st,alloca,idcs),"prtDarr_len");
      BasicBlock* preBB=builder->GetInsertBlock();
      Function* f=preBB->getParent();
      BasicBlock* condBB=BasicBlock::Create(*ctx,"prtDarrCheck",f);
      builder->CreateBr(condBB);
      builder->SetInsertPoint(condBB);
      PHINode* i=builder->CreatePHI(Type::getInt64Ty(*ctx),2,"prtDarrRunning");
      i->addIncoming(ConstantInt::get(Type::getInt64Ty(*ctx),0),preBB);
      Value* checkPassed=builder->CreateICmpULT(i,ne,"prtDarrCheckPassed");
      BasicBlock* bodyBB=BasicBlock::Create(*ctx,"prtDarrBody",f);
      BasicBlock* contBB=BasicBlock::Create(*ctx,"prtDarrCont");
      builder->CreateCondBr(checkPassed,bodyBB,contBB);
      builder->SetInsertPoint(bodyBB);
      Value* idcs1[]={i};
      Type* subType=static_cast<PointerType*>(sst->getElementType(0))->getPointerElementType();
      Value* ptr2actEl=builder->CreateGEP(subType,darrDataP,idcs1,"prtDarrGEP2actEl");
      Value* actEl=builder->CreateLoad(subType,ptr2actEl,"prtDarrActEl");
      parseSubPrt(actEl);
      bodyBB=builder->GetInsertBlock();
      Value* nexti=builder->CreateAdd(i,ConstantInt::get(Type::getInt64Ty(*ctx),1),"prtDarrRunningNext");
      createPrintf(",",vector<Value*>());
      builder->CreateBr(condBB);
      f->insert(f->end(),contBB);
      builder->SetInsertPoint(contBB);
      i->addIncoming(nexti,bodyBB);
      createPrintf("]",vector<Value*>());
    }else{
      createPrintf("{",vector<Value*>());
      Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),st,"prtCollAlloca");
      builder->CreateStore(sv,alloca);
      for(unsigned i=0;i<ne-1;i++){
        Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),i)};
        Value* actElPtr=builder->CreateGEP(st,alloca,idcs,"prtCollGEP2actEl");
        Value* actEl=builder->CreateLoad(sst->getElementType(i),actElPtr,"prtCollActEl");
        parseSubPrt(actEl);
        createPrintf(",",vector<Value*>());
      }
      createPrintf("}",vector<Value*>());
    }
  }
}

void parsePrt(string s){
  if(!prtUsed)initPrintfFn();
  Value* sv=getSomethingValue(s);
  parseSubPrt(sv);
}

void parseSubPrtS(Value* sv){
  Type* st=sv->getType();
  vector<Value*> va;
  if(st->isIntegerTy()){
    va.push_back(sv);
    createPrintf("%c",va);
  }else if(st->isFloatingPointTy()){
    va.push_back(builder->CreateFPToSI(sv,Type::getInt64Ty(*ctx)));
    createPrintf("%c",va);
  }else if(st->isPointerTy()){
    va.push_back(builder->CreateBitCast(sv,Type::getInt8PtrTy(*ctx)));
    builder->CreateCall(printfFn,va,"prtCall");
  }else if(st->isArrayTy()){
    ArrayType* sat=static_cast<ArrayType*>(st);
    Value* ne=ConstantInt::get(Type::getInt64Ty(*ctx),sat->getNumElements());
    Type* t=sat->getElementType();
    Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),st,"prtSArrAlloca");
    builder->CreateStore(sv,alloca);
    BasicBlock* preBB=builder->GetInsertBlock();
    Function* f=preBB->getParent();
    BasicBlock* condBB=BasicBlock::Create(*ctx,"prtSArrCheck",f);
    builder->CreateBr(condBB);
    builder->SetInsertPoint(condBB);
    PHINode* i=builder->CreatePHI(Type::getInt64Ty(*ctx),2,"prtSArrRunning");
    i->addIncoming(ConstantInt::get(Type::getInt64Ty(*ctx),0),preBB);
    Value* checkPassed=builder->CreateICmpULT(i,ne,"prtSArrCheckPassed");
    BasicBlock* bodyBB=BasicBlock::Create(*ctx,"prtSArrBody",f);
    BasicBlock* contBB=BasicBlock::Create(*ctx,"prtSArrCont");
    builder->CreateCondBr(checkPassed,bodyBB,contBB);
    builder->SetInsertPoint(bodyBB);
    Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),i};
    Value* ptr2actEl=builder->CreateGEP(st,alloca,idcs,"prtSArrGEP2actEl");
    Value* actEl=builder->CreateLoad(sat->getElementType(),ptr2actEl,"prtSArrActEl");
    parseSubPrtS(actEl);
    bodyBB=builder->GetInsertBlock();
    Value* nexti=builder->CreateAdd(i,ConstantInt::get(Type::getInt64Ty(*ctx),1),"prtSArrRunningNext");
    builder->CreateBr(condBB);
    f->insert(f->end(),contBB);
    builder->SetInsertPoint(contBB);
    i->addIncoming(nexti,bodyBB);
  }else if(st->isStructTy()){
    StructType* sst=static_cast<StructType*>(st);
    unsigned ne=sst->getNumElements();
    if(sst->getElementType(ne-1)->isIntegerTy(1)){
      Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),st,"prtSDarrAlloca");
      builder->CreateStore(sv,alloca);
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
      Value* darrDataP=builder->CreateLoad(sst->getElementType(0),builder->CreateGEP(st,alloca,idcs),"prtSDarr_dataP");
      idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
      Value* ne=builder->CreateLoad(Type::getInt64Ty(*ctx),builder->CreateGEP(st,alloca,idcs),"prtSDarr_len");
      BasicBlock* preBB=builder->GetInsertBlock();
      Function* f=preBB->getParent();
      BasicBlock* condBB=BasicBlock::Create(*ctx,"prtSDarrCheck",f);
      builder->CreateBr(condBB);
      builder->SetInsertPoint(condBB);
      PHINode* i=builder->CreatePHI(Type::getInt64Ty(*ctx),2,"prtSDarrRunning");
      i->addIncoming(ConstantInt::get(Type::getInt64Ty(*ctx),0),preBB);
      Value* checkPassed=builder->CreateICmpULT(i,ne,"prtSDarrCheckPassed");
      BasicBlock* bodyBB=BasicBlock::Create(*ctx,"prtSDarrBody",f);
      BasicBlock* contBB=BasicBlock::Create(*ctx,"prtSDarrCont");
      builder->CreateCondBr(checkPassed,bodyBB,contBB);
      builder->SetInsertPoint(bodyBB);
      Value* idcs1[]={i};
      Type* subType=static_cast<PointerType*>(sst->getElementType(0))->getPointerElementType();
      Value* ptr2actEl=builder->CreateGEP(subType,darrDataP,idcs1,"prtSDarrGEP2actEl");
      Value* actEl=builder->CreateLoad(subType,ptr2actEl,"prtSDarrActEl");
      parseSubPrtS(actEl);
      bodyBB=builder->GetInsertBlock();
      Value* nexti=builder->CreateAdd(i,ConstantInt::get(Type::getInt64Ty(*ctx),1),"prtSDarrRunningNext");
      builder->CreateBr(condBB);
      f->insert(f->end(),contBB);
      builder->SetInsertPoint(contBB);
      i->addIncoming(nexti,bodyBB);
    }else{
      Value* alloca=createEntryAlloca(builder->GetInsertBlock()->getParent(),st,"prtSCollAlloca");
      builder->CreateStore(sv,alloca);
      for(unsigned i=0;i<ne;i++){
        Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),i)};
        Value* actElPtr=builder->CreateGEP(st,alloca,idcs,"prtSCollGEP2actEl");
        Value* actEl=builder->CreateLoad(sst->getElementType(i),actElPtr,"prtSCollActEl");
        parseSubPrtS(actEl);
      }
    }
  }
}

void parsePrtS(string s){
  if(!prtUsed)initPrintfFn();
  Value* sv=getSomethingValue(s);
  parseSubPrtS(sv);
}

void parseStrGlob(string a){
  string fs=subStrTo(a,' ');
  if(fs.empty())error("source missing in strGlob");
  string ts=subStrTo(a,' ',fs.length()+1);
  if(ts.empty())error("destination missing in strGlob");
  if(ts.at(0)!='v')error("destination is no variable in strGlob");
  Value* fsv=getSomethingValue(fs);
  Value* tvv=getVarRef(ts,getSomethingTypeStr(fs),true);
  if(getVarInfo(ts).type.at(0)=='d'){
    Type* t=fsv->getType();
    Value* alloca=createEntryAlloca(actFn,t,"strGlob_darr_alloca");
    builder->CreateStore(fsv,alloca);
    Value* args[]={tvv,alloca};
    builder->CreateCall(getDynArrIRByType(t).copy,args);
    return;
  }
  StoreInst* si=builder->CreateStore(fsv,tvv);
}

void parseSubCast(Value* fsv,Type* tt,Value* dv){
  Type* ft=fsv->getType();
  Value* casted=nullptr;
  if(ft->isIntegerTy()){
    if(tt->isIntegerTy()){
      casted=builder->CreateSExtOrTrunc(fsv,tt,"cast");
    }else if(tt->isFloatingPointTy()){
      casted=builder->CreateSIToFP(fsv,tt,"cast");
    }else if(tt->isPointerTy()){
      casted=builder->CreateIntToPtr(fsv,tt,"cast");
    }
  }else if(ft->isFloatingPointTy()){
    if(tt->isIntegerTy()){
      casted=builder->CreateFPToSI(fsv,tt,"cast");
    }else if(tt->isFloatingPointTy()){
      casted=builder->CreateFPCast(fsv,tt,"cast");
    }
  }else if(ft->isPointerTy()){
    auto fpt=static_cast<PointerType*>(ft);
    if(tt->isPointerTy()){
      casted=builder->CreateBitCast(fsv,tt,"cast");
    }else if(tt->isIntegerTy()){
      casted=builder->CreatePtrToInt(fsv,tt,"cast");
    }else if(tt->isArrayTy()){
      auto tat=static_cast<ArrayType*>(tt);
      Type* fsubt=fpt->getPointerElementType();
      if(fsubt!=tat->getElementType())error("subtypes do not match when casting pointer to array");
      Value* pointee=builder->CreateLoad(fsubt,fsv,"castPtr2ArrPointee");
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt64Ty(*ctx),0)};
      builder->CreateStore(pointee,builder->CreateGEP(tt,dv,idcs));
      return;
    }else if(tt->isStructTy()){
      auto tst=static_cast<StructType*>(tt);
      if(tst->getElementType(tst->getNumElements()-1)->isIntegerTy(1)){
        auto dair=getDynArrIRByType(tt);
        Value* args[]={dv,ConstantInt::get(Type::getInt64Ty(*ctx),1)};
        builder->CreateCall(dair.resize,args);
        Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
        Value* ddataP=builder->CreateLoad(PointerType::getUnqual(dair.subType),builder->CreateGEP(tt,dv,idcs,"castPtr2Darr_ddataPP"),"castPtr2Darr_ddataP");
        Value* pointee=builder->CreateLoad(fpt->getPointerElementType(),fsv,"castPtr2DarrPointee");
        builder->CreateStore(pointee,ddataP);
        idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
        Value* lenP=builder->CreateGEP(tt,dv,idcs,"castPtr2Darr_dlenP");
        builder->CreateStore(ConstantInt::get(Type::getInt64Ty(*ctx),1),lenP);
        return;
      }
    }
  }else if(ft->isArrayTy()){
    Value* fsvCopyP=createEntryAlloca(builder->GetInsertBlock()->getParent(),ft,"castArr_fvCopy");
    builder->CreateStore(fsv,fsvCopyP);
    auto fat=static_cast<ArrayType*>(ft);
    if(tt->isArrayTy()){
      auto tat=static_cast<ArrayType*>(tt);
      unsigned fne=fat->getNumElements(),tne=tat->getNumElements(),ne=tne<fne?tne:fne;
      BasicBlock* preBB=builder->GetInsertBlock();
      Function* f=preBB->getParent();
      BasicBlock* condBB=BasicBlock::Create(*ctx,"castArr2Arr_cond",f);
      builder->CreateBr(condBB);
      builder->SetInsertPoint(condBB);
      PHINode* i=builder->CreatePHI(Type::getInt64Ty(*ctx),2,"castArr2Arr_i");
      i->addIncoming(ConstantInt::get(Type::getInt64Ty(*ctx),0),preBB);
      Value* checkPassed=builder->CreateICmpULT(i,ConstantInt::get(Type::getInt64Ty(*ctx),ne),"castArr2Arr_checkPassed");
      BasicBlock* bodyBB=BasicBlock::Create(*ctx,"castArr2Arr_body",f);
      BasicBlock* contBB=BasicBlock::Create(*ctx,"castArr2Arr_after");
      builder->CreateCondBr(checkPassed,bodyBB,contBB);
      builder->SetInsertPoint(bodyBB);
      Type* fst=fat->getElementType();Type* tst=tat->getElementType();
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),i};
      Value* ptr2actFEl=builder->CreateGEP(fat,fsvCopyP,idcs,"castArr2Arr_ptr2actFEl");
      Value* ptr2actDEl=builder->CreateGEP(tat,dv,idcs,"castArr2Arr_ptr2actDEl");
      Value* actFEl=builder->CreateLoad(fst,ptr2actFEl,"castArr2Arr_actFEl");
      parseSubCast(actFEl,tst,ptr2actDEl);
      bodyBB=builder->GetInsertBlock();
      Value* nexti=builder->CreateAdd(i,ConstantInt::get(Type::getInt64Ty(*ctx),1),"castArr2Arr_nextI");
      builder->CreateBr(condBB);
      f->insert(f->end(),contBB);
      builder->SetInsertPoint(contBB);
      i->addIncoming(nexti,bodyBB);
      return;
    }else if(tt->isStructTy()){
      auto tst=static_cast<StructType*>(tt);
      if(tst->getElementType(tst->getNumElements()-1)->isIntegerTy(1)){
        dynArrIR dair=getDynArrIRByType(tt);
        unsigned ne=fat->getNumElements();
        if(ne>0){
          Value* args[]={dv,ConstantInt::get(Type::getInt64Ty(*ctx),ne)};
          builder->CreateCall(dair.resize,args);
        }
        BasicBlock* preBB=builder->GetInsertBlock();
        Function* f=preBB->getParent();
        BasicBlock* condBB=BasicBlock::Create(*ctx,"castArr2Darr_cond",f);
        builder->CreateBr(condBB);
        builder->SetInsertPoint(condBB);
        PHINode* i=builder->CreatePHI(Type::getInt64Ty(*ctx),2,"castArr2Darr_i");
        i->addIncoming(ConstantInt::get(Type::getInt64Ty(*ctx),0),preBB);
        Value* checkPassed=builder->CreateICmpULT(i,ConstantInt::get(Type::getInt64Ty(*ctx),ne),"castArr2Darr_checkPassed");
        BasicBlock* bodyBB=BasicBlock::Create(*ctx,"castArr2Darr_body",f);
        BasicBlock* contBB=BasicBlock::Create(*ctx,"castArr2Darr_after");
        builder->CreateCondBr(checkPassed,bodyBB,contBB);
        builder->SetInsertPoint(bodyBB);
        Type* fsubt=fat->getElementType();
        Type* tsubt=dair.subType;
        Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),i};
        Value* ptr2actFEl=builder->CreateGEP(fat,fsvCopyP,idcs,"castArr2Darr_ptr2actFEl");
        Value* idcs1[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
        Value* ddataP=builder->CreateLoad(PointerType::getUnqual(tsubt),builder->CreateGEP(tt,dv,idcs1,"castArr2Darr_ddataPP"),"castArr2Darr_ddataP");
        Value* idcs2[]={i};
        Value* ptr2actDEl=builder->CreateGEP(tsubt,ddataP,idcs2,"castArr2Darr_ptr2actDEl");
        Value* actFEl=builder->CreateLoad(fsubt,ptr2actFEl,"castArr2Darr_actFEl");
        parseSubCast(actFEl,tsubt,ptr2actDEl);
        bodyBB=builder->GetInsertBlock();
        Value* nexti=builder->CreateAdd(i,ConstantInt::get(Type::getInt64Ty(*ctx),1),"castArr2Darr_nextI");
        builder->CreateBr(condBB);
        f->insert(f->end(),contBB);
        builder->SetInsertPoint(contBB);
        i->addIncoming(nexti,bodyBB);
        idcs1[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
        Value* dlenP=builder->CreateGEP(tt,dv,idcs1,"castArr2Darr_ddataPP");
        builder->CreateStore(ConstantInt::get(Type::getInt64Ty(*ctx),ne),dlenP);
        return;
      }
    }
  }else if(ft->isStructTy()){
    auto fst=static_cast<StructType*>(ft);
    if(fst->getElementType(fst->getNumElements()-1)->isIntegerTy(1)){
      Value* fsvCopyP=createEntryAlloca(builder->GetInsertBlock()->getParent(),ft,"castDarr_fvCopy");
      builder->CreateStore(fsv,fsvCopyP);
      dynArrIR fdair=getDynArrIRByType(ft);
      if(tt->isStructTy()){
        auto tst=static_cast<StructType*>(tt);
        if(tst->getElementType(tst->getNumElements()-1)->isIntegerTy(1)){
          dynArrIR tdair=getDynArrIRByType(tt);
          Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),1)};
          Value* ne=builder->CreateLoad(Type::getInt64Ty(*ctx),builder->CreateGEP(ft,fsvCopyP,idcs),"castDarr2Darr_ne");
          Value* neIs0=builder->CreateICmpEQ(ne,ConstantInt::get(Type::getInt64Ty(*ctx),0),"castDarr2Darr_neIs0");
          Function* f=builder->GetInsertBlock()->getParent();
          BasicBlock* resizeBB=BasicBlock::Create(*ctx,"castDarr2Darr_resize",f);
          BasicBlock* preBB=BasicBlock::Create(*ctx,"castDarr2Darr_afterResize");
          builder->CreateCondBr(neIs0,preBB,resizeBB);
          builder->SetInsertPoint(resizeBB);
          Value* args[]={dv,ne};
          builder->CreateCall(tdair.resize,args);
          builder->CreateBr(preBB);
          f->insert(f->end(),preBB);
          builder->SetInsertPoint(preBB);
          
          BasicBlock* condBB=BasicBlock::Create(*ctx,"castDarr2Darr_cond",f);
          builder->CreateBr(condBB);
          builder->SetInsertPoint(condBB);
          PHINode* i=builder->CreatePHI(Type::getInt64Ty(*ctx),2,"castDarr2Darr_i");
          i->addIncoming(ConstantInt::get(Type::getInt64Ty(*ctx),0),preBB);
          Value* checkPassed=builder->CreateICmpULT(i,ne,"castDarr2Darr_checkPassed");
          BasicBlock* bodyBB=BasicBlock::Create(*ctx,"castDarr2Darr_body",f);
          BasicBlock* contBB=BasicBlock::Create(*ctx,"castDarr2Darr_after");
          builder->CreateCondBr(checkPassed,bodyBB,contBB);
          builder->SetInsertPoint(bodyBB);
          Type* fsubt=fdair.subType;
          Type* tsubt=tdair.subType;
          Value* idcs1[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
          Value* fdataP=builder->CreateLoad(PointerType::getUnqual(fsubt),builder->CreateGEP(ft,fsvCopyP,idcs1,"castDarr2Darr_fdataPP"),"castDarr2Darr_fdataP");
          Value* idcs2[]={i};
          Value* ptr2actFEl=builder->CreateGEP(fsubt,fdataP,idcs2,"castDarr2Darr_ptr2actFEl");
          Value* ddataP=builder->CreateLoad(PointerType::getUnqual(tsubt),builder->CreateGEP(tt,dv,idcs1,"castDarr2Darr_ddataPP"),"castDarr2Darr_ddataP");
          Value* ptr2actDEl=builder->CreateGEP(tsubt,ddataP,idcs2,"castDarr2Darr_ptr2actDEl");
          Value* actFEl=builder->CreateLoad(fsubt,ptr2actFEl,"castDarr2Darr_actFEl");
          parseSubCast(actFEl,tsubt,ptr2actDEl);
          bodyBB=builder->GetInsertBlock();
          Value* nexti=builder->CreateAdd(i,ConstantInt::get(Type::getInt64Ty(*ctx),1),"castDarr2Darr_nextI");
          builder->CreateBr(condBB);
          f->insert(f->end(),contBB);
          builder->SetInsertPoint(contBB);
          i->addIncoming(nexti,bodyBB);
          idcs1[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
          Value* dlenP=builder->CreateGEP(tt,dv,idcs1,"castDarr2Darr_dlenP");
          builder->CreateStore(ne,dlenP);
          return;
        }
      }else if(tt->isArrayTy()){
        auto tat=static_cast<ArrayType*>(tt);
        Value* idcs0[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),1)};
        Value* fne=builder->CreateLoad(Type::getInt64Ty(*ctx),builder->CreateGEP(ft,fsvCopyP,idcs0),"castDarr2Arr_ne");
        Value* tne=ConstantInt::get(Type::getInt64Ty(*ctx),tat->getNumElements());
        Value* ne=builder->CreateSelect(builder->CreateICmpULT(fne,tne),fne,tne);
        BasicBlock* preBB=builder->GetInsertBlock();
        Function* f=preBB->getParent();
        BasicBlock* condBB=BasicBlock::Create(*ctx,"castDarr2Arr_cond",f);
        builder->CreateBr(condBB);
        builder->SetInsertPoint(condBB);
        PHINode* i=builder->CreatePHI(Type::getInt64Ty(*ctx),2,"castDarr2Arr_i");
        i->addIncoming(ConstantInt::get(Type::getInt64Ty(*ctx),0),preBB);
        Value* checkPassed=builder->CreateICmpULT(i,ne,"castDarr2Arr_checkPassed");
        BasicBlock* bodyBB=BasicBlock::Create(*ctx,"castDarr2Arr_body",f);
        BasicBlock* contBB=BasicBlock::Create(*ctx,"castDarr2Arr_after");
        builder->CreateCondBr(checkPassed,bodyBB,contBB);
        builder->SetInsertPoint(bodyBB);
        Type* fsubt=fdair.subType;
        Type* tsubt=tat->getElementType();
        Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt32Ty(*ctx),0)};
        Value* fdataP=builder->CreateLoad(PointerType::getUnqual(fsubt),builder->CreateGEP(ft,fsvCopyP,idcs,"castDarr2Arr_fdataPP"),"castDarr2Arr_fdataP");
        Value* idcs1[]={i};
        Value* ptr2actFEl=builder->CreateGEP(fsubt,fdataP,idcs1,"castDarr2Arr_ptr2actFEl");
        Value* idcs2[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),i};
        Value* ptr2actDEl=builder->CreateGEP(tt,dv,idcs2,"castDarr2Arr_ptr2actDEl");
        Value* actFEl=builder->CreateLoad(fsubt,ptr2actFEl,"castArr2Darr_actFEl");
        parseSubCast(actFEl,tsubt,ptr2actDEl);
        bodyBB=builder->GetInsertBlock();
        Value* nexti=builder->CreateAdd(i,ConstantInt::get(Type::getInt64Ty(*ctx),1),"castArr2Darr_nextI");
        builder->CreateBr(condBB);
        f->insert(f->end(),contBB);
        builder->SetInsertPoint(contBB);
        i->addIncoming(nexti,bodyBB);
        return;
      }
    }
  }
  if(casted)builder->CreateStore(casted,dv);else error("cast of two incompatible types");
}

void parseCast(string a){
  string fs=subStrTo(a,' ');
  if(fs.empty())error("source missing in cast");
  string ts=subStrTo(a,' ',fs.length()+1);
  if(ts.empty())error("type missing in cast");
  string ds=subStrTo(a,' ',fs.length()+1+ts.length()+1);
  if(ds.empty())error("destination missing in cast");
  if(ds.at(0)!='v')error("destination is no variable in cast");
  Value* fsv=getSomethingValue(fs);
  Type* tt=getType(ts);
  Value* dv=getVarRef(ds,ts);
  parseSubCast(fsv,tt,dv);
}

void endScope(){
  for(auto &i:vars.back()){
    if(i.second.type.at(0)=='d'){
      Value* args[]={i.second.val};
      builder->CreateCall(getDynArrIR(i.second.type).destroy,args);
    }
  }
  vars.pop_back();
}

void parseGetPtr(string a){
  string pointeeS=subStrTo(a,' ');
  if(pointeeS.empty())error("source missing in getPtr");
  if(pointeeS.at(0)!='v')error("source is not a variable in getPtr");
  string ds=subStrTo(a,' ',pointeeS.length()+1);
  if(ds.empty())error("destination missing in getPtr");
  if(ds.at(0)!='v')error("destination is not a variable in getPtr");
  varInfo pointeeVI=getVarInfo(pointeeS);
  Value* dv=getVarRef(ds,"ptr("+pointeeVI.type+")");
  builder->CreateStore(pointeeVI.val,dv);
}

void parseGetAt(string a){
  string fs=subStrTo(a,' ');
  if(fs.empty())error("source missing in getAt");
  string idxS=subStrTo(a,' ',fs.length()+1);
  if(idxS.empty())error("idx missing in getAt");
  string ds=subStrTo(a,' ',fs.length()+idxS.length()+2);
  if(ds.empty())error("destination missing in getAt");
  if(ds.at(0)!='v')error("destination is not a variable in getAt");
  varInfo fvi=getVarInfo(fs);
  Value* fvp=fvi.val;
  Value* fv=getVarVal(fs);
  Type* ft=getType(fvi.type);
  Value* idxV=getSomethingValue(idxS);
  Value* ret;
  string fsubts;
  if(ft->isStructTy()){
    auto fst=static_cast<StructType*>(ft);
    if(fst->getElementType(fst->getNumElements()-1)->isIntegerTy(1)){
      ret=dynArrGet(fv,builder->CreateSExtOrTrunc(idxV,Type::getInt64Ty(*ctx)));
      fsubts=getSubTypeSFromTypeS(fvi.type);
    }else{
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),builder->CreateSExtOrTrunc(idxV,Type::getInt32Ty(*ctx))};
      Value* retP=builder->CreateGEP(ft,fvp,idcs,"getAtColl_resultP");
      Type* fsubt=static_cast<PointerType*>(retP->getType())->getPointerElementType();
      fsubts=getTypeS(fsubt);
      ret=builder->CreateLoad(fsubt,retP,"getAtColl_result");
    }
  }else{
    fsubts=getSubTypeSFromTypeS(fvi.type);
    Type* fsubt=getType(fsubts);
    if(ft->isArrayTy()){
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),builder->CreateSExtOrTrunc(idxV,Type::getInt64Ty(*ctx))};
      ret=builder->CreateLoad(fsubt,builder->CreateGEP(ft,fvp,idcs),"getAtArrOrPtr_result");
    }else if(ft->isPointerTy()){
      auto fpt=static_cast<PointerType*>(ft);
      ret=builder->CreateLoad(fpt->getPointerElementType(),fv);
    }
  }
  Value* dv=getVarRef(ds,fsubts);
  builder->CreateStore(ret,dv);
}

void parseAppend(string a){
  string ds=subStrTo(a,' ');
  if(ds.empty())error("darr missing in append");
  if(ds.at(0)!='v')error("darr is not a variable in append");
  string is=subStrTo(a,' ',ds.length()+1);
  if(is.empty())error("item missing in append");
  varInfo dvi=getVarInfo(ds);
  Value* dv=dvi.val;
  Value* iv=getSomethingValue(is);
  Value* args[]={dv,iv};
  builder->CreateCall(getDynArrIR(dvi.type).append,args);
}

void parsePop(string a){
  string fs=subStrTo(a,' ');
  if(fs.empty())error("darr missing in pop");
  if(fs.at(0)!='v')error("darr is not a variable in pop");
  string idxS=subStrTo(a,' ',fs.length()+1);
  if(idxS.empty())error("idx missing in pop");
  string ds=subStrTo(a,' ',fs.length()+idxS.length()+2);
  if(ds.empty())error("dest missing in pop");
  varInfo fvi=getVarInfo(fs);
  Value* fv=fvi.val;
  Value* idxV=getSomethingValue(idxS);
  dynArrIR darrIR=getDynArrIR(fvi.type);
  Value* dv=getVarRef(ds,darrIR.subTypeS);
  Value* args[]={fv,idxV};
  Value* popped=builder->CreateCall(darrIR.pop,args);
  builder->CreateStore(popped,dv);
}

void parsePopLast(string a){
  string fs=subStrTo(a,' ');
  if(fs.empty())error("darr missing in popLast");
  if(fs.at(0)!='v')error("darr is not a variable in popLast");
  string ds=subStrTo(a,' ',fs.length()+1);
  if(ds.empty())error("dest missing in popLast");
  varInfo fvi=getVarInfo(fs);
  Value* fv=fvi.val;
  Value* idxV=builder->CreateSub(dynArrLen(builder->CreateLoad(getType(fvi.type),fv)),ConstantInt::get(Type::getInt64Ty(*ctx),1));
  dynArrIR darrIR=getDynArrIR(fvi.type);
  Value* dv=getVarRef(ds,darrIR.subTypeS);
  Value* args[]={fv,idxV};
  Value* popped=builder->CreateCall(darrIR.pop,args);
  builder->CreateStore(popped,dv);
}

void parseInsert(string a){
  string ds=subStrTo(a,' ');
  if(ds.empty())error("darr missing in insert");
  if(ds.at(0)!='v')error("darr is not a variable in insert");
  string is=subStrTo(a,' ',ds.length()+1);
  if(is.empty())error("item missing in insert");
  string idxS=subStrTo(a,' ',ds.length()+is.length()+2);
  if(idxS.empty())error("idx missing in insert");
  varInfo dvi=getVarInfo(ds);
  Value* dv=dvi.val;
  Value* iv=getSomethingValue(is);
  Value* idxV=builder->CreateSExtOrTrunc(getSomethingValue(idxS),Type::getInt64Ty(*ctx));
  Value* args[]={dv,iv,idxV};
  builder->CreateCall(getDynArrIR(dvi.type).insert,args);
}

void parseSetAt(string a){
  string fs=subStrTo(a,' ');
  if(fs.empty())error("destination missing in setAt");
  string idxS=subStrTo(a,' ',fs.length()+1);
  if(idxS.empty())error("idx missing in setAt");
  string vs=subStrTo(a,' ',fs.length()+idxS.length()+2);
  if(vs.empty())error("value missing in setAt");
  varInfo fvi=getVarInfo(fs);
  Value* fvp=fvi.val;
  Value* fv=getVarVal(fs);
  Type* ft=getType(fvi.type);
  Value* idxV=getSomethingValue(idxS);
  Value* dataV=getSomethingValue(vs);
  if(ft->isStructTy()){
    auto fst=static_cast<StructType*>(ft);
    if(fst->getElementType(fst->getNumElements()-1)->isIntegerTy(1)){
      dynArrSet(fv,builder->CreateSExtOrTrunc(idxV,Type::getInt64Ty(*ctx)),dataV);
    }else{
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),builder->CreateSExtOrTrunc(idxV,Type::getInt32Ty(*ctx))};
      Value* setP=builder->CreateGEP(ft,fvp,idcs,"setAtColl_setP");
      builder->CreateStore(dataV,setP);
    }
  }else{
    string fsubts=getSubTypeSFromTypeS(fvi.type);
    Type* fsubt=getType(fsubts);
    if(ft->isArrayTy()){
      Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),builder->CreateSExtOrTrunc(idxV,Type::getInt64Ty(*ctx))};
      builder->CreateStore(dataV,builder->CreateGEP(ft,fvp,idcs));
    }else if(ft->isPointerTy()){
      builder->CreateStore(dataV,fv);
    }
  }
}

void parseLbl(string a){
  BasicBlock* newLbl;
  Function* f=builder->GetInsertBlock()->getParent();
  auto pair=lbls.find(a);
  if(pair==lbls.end()){ // no match
    newLbl=BasicBlock::Create(*ctx,a,f);
  }else{
    newLbl=pair->second;
    f->insert(f->end(),newLbl);
  }
  builder->CreateBr(newLbl);
  builder->SetInsertPoint(newLbl);
  lbls[a]=newLbl;
}

void parseJmp(string a){
  BasicBlock* bb;
  auto pair=lbls.find(a);
  if(pair==lbls.end()){ // no match
    bb=BasicBlock::Create(*ctx,a);
    lbls[a]=bb;
  }else
    bb=pair->second;
  builder->CreateBr(bb);
  BasicBlock* altBB=BasicBlock::Create(*ctx,"jmpCont",builder->GetInsertBlock()->getParent());
  builder->SetInsertPoint(altBB);
}

void parseJmpif(string a){
  string cs=subStrTo(a,' ');
  if(cs.empty())error("condition missing in jmpif");
  string as=subStrTo(a,' ',cs.length()+1);
  if(as.empty())error("label missing in jmpif");
  BasicBlock* bb;
  auto pair=lbls.find(as);
  if(pair==lbls.end()){ // no match
    bb=BasicBlock::Create(*ctx,as);
    lbls[as]=bb;
  }else
    bb=pair->second;
  BasicBlock* altBB=BasicBlock::Create(*ctx,"jmpifFailed",builder->GetInsertBlock()->getParent());
  Value* cv=getSomethingValue(cs);
  Value* c;
  Type* ct=cv->getType();
  if(ct->isFloatingPointTy()){
    c=builder->CreateFCmpONE(cv,ConstantFP::get(ct,0.));
  }else if(ct->isIntegerTy()){
    c=builder->CreateICmpNE(cv,ConstantInt::get(ct,0));
  }else if(ct->isPointerTy()){
    c=builder->CreateICmpNE(cv,Constant::getNullValue(ct));
  }
  builder->CreateCondBr(c,bb,altBB);
  builder->SetInsertPoint(altBB);
}

void parseDef(string a){
  if(outOfMainFn)error("trying to def new function before ret from previous function");
  outOfMainFn=true;
  string as=subStrTo(a,' ');
  if(as.empty())error("label missing in def");
  string ts=subStrTo(a,' ',as.length()+1);
  if(ts.empty())error("arg type missing in def");
  string vs=subStrTo(a,' ',as.length()+1+ts.length()+1);
  if(vs.empty())error("arg missing in def");
  if(vs.at(0)!='v')error("arg is no variable in def");
  mainBB=builder->GetInsertBlock();
  Type* fnType=getType(ts);
  Function* f;
  auto pair=fns.find(as);
  if(pair==fns.end()){
    Type* args[]={fnType};
    f=Function::Create(FunctionType::get(Type::getInt1Ty(*ctx),args,false),Function::ExternalLinkage,"fn_"+as,mdl.get());
    fns[as]=f;
  }else
    f=pair->second;
  actFn=f;
  BasicBlock *bb=BasicBlock::Create(*ctx,"entry",f);
  builder->SetInsertPoint(bb);
  Value* vv=createEntryAlloca(f,fnType,vs);
  builder->CreateStore(&f->args().begin()[0],vv);
  varsMem.clear();
  varsMem.push_back(vars[0]);
  varsMem.push_back(map<string,varInfo>());
  varsMem.swap(vars);
  lblsMem.clear();
  lblsMem.swap(lbls);
  vars.back()[vs]=varInfo{ts,vv};
}

void parseRet(string a){
  if(!outOfMainFn)error("trying to ret from main scope");
  outOfMainFn=false;
  builder->CreateRet(ConstantInt::get(Type::getInt1Ty(*ctx),0));
  verifyFunction(*actFn);
  fpm->run(*actFn);
  builder->SetInsertPoint(mainBB);
  actFn=mainBB->getParent();
  vars.swap(varsMem);
  lbls.swap(lblsMem);
}

void parseExit(string a){
  if(outOfMainFn){
    builder->CreateRet(ConstantInt::get(Type::getInt1Ty(*ctx),1));
  }else{
    builder->CreateRet(Constant::getNullValue(Type::getInt32Ty(*ctx)));
  }
  BasicBlock* bb=BasicBlock::Create(*ctx,"afterExit",builder->GetInsertBlock()->getParent());
  builder->SetInsertPoint(bb);
}

void parseCall(string a){
  string as=subStrTo(a,' ');
  if(as.empty())error("label missing in call");
  string ss=subStrTo(a,' ',as.length()+1);
  if(ss.empty())error("arg missing in call");
  Value* sv=getSomethingValue(ss);
  Function* fn;
  auto pair=fns.find(as);
  if(pair==fns.end()){
    Type* args[]={sv->getType()};
    fn=Function::Create(FunctionType::get(Type::getInt1Ty(*ctx),args,false),Function::ExternalLinkage,"fn_"+as,mdl.get());
    fns[as]=fn;
  }else
    fn=pair->second;
  Value* args[]={sv};
  Value* ret=builder->CreateCall(fn,args,as+"_call");
  BasicBlock* bbExit=BasicBlock::Create(*ctx,"exitAfterCall",actFn);
  BasicBlock* bbCont=BasicBlock::Create(*ctx,"noExitAfterCall");
  builder->CreateCondBr(ret,bbExit,bbCont);
  builder->SetInsertPoint(bbExit);
  if(outOfMainFn){
    builder->CreateRet(ConstantInt::get(Type::getInt1Ty(*ctx),1));
  }else{
    builder->CreateRet(Constant::getNullValue(Type::getInt32Ty(*ctx)));
  }
  actFn->insert(actFn->end(),bbCont);
  builder->SetInsertPoint(bbCont);
}

void parseAdd(string a){
  string ls=subStrTo(a,' ');
  if(ls.empty())error("lefthand missing in add");
  string rs=subStrTo(a,' ',ls.length()+1);
  if(rs.empty())error("righthand missing in add");
  string vs=subStrTo(a,' ',ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in add");
  if(vs.at(0)!='v')error("destination is no variable in add");
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  Type* lt=lv->getType();
  Type* rt=rv->getType();
  if(lt->isIntegerTy()){
    if(rt->isPointerTy()){
      parseAdd(rs+" "+ls+" "+vs);
      return;
    }
    if(!rt->isIntegerTy()){
      error("trying to add an integer with a non integer");
    }
    unsigned lbw=static_cast<IntegerType*>(lt)->getBitWidth(),rbw=static_cast<IntegerType*>(rt)->getBitWidth();
    if(lbw>rbw){
      rv=builder->CreateSExt(rv,lt,"add_int_ext");
    }else if(lbw<rbw){
      lv=builder->CreateSExt(lv,rt,"add_int_ext");
    }
    Value* vv=getVarRef(vs,"i"+to_string(lbw>rbw?lbw:rbw));
    builder->CreateStore(builder->CreateAdd(lv,rv,"add_result"),vv);
  }else if(lt->isFloatingPointTy()){
    if(!rt->isFloatingPointTy()){
      error("trying to add a float with a non float");
    }
    string vts="f32";
    if(lt->isDoubleTy()){
      vts="f64";
      if(rt->isFloatTy()){
        rv=builder->CreateFPCast(rv,lt,"add_float_ext");
      }
    }else if(rt->isDoubleTy()){
      vts="f64";
      lv=builder->CreateFPCast(lv,rt,"add_float_ext");
    }
    Value* vv=getVarRef(vs,vts);
    builder->CreateStore(builder->CreateFAdd(lv,rv,"add_result"),vv);
  }else if(lt->isPointerTy()){
    if(!rt->isIntegerTy()){
      error("trying to add a ptr with a non int");
    }
    Value* vv=getVarRef(vs,getTypeS(lt));
    Value* idcs[]={rv};
    builder->CreateStore(builder->CreateGEP(static_cast<PointerType*>(lt)->getPointerElementType(),lv,idcs,"add_result"),vv);
  }else if(lt->isStructTy()){
    auto lst=static_cast<StructType*>(lt);
    if(lst->getElementType(lst->getNumElements()-1)->isIntegerTy(1)){
      if(rt->isStructTy()){
        auto rst=static_cast<StructType*>(rt);
        if(rst->getElementType(rst->getNumElements()-1)->isIntegerTy(1)){
          string ts=getTypeS(lt);
          if(ts!=getTypeS(rt)){
            error("darr types not matching when trying to add them");
          }
          dynArrIR dair=getDynArrIRByType(lt);
          Value* lvp=createEntryAlloca(actFn,lt);
          Value* rvp=createEntryAlloca(actFn,lt);
          builder->CreateStore(lv,lvp);
          builder->CreateStore(rv,rvp);
          Value* vv=getVarRef(vs,ts);
          Value* args[]={vv,lvp,rvp};
          builder->CreateCall(dair.concat,args);
        }
      }
    }
  }else if(lt->isArrayTy()){
    if(!rt->isArrayTy())error("trying to add an array with a non array");
    auto lat=static_cast<ArrayType*>(lt);
    auto rat=static_cast<ArrayType*>(rt);
    auto st=lat->getElementType();
    if(st!=rat->getElementType())error("trying to add two arrays of different types");
    Value* lvp=createEntryAlloca(actFn,lt,"add_arr_lvp");
    Value* rvp=createEntryAlloca(actFn,rt,"add_arr_rvp");
    builder->CreateStore(lv,lvp);
    builder->CreateStore(rv,rvp);
    unsigned lne=lat->getNumElements(),rne=rat->getNumElements();
    Type* vt=ArrayType::get(st,lne+rne);
    Value* vv=getVarRef(vs,getTypeS(vt));
    if(!mallocFnsUsed)initMallocFns();
    Value* sts=getTypeSize(st,builder->GetInsertBlock());
    Value* idcs[]={ConstantInt::get(Type::getInt64Ty(*ctx),0),ConstantInt::get(Type::getInt64Ty(*ctx),0)};
    Value* lstartP=builder->CreateGEP(lt,lvp,idcs,"add_arr_lstartP");
    Value* rstartP=builder->CreateGEP(rt,rvp,idcs,"add_arr_rstartP");
    Value* vstartP=builder->CreateGEP(vt,vv,idcs,"add_arr_vstartP");
    idcs[1]=ConstantInt::get(Type::getInt64Ty(*ctx),lne);
    Value* vmidP=builder->CreateGEP(vt,vv,idcs,"add_arr_vmidP");
    Value* lnumCpy=builder->CreateMul(ConstantInt::get(Type::getInt64Ty(*ctx),lne),sts,"add_arr_lnumCpy");
    Value* rnumCpy=builder->CreateMul(ConstantInt::get(Type::getInt64Ty(*ctx),rne),sts,"add_arr_rnumCpy");
    Value* args[]={builder->CreateBitCast(vstartP,Type::getInt8PtrTy(*ctx)),builder->CreateBitCast(lstartP,Type::getInt8PtrTy(*ctx)),lnumCpy};
    builder->CreateCall(memmoveFn,args);
    args[0]=builder->CreateBitCast(vmidP,Type::getInt8PtrTy(*ctx));args[1]=builder->CreateBitCast(rstartP,Type::getInt8PtrTy(*ctx));args[2]=rnumCpy;
    builder->CreateCall(memmoveFn,args);
  }
}

void parseSub(string a){
  string ls=subStrTo(a,' ');
  if(ls.empty())error("lefthand missing in sub");
  string rs=subStrTo(a,' ',ls.length()+1);
  if(rs.empty())error("righthand missing in sub");
  string vs=subStrTo(a,' ',ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in sub");
  if(vs.at(0)!='v')error("destination is no variable in sub");
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  Type* lt=lv->getType();
  Type* rt=rv->getType();
  if(lt->isIntegerTy()){
    if(!rt->isIntegerTy()){
      error("trying to sub an integer with a non integer");
    }
    unsigned lbw=static_cast<IntegerType*>(lt)->getBitWidth(),rbw=static_cast<IntegerType*>(rt)->getBitWidth();
    if(lbw>rbw){
      rv=builder->CreateSExt(rv,lt,"sub_int_ext");
    }else if(lbw<rbw){
      lv=builder->CreateSExt(lv,rt,"sub_int_ext");
    }
    Value* vv=getVarRef(vs,"i"+to_string(lbw>rbw?lbw:rbw));
    builder->CreateStore(builder->CreateSub(lv,rv,"sub_result"),vv);
  }else if(lt->isFloatingPointTy()){
    if(!rt->isFloatingPointTy()){
      error("trying to sub a float with a non float");
    }
    string vts="f32";
    if(lt->isDoubleTy()){
      vts="f64";
      if(rt->isFloatTy()){
        rv=builder->CreateFPCast(rv,lt,"sub_float_ext");
      }
    }else if(rt->isDoubleTy()){
      vts="f64";
      lv=builder->CreateFPCast(lv,rt,"sub_float_ext");
    }
    Value* vv=getVarRef(vs,vts);
    builder->CreateStore(builder->CreateFSub(lv,rv,"sub_result"),vv);
  }else if(lt->isPointerTy()){
    if(!rt->isIntegerTy()){
      error("trying to sub a ptr with a non int");
    }
    Value* vv=getVarRef(vs,getTypeS(lt));
    Value* idcs[]={builder->CreateSub(Constant::getNullValue(rt),rv)};
    builder->CreateStore(builder->CreateGEP(static_cast<PointerType*>(lt)->getPointerElementType(),lv,idcs,"sub_result"),vv);
  }
}

void parseMul(string a){
  string ls=subStrTo(a,' ');
  if(ls.empty())error("lefthand missing in mul");
  string rs=subStrTo(a,' ',ls.length()+1);
  if(rs.empty())error("righthand missing in mul");
  string vs=subStrTo(a,' ',ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in mul");
  if(vs.at(0)!='v')error("destination is no variable in mul");
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  Type* lt=lv->getType();
  Type* rt=rv->getType();
  if(lt->isIntegerTy()){
    if(rt->isStructTy()){
      parseMul(rs+" "+ls+" "+vs);
      return;
    }
    if(!rt->isIntegerTy()){
      error("trying to mul an integer with a non integer");
    }
    unsigned lbw=static_cast<IntegerType*>(lt)->getBitWidth(),rbw=static_cast<IntegerType*>(rt)->getBitWidth();
    if(lbw>rbw){
      rv=builder->CreateSExt(rv,lt,"mul_int_ext");
    }else if(lbw<rbw){
      lv=builder->CreateSExt(lv,rt,"mul_int_ext");
    }
    Value* vv=getVarRef(vs,"i"+to_string(lbw>rbw?lbw:rbw));
    builder->CreateStore(builder->CreateMul(lv,rv,"mul_result"),vv);
  }else if(lt->isFloatingPointTy()){
    if(!rt->isFloatingPointTy()){
      error("trying to mul a float with a non float");
    }
    string vts="f32";
    if(lt->isDoubleTy()){
      vts="f64";
      if(rt->isFloatTy()){
        rv=builder->CreateFPCast(rv,lt,"mul_float_ext");
      }
    }else if(rt->isDoubleTy()){
      vts="f64";
      lv=builder->CreateFPCast(lv,rt,"mul_float_ext");
    }
    Value* vv=getVarRef(vs,vts);
    builder->CreateStore(builder->CreateFMul(lv,rv,"mul_result"),vv);
  }else if(lt->isStructTy()){
    auto lst=static_cast<StructType*>(lt);
    if(lst->getElementType(lst->getNumElements()-1)->isIntegerTy(1)){
      if(rt->isIntegerTy()){
        dynArrIR dair=getDynArrIRByType(lt);
        Value* vv=getVarRef(vs,dair.typeString);
        Value* lvp=createEntryAlloca(actFn,lt);
        builder->CreateStore(lv,lvp);
        Value* i=createEntryAlloca(actFn,Type::getInt64Ty(*ctx),"mul_darr_runningVar");
        builder->CreateStore(rv,i);
        Value* args[]={vv,Constant::getNullValue(Type::getInt64Ty(*ctx))};
        builder->CreateCall(dair.create,args);
        BasicBlock* loopStart=BasicBlock::Create(*ctx,"mul_darr_loopStart",actFn);
        BasicBlock* loopCont=BasicBlock::Create(*ctx,"mul_darr_loopCont");
        BasicBlock* loopBreak=BasicBlock::Create(*ctx,"mul_darr_loopBreak");
        builder->CreateBr(loopStart);
        builder->SetInsertPoint(loopStart);
        Value* iv=builder->CreateLoad(Type::getInt64Ty(*ctx),i);
        Value* cont=builder->CreateICmpNE(iv,Constant::getNullValue(Type::getInt64Ty(*ctx)),"mul_darr_continue");
        builder->CreateCondBr(cont,loopCont,loopBreak);
        actFn->insert(actFn->end(),loopCont);
        builder->SetInsertPoint(loopCont);
        Value* args1[]={vv,vv,lvp};
        builder->CreateCall(dair.concat,args1);
        Value* ivDec=builder->CreateSub(iv,ConstantInt::get(Type::getInt64Ty(*ctx),1),"mul_darr_runningVarDec");
        builder->CreateStore(ivDec,i);
        builder->CreateBr(loopStart);
        actFn->insert(actFn->end(),loopBreak);
        builder->SetInsertPoint(loopBreak);
      }
    }
  }
}

void parseDiv(string a){
  string ls=subStrTo(a,' ');
  if(ls.empty())error("lefthand missing in div");
  string rs=subStrTo(a,' ',ls.length()+1);
  if(rs.empty())error("righthand missing in div");
  string vs=subStrTo(a,' ',ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in div");
  if(vs.at(0)!='v')error("destination is no variable in div");
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  Type* lt=lv->getType();
  Type* rt=rv->getType();
  if(lt->isIntegerTy()){
    if(!rt->isIntegerTy()){
      error("trying to div an integer with a non integer");
    }
    unsigned lbw=static_cast<IntegerType*>(lt)->getBitWidth(),rbw=static_cast<IntegerType*>(rt)->getBitWidth();
    if(lbw>rbw){
      rv=builder->CreateSExt(rv,lt,"div_int_ext");
    }else if(lbw<rbw){
      lv=builder->CreateSExt(lv,rt,"div_int_ext");
    }
    Value* vv=getVarRef(vs,"i"+to_string(lbw>rbw?lbw:rbw));
    builder->CreateStore(builder->CreateSDiv(lv,rv,"div_result"),vv);
  }else if(lt->isFloatingPointTy()){
    if(!rt->isFloatingPointTy()){
      error("trying to div a float with a non float");
    }
    string vts="f32";
    if(lt->isDoubleTy()){
      vts="f64";
      if(rt->isFloatTy()){
        rv=builder->CreateFPCast(rv,lt,"div_float_ext");
      }
    }else if(rt->isDoubleTy()){
      vts="f64";
      lv=builder->CreateFPCast(lv,rt,"div_float_ext");
    }
    Value* vv=getVarRef(vs,vts);
    builder->CreateStore(builder->CreateFDiv(lv,rv,"div_result"),vv);
  }
}

void destroyVal(Value* v){
  Type* t=v->getType();
  if(getTypeS(t).find("darr")==string::npos)return;
  if(t->isPointerTy()){
    destroyVal(builder->CreateLoad(static_cast<PointerType*>(t)->getPointerElementType(),v));
  }else if(t->isArrayTy()){
    Value* vCopyP=createEntryAlloca(actFn,t,"destroyArrVCopyP");
    builder->CreateStore(v,vCopyP);
    ArrayType* at=static_cast<ArrayType*>(t);
    unsigned ne=at->getNumElements();
    Value* runningP=createEntryAlloca(actFn,Type::getInt64Ty(*ctx),"destroyArrRunningP");
    builder->CreateStore(Constant::getNullValue(Type::getInt64Ty(*ctx)),runningP);
    BasicBlock* loopStart=BasicBlock::Create(*ctx,"destroy_arr_loopStart",actFn);
    BasicBlock* loopCont=BasicBlock::Create(*ctx,"destroy_arr_loopCont");
    BasicBlock* loopBreak=BasicBlock::Create(*ctx,"destroy_arr_loopBreak");
    builder->CreateBr(loopStart);
    builder->SetInsertPoint(loopStart);
    Value* running=builder->CreateLoad(Type::getInt64Ty(*ctx),runningP,"destroyArrRunning");
    Value* cont=builder->CreateICmpULT(running,ConstantInt::get(Type::getInt64Ty(*ctx),ne),"destroyArrContinue");
    builder->CreateCondBr(cont,loopCont,loopBreak);
    actFn->insert(actFn->end(),loopCont);
    builder->SetInsertPoint(loopCont);
    Value* idcs[]={Constant::getNullValue(Type::getInt64Ty(*ctx)),running};
    Value* actElP=builder->CreateGEP(t,vCopyP,idcs,"destroyArrActElP");
    destroyVal(builder->CreateLoad(at->getElementType(),actElP,"destroyArrActEl"));
    Value* runningInc=builder->CreateAdd(ConstantInt::get(Type::getInt64Ty(*ctx),1),running,"destroyArrRunningInc");
    builder->CreateStore(runningInc,runningP);
    builder->CreateBr(loopStart);
    actFn->insert(actFn->end(),loopBreak);
    builder->SetInsertPoint(loopBreak);
  }else if(t->isStructTy()){
    auto st=static_cast<StructType*>(t);
    unsigned sne=st->getNumElements();
    if(st->getElementType(sne-1)->isIntegerTy(1)){
      Value* runningP=createEntryAlloca(actFn,Type::getInt64Ty(*ctx),"destroyDarrRunningP");
      builder->CreateStore(Constant::getNullValue(Type::getInt64Ty(*ctx)),runningP);
      Value* ne=dynArrLen(v);
      BasicBlock* loopStart=BasicBlock::Create(*ctx,"destroy_darr_loopStart",actFn);
      BasicBlock* loopCont=BasicBlock::Create(*ctx,"destroy_darr_loopCont");
      BasicBlock* loopBreak=BasicBlock::Create(*ctx,"destroy_darr_loopBreak");
      builder->CreateBr(loopStart);
      builder->SetInsertPoint(loopStart);
      Value* running=builder->CreateLoad(Type::getInt64Ty(*ctx),runningP,"destroyDarrRunning");
      Value* cont=builder->CreateICmpULT(running,ne,"destroyDarrContinue");
      builder->CreateCondBr(cont,loopCont,loopBreak);
      actFn->insert(actFn->end(),loopCont);
      builder->SetInsertPoint(loopCont);
      destroyVal(dynArrGet(v,running));
      Value* runningInc=builder->CreateAdd(ConstantInt::get(Type::getInt64Ty(*ctx),1),running,"destroyArrRunningInc");
      builder->CreateStore(runningInc,runningP);
      builder->CreateBr(loopStart);
      actFn->insert(actFn->end(),loopBreak);
      builder->SetInsertPoint(loopBreak);
      Value* vCopyP=createEntryAlloca(actFn,t,"destroyDarrVCopyP");
      builder->CreateStore(v,vCopyP);
      Value* args[]={vCopyP};
      builder->CreateCall(getDynArrIRByType(t).destroy,args);
    }else{
      Value* vCopyP=createEntryAlloca(actFn,t,"destroyCollVCopyP");
      builder->CreateStore(v,vCopyP);
      for(unsigned i=0;i<sne;i++){
        Value* idcs[]={Constant::getNullValue(Type::getInt64Ty(*ctx)),ConstantInt::get(Type::getInt32Ty(*ctx),i)};
        Value* actElP=builder->CreateGEP(t,vCopyP,idcs,"destroyCollActElP");
        destroyVal(builder->CreateLoad(st->getElementType(i),actElP,"destroyCollActEl"));
      }
    }
  }
}

void parseDestroy(string a){
  if(a.at(0)!='v')error("trying to destroy a literal - you can only destroy variables");
  varInfo vi={"",nullptr};
  unsigned i=0;
  for(;i<vars.size();i++){
    if(vars[i].count(a)>0){
      vi=vars[i][a];
      break;
    }
  }
  if(vi.val){
    if(vi.type.find("darr")!=string::npos){
      destroyVal(builder->CreateLoad(getType(vi.type),vi.val,"destroyVVal"));
    }
    vars[i].erase(a);
  }else error("trying to destroy nonexistent variable "+a);
}

Value* cmpEq(Value* lv,Value* rv){
  Type* lt=lv->getType();
  Type* rt=rv->getType();
  if(lt->isIntegerTy()){
    if(!rt->isIntegerTy()){
      error("trying to eq an integer with a non integer");
    }
    unsigned lbw=static_cast<IntegerType*>(lt)->getBitWidth(),rbw=static_cast<IntegerType*>(rt)->getBitWidth();
    if(lbw>rbw){
      rv=builder->CreateSExt(rv,lt,"eq_int_ext");
    }else if(lbw<rbw){
      lv=builder->CreateSExt(lv,rt,"eq_int_ext");
    }
    return builder->CreateICmpEQ(lv,rv,"eq_result");
  }else if(lt->isFloatingPointTy()){
    if(!rt->isFloatingPointTy()){
      error("trying to eq a float with a non float");
    }
    if(lt->isDoubleTy()){
      if(rt->isFloatTy()){
        rv=builder->CreateFPCast(rv,lt,"eq_float_ext");
      }
    }else if(rt->isDoubleTy()){
      lv=builder->CreateFPCast(lv,rt,"eq_float_ext");
    }
    return builder->CreateFCmpOEQ(lv,rv,"eq_result");
  }else if(lt->isPointerTy()){
    if(!rt->isPointerTy()){
      error("trying to eq a ptr with a non ptr");
    }
    return builder->CreateICmpEQ(lv,rv,"eq_result");
  }else if(lt->isArrayTy()){
    if(!rt->isArrayTy()){
      error("trying to eq an arr with a non arr");
    }
    ArrayType* lat=static_cast<ArrayType*>(lt);
    ArrayType* rat=static_cast<ArrayType*>(rt);
    Type* ast=lat->getElementType();
    if(ast!=rat->getElementType()){error("trying to eq two arrays of different type");return nullptr;}
    unsigned ne=lat->getNumElements();
    if(ne!=rat->getNumElements())return Constant::getNullValue(Type::getInt1Ty(*ctx));
    Value* lvCopyP=createEntryAlloca(actFn,lt,"eqArrLVCopyP");
    builder->CreateStore(lv,lvCopyP);
    Value* rvCopyP=createEntryAlloca(actFn,rt,"eqArrRVCopyP");
    builder->CreateStore(rv,rvCopyP);
    Value* runningP=createEntryAlloca(actFn,Type::getInt64Ty(*ctx),"eqArrRunningP");
    builder->CreateStore(Constant::getNullValue(Type::getInt64Ty(*ctx)),runningP);
    Value* retP=createEntryAlloca(actFn,Type::getInt1Ty(*ctx),"retVal");
    builder->CreateStore(ConstantInt::get(Type::getInt1Ty(*ctx),1),retP);
    BasicBlock* loopStart=BasicBlock::Create(*ctx,"eq_arr_loopStart",actFn);
    BasicBlock* loopCont=BasicBlock::Create(*ctx,"eq_arr_loopCont");
    BasicBlock* bbElsAreEq=BasicBlock::Create(*ctx,"eq_arr_elsAreEq");
    BasicBlock* bbElsAreNe=BasicBlock::Create(*ctx,"eq_arr_elsAreNe");
    BasicBlock* loopBreak=BasicBlock::Create(*ctx,"eq_arr_loopBreak");
    builder->CreateBr(loopStart);
    builder->SetInsertPoint(loopStart);
    Value* running=builder->CreateLoad(Type::getInt64Ty(*ctx),runningP,"eqArrRunning");
    Value* cont=builder->CreateICmpULT(running,ConstantInt::get(Type::getInt64Ty(*ctx),ne),"eqArrContinue");
    builder->CreateCondBr(cont,loopCont,loopBreak);
    actFn->insert(actFn->end(),loopCont);
    builder->SetInsertPoint(loopCont);
    Value* idcs[]={Constant::getNullValue(Type::getInt64Ty(*ctx)),running};
    Value* lActElP=builder->CreateGEP(lt,lvCopyP,idcs,"eqArrLActElP");
    Value* rActElP=builder->CreateGEP(rt,rvCopyP,idcs,"eqArrRActElP");
    Value* res=cmpEq(builder->CreateLoad(ast,lActElP,"eqArrLActEl"),builder->CreateLoad(ast,rActElP,"eqArrRActEl"));
    builder->CreateCondBr(res,bbElsAreEq,bbElsAreNe);
    actFn->insert(actFn->end(),bbElsAreNe);
    builder->SetInsertPoint(bbElsAreNe);
    builder->CreateStore(Constant::getNullValue(Type::getInt1Ty(*ctx)),retP);
    builder->CreateBr(loopBreak);
    actFn->insert(actFn->end(),bbElsAreEq);
    builder->SetInsertPoint(bbElsAreEq);
    Value* runningInc=builder->CreateAdd(ConstantInt::get(Type::getInt64Ty(*ctx),1),running,"eqArrRunningInc");
    builder->CreateStore(runningInc,runningP);
    builder->CreateBr(loopStart);
    actFn->insert(actFn->end(),loopBreak);
    builder->SetInsertPoint(loopBreak);
    return builder->CreateLoad(Type::getInt1Ty(*ctx),retP);
  }else if(lt->isStructTy()){
    if(!rt->isStructTy()){error("trying to eq coll or darr with something else");return nullptr;}
    auto lst=static_cast<StructType*>(lt);
    auto rst=static_cast<StructType*>(rt);
    unsigned ne=lst->getNumElements();
    if(ne!=rst->getNumElements()){error("trying to eq coll or darr with coll or darr of different type");return nullptr;}
    if(lst->getElementType(ne-1)->isIntegerTy(1)){
      if(!rst->getElementType(ne-1)->isIntegerTy(1)){error("trying to eq darr with coll");return nullptr;}
      dynArrIR dair=getDynArrIRByType(lt);
      if(dair.subTypeS!=getDynArrIRByType(rt).subTypeS){error("trying to eq darrs of different subtypes");return nullptr;}
      Value* ne=dynArrLen(lv);
      Value* rne=dynArrLen(rv);
      Value* retP=createEntryAlloca(actFn,Type::getInt1Ty(*ctx),"retVal");
      builder->CreateStore(ConstantInt::get(Type::getInt1Ty(*ctx),1),retP);
      BasicBlock* bbSameLen=BasicBlock::Create(*ctx,"eq_darr_sameLen",actFn);
      BasicBlock* bbRet0=BasicBlock::Create(*ctx,"eq_darr_retFalse");
      Value* sameLen=builder->CreateICmpEQ(ne,rne,"eqDarrSameLen");
      builder->CreateCondBr(sameLen,bbSameLen,bbRet0);
      builder->SetInsertPoint(bbSameLen);
      Value* lvCopyP=createEntryAlloca(actFn,lt,"eqDarrLVCopyP");
      builder->CreateStore(lv,lvCopyP);
      Value* rvCopyP=createEntryAlloca(actFn,rt,"eqDarrRVCopyP");
      builder->CreateStore(rv,rvCopyP);
      Value* runningP=createEntryAlloca(actFn,Type::getInt64Ty(*ctx),"eqDarrRunningP");
      builder->CreateStore(Constant::getNullValue(Type::getInt64Ty(*ctx)),runningP);
      BasicBlock* loopStart=BasicBlock::Create(*ctx,"eq_darr_loopStart",actFn);
      BasicBlock* loopCont=BasicBlock::Create(*ctx,"eq_darr_loopCont");
      BasicBlock* bbElsAreEq=BasicBlock::Create(*ctx,"eq_darr_elsAreEq");
      BasicBlock* loopBreak=BasicBlock::Create(*ctx,"eq_darr_loopBreak");
      builder->CreateBr(loopStart);
      builder->SetInsertPoint(loopStart);
      Value* running=builder->CreateLoad(Type::getInt64Ty(*ctx),runningP,"eqDarrRunning");
      Value* cont=builder->CreateICmpULT(running,ne,"eqDarrContinue");
      builder->CreateCondBr(cont,loopCont,loopBreak);
      actFn->insert(actFn->end(),loopCont);
      builder->SetInsertPoint(loopCont);
      Value* lActEl=dynArrGet(lv,running);
      Value* rActEl=dynArrGet(rv,running);
      Value* res=cmpEq(lActEl,rActEl);
      builder->CreateCondBr(res,bbElsAreEq,bbRet0);
      actFn->insert(actFn->end(),bbRet0);
      builder->SetInsertPoint(bbRet0);
      builder->CreateStore(Constant::getNullValue(Type::getInt1Ty(*ctx)),retP);
      builder->CreateBr(loopBreak);
      actFn->insert(actFn->end(),bbElsAreEq);
      builder->SetInsertPoint(bbElsAreEq);
      Value* runningInc=builder->CreateAdd(ConstantInt::get(Type::getInt64Ty(*ctx),1),running,"eqArrRunningInc");
      builder->CreateStore(runningInc,runningP);
      builder->CreateBr(loopStart);
      actFn->insert(actFn->end(),loopBreak);
      builder->SetInsertPoint(loopBreak);
      return builder->CreateLoad(Type::getInt1Ty(*ctx),retP);
    }else{
      if(rst->getElementType(ne-1)->isIntegerTy(1)){error("trying to eq coll with darr");return nullptr;}
      Value* lvCopyP=createEntryAlloca(actFn,lt,"eqCollLVCopyP");
      builder->CreateStore(lv,lvCopyP);
      Value* rvCopyP=createEntryAlloca(actFn,rt,"eqCollRVCopyP");
      builder->CreateStore(rv,rvCopyP);
      Value* retP=createEntryAlloca(actFn,Type::getInt1Ty(*ctx),"eqCollRetP");
      builder->CreateStore(ConstantInt::get(Type::getInt1Ty(*ctx),1),retP);
      BasicBlock* bbret0=BasicBlock::Create(*ctx,"eqCollReturnFalse");
      for(unsigned i=0;i<ne-1;i++){
        Value* idcs[]={Constant::getNullValue(Type::getInt64Ty(*ctx)),ConstantInt::get(Type::getInt32Ty(*ctx),i)};
        Value* lActElP=builder->CreateGEP(lt,lvCopyP,idcs,"eqCollLActElP");
        Value* rActElP=builder->CreateGEP(rt,rvCopyP,idcs,"eqCollRActElP");
        Value* res=cmpEq(builder->CreateLoad(lst->getElementType(i),lActElP,"eqCollLActEl"),builder->CreateLoad(rst->getElementType(i),rActElP,"eqCollRActEl"));
        BasicBlock* bbCont=BasicBlock::Create(*ctx,"eqCollCont",actFn);
        builder->CreateCondBr(res,bbCont,bbret0);
        builder->SetInsertPoint(bbCont);
      }
      BasicBlock* bbEnd=BasicBlock::Create(*ctx,"eqCollEnd");
      builder->CreateBr(bbEnd);
      actFn->insert(actFn->end(),bbret0);
      builder->SetInsertPoint(bbret0);
      builder->CreateStore(Constant::getNullValue(Type::getInt1Ty(*ctx)),retP);
      builder->CreateBr(bbEnd);
      actFn->insert(actFn->end(),bbEnd);
      builder->SetInsertPoint(bbEnd);
      return builder->CreateLoad(Type::getInt1Ty(*ctx),retP);
    }
  }
}

void parseEq(string a){
  string ls=subStrTo(a,' ');
  if(ls.empty())error("lefthand missing in eq");
  string rs=subStrTo(a,' ',ls.length()+1);
  if(rs.empty())error("righthand missing in eq");
  string vs=subStrTo(a,' ',ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in eq");
  if(vs.at(0)!='v')error("destination is no variable in eq");
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  Value* vv=getVarRef(vs,"i8");
  builder->CreateStore(builder->CreateZExt(cmpEq(lv,rv),Type::getInt8Ty(*ctx)),vv);
}

void parseGt(string a){
  string ls=subStrTo(a,' ');
  if(ls.empty())error("lefthand missing in gt");
  string rs=subStrTo(a,' ',ls.length()+1);
  if(rs.empty())error("righthand missing in gt");
  string vs=subStrTo(a,' ',ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in gt");
  if(vs.at(0)!='v')error("destination is no variable in gt");
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  Type* lt=lv->getType();
  Type* rt=rv->getType();
  Value* vv=getVarRef(vs,"i8");
  Value* res;
  if(lt->isIntegerTy()){
    if(!rt->isIntegerTy()){
      error("trying to gt an integer with a non integer");
    }
    unsigned lbw=static_cast<IntegerType*>(lt)->getBitWidth(),rbw=static_cast<IntegerType*>(rt)->getBitWidth();
    if(lbw>rbw){
      rv=builder->CreateSExt(rv,lt,"gt_int_ext");
    }else if(lbw<rbw){
      lv=builder->CreateSExt(lv,rt,"gt_int_ext");
    }
    res=builder->CreateICmpSGT(lv,rv,"gt_int_res");
  }else if(lt->isFloatingPointTy()){
    if(!rt->isFloatingPointTy()){
      error("trying to gt a float with a non float");
    }
    if(lt->isDoubleTy()){
      if(rt->isFloatTy()){
        rv=builder->CreateFPCast(rv,lt,"gt_float_ext");
      }
    }else if(rt->isDoubleTy()){
      lv=builder->CreateFPCast(lv,rt,"gt_float_ext");
    }
    res=builder->CreateFCmpOGT(lv,rv,"gt_result");
  }else if(lt->isPointerTy()){
    if(!rt->isPointerTy()){
      error("trying to gt a ptr with a non ptr");
    }
    res=builder->CreateICmpUGT(lv,rv,"gt_ptr_res");
  }
  builder->CreateStore(builder->CreateZExt(res,Type::getInt8Ty(*ctx)),vv);
}

void parseGte(string a){
  string ls=subStrTo(a,' ');
  if(ls.empty())error("lefthand missing in gte");
  string rs=subStrTo(a,' ',ls.length()+1);
  if(rs.empty())error("righthand missing in gte");
  string vs=subStrTo(a,' ',ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in gte");
  if(vs.at(0)!='v')error("destination is no variable in gte");
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  Type* lt=lv->getType();
  Type* rt=rv->getType();
  Value* vv=getVarRef(vs,"i8");
  Value* res;
  if(lt->isIntegerTy()){
    if(!rt->isIntegerTy()){
      error("trying to gte an integer with a non integer");
    }
    unsigned lbw=static_cast<IntegerType*>(lt)->getBitWidth(),rbw=static_cast<IntegerType*>(rt)->getBitWidth();
    if(lbw>rbw){
      rv=builder->CreateSExt(rv,lt,"gte_int_ext");
    }else if(lbw<rbw){
      lv=builder->CreateSExt(lv,rt,"gte_int_ext");
    }
    res=builder->CreateICmpSGE(lv,rv,"gte_int_res");
  }else if(lt->isFloatingPointTy()){
    if(!rt->isFloatingPointTy()){
      error("trying to gte a float with a non float");
    }
    if(lt->isDoubleTy()){
      if(rt->isFloatTy()){
        rv=builder->CreateFPCast(rv,lt,"gte_float_ext");
      }
    }else if(rt->isDoubleTy()){
      lv=builder->CreateFPCast(lv,rt,"gte_float_ext");
    }
    res=builder->CreateFCmpOGE(lv,rv,"gte_result");
  }else if(lt->isPointerTy()){
    if(!rt->isPointerTy()){
      error("trying to gte a ptr with a non ptr");
    }
    res=builder->CreateICmpUGE(lv,rv,"gte_ptr_res");
  }
  builder->CreateStore(builder->CreateZExt(res,Type::getInt8Ty(*ctx)),vv);
}

void parseIs(string a){
  string ss=subStrTo(a,' ');
  if(ss.empty())error("argument missing in is");
  string vs=subStrTo(a,' ',ss.length()+1);
  if(vs.empty())error("destination var missing in is");
  if(vs.at(0)!='v')error("destination is no variable in is");
  Value* sv=getSomethingValue(ss);
  Type* st=sv->getType();
  Value* vv=getVarRef(vs,"i8");
  Value* res;
  if(st->isIntegerTy()){
    res=builder->CreateICmpNE(Constant::getNullValue(st),sv,"is_int_res");
  }else if(st->isFloatingPointTy()){
    res=builder->CreateFCmpONE(Constant::getNullValue(st),sv,"is_float_res");
  }else if(st->isPointerTy()){
    res=builder->CreateICmpNE(Constant::getNullValue(st),sv,"is_ptr_res");
  }else if(st->isArrayTy()||st->isStructTy()){
    res=ConstantInt::get(Type::getInt8Ty(*ctx),1);
  }
  builder->CreateStore(builder->CreateZExt(res,Type::getInt8Ty(*ctx)),vv);
}

void parseBnot(string a){
  string ss=subStrTo(a,' ');
  if(ss.empty())error("argument missing in bnot");
  string vs=subStrTo(a,' ',ss.length()+1);
  if(vs.empty())error("destination var missing in bnot");
  if(vs.at(0)!='v')error("destination is no variable in bnot");
  Value* sv=getSomethingValue(ss);
  Type* st=sv->getType();
  if(!st->isIntegerTy()){error("trying to bnot a non int");return;}
  Value* vv=getVarRef(vs,getTypeS(st));
  Value* res=builder->CreateXor(sv,ConstantInt::get(st,-1),"bnot_res");
  builder->CreateStore(res,vv);
}

void parseNot(string a){
  string ss=subStrTo(a,' ');
  if(ss.empty())error("argument missing in not");
  string vs=subStrTo(a,' ',ss.length()+1);
  if(vs.empty())error("destination var missing in not");
  if(vs.at(0)!='v')error("destination is no variable in not");
  Value* sv=getSomethingValue(ss);
  Type* st=sv->getType();
  Value* vv=getVarRef(vs,"i8");
  Value* res;
  if(st->isIntegerTy()){
    res=builder->CreateICmpEQ(Constant::getNullValue(st),sv,"not_int_res");
  }else if(st->isFloatingPointTy()){
    res=builder->CreateFCmpOEQ(Constant::getNullValue(st),sv,"not_float_res");
  }else if(st->isPointerTy()){
    res=builder->CreateICmpEQ(Constant::getNullValue(st),sv,"not_ptr_res");
  }else if(st->isArrayTy()||st->isStructTy()){
    res=ConstantInt::get(Type::getInt8Ty(*ctx),0);
  }
  builder->CreateStore(builder->CreateZExt(res,Type::getInt8Ty(*ctx)),vv);
}

void parseAnd(string a){
  string ls=subStrTo(a,' ');
  if(ls.empty())error("lefthand missing in and");
  string rs=subStrTo(a,' ',ls.length()+1);
  if(rs.empty())error("righthand missing in and");
  string vs=subStrTo(a,' ',ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in and");
  if(vs.at(0)!='v')error("destination is no variable in and");
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  Type* lt=lv->getType();
  Type* rt=rv->getType();
  if(!(lt->isIntegerTy()&&rt->isIntegerTy())){error("trying to and two values of which at least one is not an int");return;}
  unsigned lbw=static_cast<IntegerType*>(lt)->getBitWidth(),rbw=static_cast<IntegerType*>(rt)->getBitWidth();
  if(lbw>rbw){
    rv=builder->CreateSExt(rv,lt,"and_ext");
  }else if(lbw<rbw){
    lv=builder->CreateSExt(lv,rt,"and_ext");
  }
  Value* res=builder->CreateAnd(lv,rv,"and_res");
  Value* vv=getVarRef(vs,"i"+to_string(lbw>rbw?lbw:rbw));
  builder->CreateStore(res,vv);
}

void parseOr(string a){
  string ls=subStrTo(a,' ');
  if(ls.empty())error("lefthand missing in or");
  string rs=subStrTo(a,' ',ls.length()+1);
  if(rs.empty())error("righthand missing in or");
  string vs=subStrTo(a,' ',ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in or");
  if(vs.at(0)!='v')error("destination is no variable in or");
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  Type* lt=lv->getType();
  Type* rt=rv->getType();
  if(!(lt->isIntegerTy()&&rt->isIntegerTy())){error("trying to or two values of which at least one is not an int");return;}
  unsigned lbw=static_cast<IntegerType*>(lt)->getBitWidth(),rbw=static_cast<IntegerType*>(rt)->getBitWidth();
  if(lbw>rbw){
    rv=builder->CreateSExt(rv,lt,"or_ext");
  }else if(lbw<rbw){
    lv=builder->CreateSExt(lv,rt,"or_ext");
  }
  Value* res=builder->CreateOr(lv,rv,"or_res");
  Value* vv=getVarRef(vs,"i"+to_string(lbw>rbw?lbw:rbw));
  builder->CreateStore(res,vv);
}

void parseInp(string a){
  string ts=subStrTo(a,' ');
  if(ts.empty())error("type missing in inp");
  string vs=subStrTo(a,' ',ts.length()+1);
  if(vs.empty())error("destination missing in inp");
  if(vs.at(0)!='v')error("destination is no variable in inp");
  Type* t=getType(ts);
  Value* inp=getLine();
  Value* inpP=createEntryAlloca(actFn,inp->getType(),"inp_inpP");
  builder->CreateStore(inp,inpP);
  Value* idcs[]={Constant::getNullValue(Type::getInt64Ty(*ctx)),Constant::getNullValue(Type::getInt32Ty(*ctx))};
  Value* dataPP=builder->CreateGEP(inp->getType(),inpP,idcs,"inp_dataPP");
  Value* dataP=builder->CreateLoad(Type::getInt8PtrTy(*ctx),dataPP);
  Value* vv=getVarRef(vs,ts);
  if(t->isIntegerTy()){
    Value* args[]={dataP,Constant::getNullValue(PointerType::getUnqual(Type::getInt8PtrTy(*ctx))),ConstantInt::get(Type::getInt32Ty(*ctx),10)};
    Value* lVal=builder->CreateCall(strtolFn,args);
    Value* val=builder->CreateTrunc(lVal,t,"inp_truncIntInp");
    builder->CreateStore(val,vv);
  }else if(t->isFloatingPointTy()){
    Value* args[]={dataP,Constant::getNullValue(PointerType::getUnqual(Type::getInt8PtrTy(*ctx)))};
    Value* dVal=builder->CreateCall(strtodFn,args);
    Value* val=builder->CreateFPCast(dVal,t,"inp_castFPInp");
    builder->CreateStore(val,vv);
  }
  Value* args1[]={inpP};
  builder->CreateCall(getDynArrIR("darr(i8)").destroy,args1);
}

void parseInpS(string a){
  string vs=subStrTo(a,' ');
  if(vs.empty())error("destination missing in inpS");
  if(vs.at(0)!='v')error("destination is no variable in inp");
  Value* inp=getLine();
  Value* vv=getVarRef(vs,"darr(i8)");
  builder->CreateStore(inp,vv);
}

void parseLen(string a){
  string ss=subStrTo(a,' ');
  if(ss.empty())error("arg missing in len");
  string vs=subStrTo(a,' ',ss.length()+1);
  if(vs.empty())error("destination missing in len");
  if(vs.at(0)!='v')error("destination is no variable in len");
  Value* sv=getSomethingValue(ss);
  Type* t=sv->getType();
  Value* vv=getVarRef(vs,"u64");
  Value* res;
  if(t->isStructTy()){
    auto st=static_cast<StructType*>(t);
    unsigned ne=st->getNumElements();
    if(st->getElementType(ne-1)->isIntegerTy(1))
      res=dynArrLen(sv);
    else
      res=ConstantInt::get(Type::getInt64Ty(*ctx),ne-1);
  }else if(t->isArrayTy())
    res=ConstantInt::get(Type::getInt64Ty(*ctx),static_cast<ArrayType*>(t)->getNumElements());
  builder->CreateStore(res,vv);
}

void parseSplice(string a){
  string ss=subStrTo(a,' ');
  if(ss.empty())error("source missing in splice");
  string ls=subStrTo(a,' ',ss.length()+1);
  if(ls.empty())error("start missing in splice");
  string rs=subStrTo(a,' ',ss.length()+1+ls.length()+1);
  if(rs.empty())error("len missing in splice");
  string vs=subStrTo(a,' ',ss.length()+1+ls.length()+1+rs.length()+1);
  if(vs.empty())error("destination var missing in splice");
  if(vs.at(0)!='v')error("destination is no variable in splice");
  Value* sv=getSomethingValue(ss);
  Value* lv=getSomethingValue(ls);
  Value* rv=getSomethingValue(rs);
  if(!(lv->getType()->isIntegerTy()&&rv->getType()->isIntegerTy()))error("start or len are not ints in splice");
  Type* st=sv->getType();
  if(st->isArrayTy()){
    rv=builder->CreateSExtOrTrunc(rv,Type::getInt64Ty(*ctx));
    ArrayType* sat=static_cast<ArrayType*>(st);
    Type* sst=sat->getElementType();
    dynArrIR dair=getDynArrIR("darr("+getTypeS(sst)+")");
    Value* vv=getVarRef(vs,dair.typeString);
    Value* args[]={vv,rv};
    builder->CreateCall(dair.resize,args);
    Value* idcs[]={Constant::getNullValue(Type::getInt64Ty(*ctx)),Constant::getNullValue(Type::getInt32Ty(*ctx))};
    Value* vvDataPP=builder->CreateGEP(dair.type,vv,idcs,"splice_arr_destDataPP");
    idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
    Value* vvLenP=builder->CreateGEP(dair.type,vv,idcs,"splice_arr_destLenP");
    builder->CreateStore(rv,vvLenP);
    Value* vvDataP=builder->CreateLoad(PointerType::getUnqual(dair.subType),vvDataPP,"splice_arr_destDataP");
    Value* svP=createEntryAlloca(actFn,st,"splice_arr_srcP");
    builder->CreateStore(sv,svP);
    idcs[1]=builder->CreateSExtOrTrunc(lv,Type::getInt64Ty(*ctx));
    Value* svDataP=builder->CreateGEP(st,svP,idcs,"splice_arr_srcDataP");
    Value* args1[]={builder->CreateBitCast(vvDataP,Type::getInt8PtrTy(*ctx)),
                    builder->CreateBitCast(svDataP,Type::getInt8PtrTy(*ctx)),
                    builder->CreateMul(rv,getTypeSize(dair.subType,builder->GetInsertBlock()),"splice_arr_bytes2move")};
    builder->CreateCall(memmoveFn,args1);
    return;
  }else if(st->isStructTy()){
    StructType* sst=static_cast<StructType*>(st);
    if(sst->getElementType(sst->getNumElements()-1)->isIntegerTy(1)){
      rv=builder->CreateSExtOrTrunc(rv,Type::getInt64Ty(*ctx));
      dynArrIR dair=getDynArrIRByType(st);
      Type* sst=dair.subType;
      Value* vv=getVarRef(vs,dair.typeString);
      Value* args[]={vv,rv};
      builder->CreateCall(dair.resize,args);
      Value* svP=createEntryAlloca(actFn,st,"splice_darr_srcP");
      builder->CreateStore(sv,svP);
      Value* idcs[]={Constant::getNullValue(Type::getInt64Ty(*ctx)),Constant::getNullValue(Type::getInt32Ty(*ctx))};
      Value* vvDataPP=builder->CreateGEP(dair.type,vv,idcs,"splice_darr_destDataPP");
      Value* vvDataP=builder->CreateLoad(PointerType::getUnqual(dair.subType),vvDataPP,"splice_darr_destDataP");
      Value* svDataPP=builder->CreateGEP(st,svP,idcs,"splice_darr_srcDataPP");
      Value* svDataP=builder->CreateLoad(PointerType::getUnqual(dair.subType),svDataPP,"splice_darr_srcDataP");
      idcs[1]=ConstantInt::get(Type::getInt32Ty(*ctx),1);
      Value* vvLenP=builder->CreateGEP(dair.type,vv,idcs,"splice_arr_destLenP");
      builder->CreateStore(rv,vvLenP);
      Value* idcs1[]={lv};
      Value* svDataPOff=builder->CreateGEP(dair.subType,svDataP,idcs1,"splice_darr_srcDataPOff");
      Value* args1[]={builder->CreateBitCast(vvDataP,Type::getInt8PtrTy(*ctx)),
                      builder->CreateBitCast(svDataPOff,Type::getInt8PtrTy(*ctx)),
                      builder->CreateMul(rv,getTypeSize(dair.subType,builder->GetInsertBlock()),"splice_darr_bytes2move")};
      builder->CreateCall(memmoveFn,args1);
      return;
    }
  }
  error("trying to splice a non array or darr");
}

void parseLine(string line){
  if(line.length()==0||line.at(0)=='#')return;
  if(DEBUGLVL>=1)cout<<"Parsing line: "<<line<<endl;
  string op=subStrTo(line,' ');
  string rest=line.length()>op.length()?line.substr(op.length()+1):"";
  if(op=="nop")return;
  else if(op=="str")parseStr(rest);
  else if(op=="prt")parsePrt(rest);
  else if(op=="prtS")parsePrtS(rest);
  else if(op=="strGlob")parseStrGlob(rest);
  else if(op=="beginScope")vars.push_back(map<string,varInfo>());
  else if(op=="endScope")endScope();
  else if(op=="cast")parseCast(rest);
  else if(op=="getPtr")parseGetPtr(rest);
  else if(op=="getAt")parseGetAt(rest);
  else if(op=="append")parseAppend(rest);
  else if(op=="pop")parsePop(rest);
  else if(op=="popLast")parsePopLast(rest);
  else if(op=="insert")parseInsert(rest);
  else if(op=="setAt")parseSetAt(rest);
  else if(op=="lbl")parseLbl(rest);
  else if(op=="jmp")parseJmp(rest);
  else if(op=="jmpif")parseJmpif(rest);
  else if(op=="def")parseDef(rest);
  else if(op=="ret")parseRet(rest);
  else if(op=="exit")parseExit(rest);
  else if(op=="call")parseCall(rest);
  else if(op=="add")parseAdd(rest);
  else if(op=="sub")parseSub(rest);
  else if(op=="mul")parseMul(rest);
  else if(op=="div")parseDiv(rest);
  else if(op=="destroy")parseDestroy(rest);
  else if(op=="eq")parseEq(rest);
  else if(op=="gt")parseGt(rest);
  else if(op=="gte")parseGte(rest);
  else if(op=="is")parseIs(rest);
  else if(op=="bnot")parseBnot(rest);
  else if(op=="not")parseNot(rest);
  else if(op=="and")parseAnd(rest);
  else if(op=="or")parseOr(rest);
  else if(op=="inp")parseInp(rest);
  else if(op=="inpS")parseInpS(rest);
  else if(op=="len")parseLen(rest);
  else if(op=="splice")parseSplice(rest);
  else error("unknown opcode "+op);
}

void mainLoop(string code){
  unsigned pos=0;
  vector<Type*> mainArgTypes;
  mainArgTypes.push_back(Type::getInt32Ty(*ctx));
  mainArgTypes.push_back(PointerType::getUnqual(Type::getInt8PtrTy(*ctx)));
  FunctionType* ft=FunctionType::get(Type::getInt32Ty(*ctx),mainArgTypes,false);
  Function* f=Function::Create(ft,Function::ExternalLinkage,"main",mdl.get());
  f->args().begin()[0].setName("argc");
  f->args().begin()[1].setName("argv");
  mainBB=BasicBlock::Create(*ctx,"entry",f);
  actFn=f;
  builder->SetInsertPoint(mainBB);
  vars.push_back(map<string,varInfo>()); // global vars
  vars.push_back(map<string,varInfo>()); // main vars
  while(pos<code.length()){
    string line=subStrTo(code,'\n',pos);
    parseLine(line);
    pos+=line.length()+1;
  }
  builder->CreateRet(Constant::getNullValue(Type::getInt32Ty(*ctx)));
  verifyFunction(*f);
  fpm->run(*f);
}

int main(int argc,char const *argv[]){
  string code;
  string ifName="";
  string ofName="out/out.ll";
  bool srcIsInter=false;
  for(int i=1;i<argc;i++){
    string arg=string(argv[i]);
    if(arg.at(0)=='-'){
      if(arg.at(1)=='h'){return -1;} // TODO: help screen
      if(arg.at(1)=='d')DEBUGLVL=stoi(arg.substr(2));
      else if(arg.at(1)=='o')ofName=arg.substr(2);
      else if(arg.at(1)=='i')srcIsInter=true;
    }else{
      ifName=arg;
    }
  }
  if(ifName==""){
    cout<<"Error: No input file provided!"<<endl;
    return -1;
  }
  if(srcIsInter){
    ifstream f(ifName);
    string buf;
    while(f){
      getline(f,buf);
      code+=buf+"\n";
    }
  }else{
    unsigned ec;
    code=midi2code(ifName,&ec,DEBUGLVL);
  }
  
  if(DEBUGLVL>=1){cout <<"Intermediary code:\n\n" << code << endl;}
  
  initModule();
  
  mainLoop(code);
  
  string out;
  raw_string_ostream os(out);
  os << *mdl;
  os.flush();
  
  if(exitCode)return exitCode;
  
  ofstream of(ofName);
  if(of.is_open()){
    of << out << "\n";
    of.close();
  }else{
    fprintf(stderr,"Could not open output file!\n");
    return -1;
  }
  
  return exitCode;
}
