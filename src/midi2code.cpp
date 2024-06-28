#include "midi2code.h"

using namespace std;
using namespace smf;

#define VEL_THRESH 0

int debugLvl;

const char* dictS={
#include "opsNew.csv"
};

vector<string> split(string s,string del){
  vector<string> ret;
  if(del.length()==0){
    for(unsigned i=0;i<s.length();i++){
      ret.push_back(string(1,s.at(i)));
    }
    return ret;
  }
  int prevI=-1;
  for(unsigned i=0,delI=0;i<s.length();i++){
    if(del.at(delI)!=s.at(i)){
      delI=0;
      continue;
    }
    delI++;
    if(delI==del.length()){
      ret.push_back(s.substr(prevI+1,i-delI-prevI));
      delI=0;
      prevI=i;
    }
  }
  ret.push_back(s.substr(prevI+1));
  return ret;
}

vector<string> Dict;
int dictSize;

const string types[]={"i8","i8","i16","i16","i32","i32","i64","i64","i64","i64","f32","f64","arr","arr","darr","darr","ptr","ptr","coll","coll","i8","i16","i32","i64","f32","f64","darr","ptr","coll"}; // length=29
const int typesLen=sizeof(types)/sizeof(string); // has to be int because we will later do int%typesLen

typedef struct{
  int note;
  unsigned vel;
} Note;

enum class compareChordsReturn:unsigned char{
  EQ=0,SIM=1,DIF=2
};

enum class CompileError:unsigned{
  OK,openingOpNoClose,notEnoughArguments
};

compareChordsReturn compareChords(vector<Note> c1,vector<Note> c2,unsigned velThresh){
  compareChordsReturn ret{compareChordsReturn::EQ};
  int min1=0xFF,min2=0xFF;
  float velSum1=0,velSum2=0;
  for(const Note& n1:c1){velSum1+=n1.vel;if(n1.note<min1)min1=n1.note;}
  for(const Note& n2:c2){velSum2+=n2.vel;if(n2.note<min2)min2=n2.note;}
  if(min1!=min2)return compareChordsReturn::DIF;
  velSum1/=c1.size();velSum2/=c2.size();
  return (velSum1>velSum2?velSum1-velSum2:(velSum2-velSum1))>velThresh?compareChordsReturn::SIM:compareChordsReturn::EQ;
}

typedef struct{
  CompileError error;
  compareChordsReturn compareChordsVal;
  int sum;
  unsigned end;
} TokenInfo;

TokenInfo getToken(vector<vector<Note>> notes,unsigned i,unsigned velThresh){
  if(debugLvl>=3){
    cout<<"entering getToken with i="<<i<<" and the following notes:\n";
    for(auto c=notes.begin()+i;c<notes.end();c++){for(const Note& n:*c)cout<<n.note<<","<<n.vel<<" ";cout<<";";}cout<<endl;
  }
  vector<Note> opOpen=notes[i]; // remember the opening chord
  i++;
  if(i==notes.size()){ // check that notes are left
    return TokenInfo{CompileError::openingOpNoClose,compareChordsReturn::EQ,0,0};
  }
  int sum=0;
  compareChordsReturn compareChordsVal;
  while((compareChordsVal=compareChords(opOpen,notes[i],velThresh))==compareChordsReturn::DIF){ // test if we already reached the closing chord
    for(const Note& n:notes[i])sum+=n.note; // sum up all notes
    i++;
    if(i==notes.size()){ // test if we miss a closing chord
      return TokenInfo{CompileError::openingOpNoClose,compareChordsReturn::EQ,0,0};
    }
  }
  if(debugLvl>=2)cout<<"exiting getToken with sum="<<sum<<" and i="<<i<<endl;
  return TokenInfo{CompileError::OK,compareChordsVal,sum,i};
}

bool startsWith(string s,string p){ // wrapper because I originally coded it in D and was too lazy to change all occurences of startsWith
  return 0==s.rfind(p,0);
}

typedef struct{
  CompileError error;
  string argStr;
} ArgRet;

ArgRet getArg_(vector<vector<Note>> notes,char mode,int* arglen);

ArgRet getArg(vector<vector<Note>> notes,char mode,int* arglen){
  ArgRet ret=getArg_(notes,mode,arglen);
  if(debugLvl>=1)cout<<ret.argStr<<endl;
  return ret;
}

ArgRet getArg_(vector<vector<Note>> notes,char mode,int* arglen){
  if(debugLvl>=2)printf("getArg with mode %c\n",mode);
  switch(mode){
  case 't':{ // type
    unsigned i=0;
    TokenInfo typeTk=getToken(notes,i,1000);
    if(typeTk.error==CompileError::openingOpNoClose){
      return ArgRet{CompileError::openingOpNoClose,""};
    }
    string type=types[(typeTk.sum%typesLen+typesLen)%typesLen];
    unsigned end=typeTk.end;
    *arglen=end+1;
    if(type=="coll"){
      string ret="coll{";
      TokenInfo typesTk=getToken(notes,*arglen,1000);
      if(typesTk.error==CompileError::openingOpNoClose){
        return ArgRet{CompileError::openingOpNoClose,""};
      }
      unsigned start=*arglen+1;
      *arglen=typesTk.end+1;
      while(start<typesTk.end){
        int len=0;
        ArgRet subTypeTk=getArg(vector<vector<Note>>(notes.begin()+start,notes.end()),'t',&len);
        if(subTypeTk.error!=CompileError::OK){
          return ArgRet{subTypeTk.error,""};
        }
        ret+=subTypeTk.argStr+",";
        start+=len;
      }
      ret+="}";
      return ArgRet{CompileError::OK,ret};
    }
    if(type=="arr"||type=="ptr"||type=="darr"){ // arr, ptr and darr come with specific type attached
      if(end+1==notes.size()){
        return ArgRet{CompileError::openingOpNoClose,""};
      }
    }else{
      return ArgRet{CompileError::OK,type};
    }
    string retStr=type;
    if(type=="arr"){
      TokenInfo lenTk=getToken(notes,end+1,VEL_THRESH); // if EQ, we want the length to be the sum of vels, if SIM, we want it to be the number of notes
      if(lenTk.error!=CompileError::OK)return ArgRet{lenTk.error,""};
      unsigned len=lenTk.compareChordsVal==compareChordsReturn::EQ?lenTk.sum:(lenTk.end-end-2);
      retStr+="!"+to_string(len);
      end=lenTk.end;
      if(end+1==notes.size()){
        return ArgRet{CompileError::openingOpNoClose,""};
      }
      *arglen=lenTk.end+1;
    }
    int subTypeTkLen=0;
    ArgRet subTypeTk=getArg(vector<vector<Note>>(notes.begin()+end+1,notes.end()),'t',&subTypeTkLen);
    if(subTypeTk.error!=CompileError::OK){
      return ArgRet{subTypeTk.error,""};
    }
    retStr+="("+subTypeTk.argStr+")";
    *arglen+=subTypeTkLen;
    return ArgRet{CompileError::OK,retStr};
    break;
  }case 'v':{ // variable
    TokenInfo varTk=getToken(notes,0,1000);
    if(varTk.error==CompileError::openingOpNoClose){
      return ArgRet{CompileError::openingOpNoClose,""};
    }
    *arglen=varTk.end+1;
    return ArgRet{CompileError::OK,"v"+to_string(varTk.sum)};
    break;
  }case 'a':{ // label
    TokenInfo labelTk=getToken(notes,0,1000);
    if(labelTk.error==CompileError::openingOpNoClose){
      return ArgRet{CompileError::openingOpNoClose,""};
    }
    *arglen=labelTk.end+1;
    return ArgRet{CompileError::OK,"a"+to_string(labelTk.sum)};
    break;
  }case 'l':{ // literal
    ArgRet typeTk=getArg(notes,'t',arglen);
    if(typeTk.error!=CompileError::OK){
      return ArgRet{typeTk.error,""};
    }
    string type=typeTk.argStr;
    if(startsWith(type,"i")||startsWith(type,"u")){
      TokenInfo valTk=getToken(notes,*arglen,VEL_THRESH);
      if(valTk.error==CompileError::openingOpNoClose){
        return ArgRet{CompileError::openingOpNoClose,""};
      }
      int val=valTk.compareChordsVal==compareChordsReturn::EQ?valTk.sum:valTk.end-*arglen-1;
      *arglen=valTk.end+1;
      return ArgRet{CompileError::OK,"l"+type+"["+to_string(val)+"]"};
    }
    if(startsWith(type,"f")){
      TokenInfo leftTk=getToken(notes,*arglen,VEL_THRESH);
      if(leftTk.error==CompileError::openingOpNoClose){
        return ArgRet{CompileError::openingOpNoClose,""};
      }
      int left=leftTk.compareChordsVal==compareChordsReturn::EQ?leftTk.sum:leftTk.end-*arglen-1;
      *arglen=leftTk.end+1;
      TokenInfo rightTk=getToken(notes,*arglen,1000);
      if(rightTk.error==CompileError::openingOpNoClose){
        return ArgRet{CompileError::openingOpNoClose,""};
      }
      string rightS="";
      for(unsigned i=*arglen+1;i<rightTk.end;i++){
        int sum=0;
        for(unsigned j=0;j<notes[i].size();j++){
          sum+=notes[i][j].note;
        }
        rightS+=to_string(sum%10);
      }
      *arglen=rightTk.end+1;
      return ArgRet{CompileError::OK,"l"+type+"["+to_string(left)+"."+rightS+"]"};
    }
    if(startsWith(type,"coll")){
      TokenInfo collTk=getToken(notes,*arglen,VEL_THRESH);
      if(collTk.error==CompileError::openingOpNoClose){
        return ArgRet{CompileError::openingOpNoClose,""};
      }
      string ret="l"+type+"[";
      int start=*arglen+1;
      *arglen=collTk.end+1;
      while(start<collTk.end){
        int len=0;
        ArgRet itemTk=getArg(vector<vector<Note>>(notes.begin()+start,notes.end()),'s',&len);
        if(itemTk.error!=CompileError::OK){
          return ArgRet{itemTk.error,""};
        }
        ret+=itemTk.argStr+",";
        start+=len;
      }
      ret+="]";
      return ArgRet{CompileError::OK,ret};
    }
    return ArgRet{CompileError::OK,"l"+type+((startsWith(type,"arr")||startsWith(type,"darr")||startsWith(type,"ptr"))?"[]":"")};
    break;
  }case 's':{
    TokenInfo vorlTk=getToken(notes,*arglen,VEL_THRESH);
    if(vorlTk.error==CompileError::openingOpNoClose){
      return ArgRet{CompileError::openingOpNoClose,""};
    }
    if(debugLvl>=2)printf("                 |--> is a %c",vorlTk.compareChordsVal==compareChordsReturn::EQ?'v':'l');
    return getArg_(notes,vorlTk.compareChordsVal==compareChordsReturn::EQ?'v':'l',arglen);
  }default:assert(0);
  }
  return ArgRet{CompileError::OK,""};
}

string midi2code(string filename,unsigned* exitStatus,int dl){
  debugLvl=dl;
  Dict=split(string(dictS),"\n");
  dictSize=Dict.size();
  
  MidiFile f;
  f.read(filename);
  f.joinTracks();
  vector<vector<Note>> notes;
  int prevTick=0;
  vector<Note> act;
  for(int i=0;i<f[0].size();i++){
    MidiEvent* mev=&f[0][i];
    if(mev->tick!=prevTick){
      prevTick=mev->tick;
      if(act.size()!=0){
        unsigned idx=notes.size();
        notes.push_back(vector<Note>());
        for(unsigned j=0;j<act.size();j++){
          Note actact={act[j].note,act[j].vel};
          notes[idx].push_back(actact);
        }
        act.clear();
      }
    }
    if(mev->size()!=3||(!((*mev)[0]>>4==9))||(*mev)[2]==0)continue;
    Note note={(*mev)[1]-60,(*mev)[2]};
    act.push_back(note);
  }
  if(act.size()>0)notes.push_back(act);
  
  if(debugLvl>=2){for(const vector<Note>& c:notes){for(const Note& n:c)cout<<n.note<<","<<n.vel<<" ";cout<<";";}cout<<endl;}
  
  // notes now contains all note pitches and vels, grouped by the time they are played
  // we will now build our intermediate code
  string code="";
  unsigned i=0;
  while(i<notes.size()){ // go through notes
    TokenInfo operationToken=getToken(notes,i,1000);
    if(operationToken.error!=CompileError::OK){
      *exitStatus=static_cast<unsigned>(operationToken.error);
      return "";
    }
    vector<string> operation=split(Dict[(operationToken.sum%dictSize+dictSize)%dictSize],";"); // we got the operation now
    code+=operation[0];
    if(debugLvl>=1){cout<<(operationToken.sum%dictSize+dictSize)%dictSize<<":"<<operation[0]<<endl;}
    i=operationToken.end+1;
    for(unsigned j=1;j<operation.size()&&operation[j]!="";j++){ // go through the arguments
      if(notes.size()==i){*exitStatus=static_cast<unsigned>(CompileError::notEnoughArguments);return "";}
      TokenInfo argTk=getToken(notes,i,operation[j]=="s"?VEL_THRESH:1000); // get the next argument token
      if(argTk.error==CompileError::openingOpNoClose){
        *exitStatus=static_cast<unsigned>(CompileError::openingOpNoClose);
        return "";
      }
      int arglen=0;
      ArgRet argRet=getArg(vector<vector<Note>>(notes.begin()+i,notes.end()),operation[j].at(0)=='s'?(argTk.compareChordsVal==compareChordsReturn::EQ?'v':'l'):operation[j].at(0),&arglen);
      if(argRet.error!=CompileError::OK){
        *exitStatus=static_cast<unsigned>(argRet.error);
        return "";
      }
      code+=" "+argRet.argStr;
      i+=arglen;
    }
    code+="\n";
  }
  *exitStatus=0;
  return code;
}

