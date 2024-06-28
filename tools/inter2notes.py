import sys
from random import randint as ri
from random import choice,seed,random
from midiutil.MidiFile import MIDIFile

#seed(1)

if len(sys.argv)<3:
  print("input or output file missing")
  exit()
f=open(sys.argv[1])
code=[i.replace("\n","") for i in f.readlines()]
code=filter(lambda s:len(s)>0 and not(s.startswith("#")),code)
code=[i.split(" ") for i in code]
#print(code)

f=open("../src/opsNew.csv","r")
ops=[i.replace("\n","").replace("R\"(","").replace(")\"","").split(";") for i in f.readlines()]
f.close()
#print("\n".join("#".join(i) for i in ops))
opsRev={}
for i in range(len(ops)):
  opsRev[ops[i][0]]=i
#print(opsRev)

f=open("types.txt","r")
types_=[j for j in filter(lambda i:len(i)!=0,[i.replace("\n","") for i in f.readlines()])]
f.close()
types={}
for i in types_:
  types[i]=[]
for i in range(len(types_)):
  types[types_[i]].append(i)
#print(types)

vars=[]
lbls=[]

def getType(arg,vel=0):
  if arg.startswith("i") or arg.startswith("f"):
    return [(choice(types[arg]),vel)]
  elif arg.startswith("p"):
    return [(choice(types["ptr"]),vel)]+getType(arg[4:-1])
  elif arg.startswith("d"):
    return [(choice(types["darr"]),vel)]+getType(arg[5:-1])
  elif arg.startswith("a"):
    lParanIdx=arg.find("(")
    return [(choice(types["arr"]),vel),(int(arg[4:lParanIdx]),1)]+getType(arg[lParanIdx+1:-1])
  elif arg.startswith("c"):
    subTypes=arg[5:-2].split(",")
    subTypeTks=[]
    for i in subTypes:
      subTypeTks+=getType(i)
    return [(choice(types["coll"]),vel),(0,3)]+subTypeTks+[(0,4)]

def getVar(arg,velImp):
  idx=len(vars)
  if arg in vars:
    idx=vars.index(arg)
  else:
    vars.append(arg)
  return [(idx,1 if velImp else 0)]

def getLit(arg,velImp):
  tv=arg[1:-1].split("[",1)
  type,val=tv[0],tv[1]
  typeTks=getType(type,2 if velImp else 0)
  if type.startswith("i"):
    return typeTks+[(int(val),1)]
  if type.startswith("f"):
    l,r=0,""
    if "." in val:
      lr=val.split(".")
      l=int(lr[0])
      r=lr[1]
    else:
      l=int(val)
    return typeTks+[(l,1),(r,5)]
  if type.startswith("p") or type.startswith("a") or type.startswith("d"):
    return typeTks
  if type.startswith("c"):
    subVals=[]
    paranLvls=[0,0,0] # (,[,{
    startP,p=0,0
    while p<len(val):
      if val[p]=="(":
        paranLvls[0]+=1
      elif val[p]==")":
        paranLvls[0]-=1
      elif val[p]=="[":
        paranLvls[1]+=1
      elif val[p]=="]":
        paranLvls[1]-=1
      elif val[p]=="{":
        paranLvls[2]+=1
      elif val[p]=="}":
        paranLvls[2]-=1
      elif val[p]==",":
        if sum(paranLvls)==0:
          actSubValS=val[startP:p]
          subVals+=getVar(actSubValS,True) if actSubValS[0]=="v" else getLit(actSubValS,True)
          startP=p+1
      p+=1
    return typeTks+[(0,3)]+subVals+[(0,4)]

def getLbl(arg):
  idx=len(lbls)
  if arg in lbls:
    idx=lbls.index(arg)
  else:
    lbls.append(arg)
  return [(idx,0)]

# tokens will be stored as (val,info) where val is the numeric value needed and info is 1=eq vels, 2=sim vels, 0=vels unimportant, 3=collStart, 4=collEnd, 5=floatDec
tks=[]
for i in code:
  op=i[0]
  opN=opsRev[op]
  tks.append((opN,0))
  opD=ops[opN]
  #print(opD,"#",i)
  for j in range(1,len(opD)):
    arg=i[j]
    kind=opD[j]
    if kind=='t':
      tks+=getType(arg)
    elif kind=='v':
      tks+=getVar(arg,False)
    elif kind=='l':
      tks+=getLit(arg,False)
    elif kind=='a':
      tks+=getLbl(arg)
    elif kind=='s':
      tks+=(getVar(arg,True) if arg[0]=='v' else getLit(arg,True))
#print(tks)

notes=[] # [(pitch,vel),...]
collOpenings=[] # [pitch,...]
for i in tks:
  if i[1]==5:
    openClosePitch=ri(1,126)
    while openClosePitch in range(60,70) or openClosePitch in collOpenings:
      openClosePitch=ri(1,126)
    notes.append((openClosePitch,ri(1,127)))
    for j in i[0]:
      notes.append((60+int(j),ri(1,127)))
    notes.append((openClosePitch,ri(1,127)))
  if i[1]==3:
    pitch=ri(1,126)
    while pitch in collOpenings:
      pitch=ri(1,126)
    collOpenings.append(pitch)
    notes.append((pitch,ri(1,127)))
  if i[1]==4:
    notes.append((collOpenings[-1],ri(1,127)))
    collOpenings.pop()
  if i[1] in (0,1,2):
    finalDataPitch=(i[0]%67+60) if i[0]>=0 else 60-(abs(i[0])%60)
    openClosePitch=ri(1,126)
    while openClosePitch==finalDataPitch or openClosePitch in collOpenings:
      openClosePitch=ri(1,126)
    openVel=ri(1,127)
    notes.append((openClosePitch,openVel))
    if i[0]>=0:
      notes+=[(127,ri(1,127)) for j in range(i[0]//67)]
      #for j in range:
      #  actPitch=ri(1,126)
      #  while actPitch==openClosePitch or actPitch in collOpenings:
      #    actPitch=ri(1,126)
      #  notes.append((actPitch,ri(1,127)))
    else:
      notes+=[(0,ri(1,127)) for j in range(abs(i[0])//60)]
    notes.append((finalDataPitch,ri(1,127)))
    closeVel=ri(1,127) if i[1]==0 else openVel
    while i[1]==2 and closeVel==openVel:
      closeVel=ri(1,127)
    notes.append((openClosePitch,closeVel))
#print(notes)

mf=MIDIFile(1)
track,time,channel,duration=0,0,0,random()*1.999+.001
mf.addTempo(track,time,ri(60,300))
for i in notes:
  mf.addNote(track,channel,i[0],time,duration,i[1])
  time+=duration
  duration=random()*1.999+.001

f=open(sys.argv[2],"wb")
mf.writeFile(f)
f.close()
