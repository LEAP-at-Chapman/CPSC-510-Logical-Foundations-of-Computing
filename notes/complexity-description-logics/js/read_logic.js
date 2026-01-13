function checkedindex(radiobaton)
{ for(var i=0; i<radiobaton.length; i++)
  { if(radiobaton[i].checked) return i; }
}

function checkedvalue(radiobaton)
{ return radiobaton[checkedindex(radiobaton)].value;
}

var Dunno='<span style=\"font-family:Times New Roman;font-size:16pt\" '+
          'title=\"I do not know... If you know, send me a mail! (see below)\">&#9786;</span>';
var sAND='<span class=little>&and;</span>';
var SPACE = '&nbsp;';

// ########################################################

var // Boolean variables for checkboxes

Func     = false;           // Concept constructions:
NRestr   = false;
QNRestr  = false;
Nominals = false;

RInver= false;              // Role constructions:

RInter= false;
RUnion= false;
RCompl= false;
RComplAtomic=false;
RComplFull=false;
RCompo= false;
RStar = false;
idC   = false;

BRinN = false;

AxTrans  = false;           // Additional axioms
AxHierar = false;
AxCRI    = false; // Complex Role Inclusions
AxMisc   = false; // Reflexivity, Irreflexivity, etc.

EmptyTB = "NoTBox";         // TBox options
AcyclTB = "AcyclicTBox";
CycleTB = "GeneralTBox";
InterTB = "InternalizedTBox";

TBoxOption=EmptyTB;

TBoxIsEmpty=false;
TBoxIsAcycl=false;
TBoxIsCycle=false;

MuOper=false;               // Miscellaneous
RVMaps=false;
FAgree=false;

//----------------------------
function ReadInput() // Read the form into the boolean variables
{
 with(document.LogicForm)
 {
                                 // Concept constructions:
  Func     = F.checked;
  NRestr   = N.checked;
  QNRestr  = Q.checked;
  Nominals = O.checked;

                                 // Role constructions:
  RInver = Inverses.checked;

  RInter = Intersect.checked;
  RUnion = Union.checked;
  RCompl = Complement.checked;
  RComplAtomic = (NegType.selectedIndex==1); // "as is" value, to
  RComplFull   = (NegType.selectedIndex==0); // be adjusted later
  RCompo = Chain.checked;
  RStar  = Kleene.checked;
  idC    = Identity.checked;

  BRinN = (ROpInN.selectedIndex==1);

                                // Additional axioms
  AxTrans  = Transitivity.checked;
  AxHierar = Hierarchy.checked;
  AxCRI    = ComplRoleIncl.checked;
  AxMisc   = OtherStuff.checked;

  TBoxOption = checkedvalue(TBoxOpt);

                               // Miscellaneous
  MuOper = MuOperator.checked;
//  RVMaps = RoleVMaps.checked;
//  FAgree = Agreement.checked;
 }
}


var        // Create integer variables (Logic Determinators)

SS = 0;
HH = 0;
II = 0;
OO = 0;

RR = 0; // Complex Role Inclusions
KK = 0; // Refl, Irrefl, Disj, etc.

MM = 0; // Mu-operator
RV = 0; // Role value maps
CC = 0; // Chain (dis)agreement

RCap = 0;
RCup = 0;
RNeg = 0;
RNegA= 0;
RNegF= 0;
RCrc = 0;
RStr = 0;
RIdC = 0;

RinN = 0;   // Role operations allowed in scope of number restrictions

SH =0;      // ALC=0; S=1; ALCH=2; SH=3;
IO =0;      // None=0; I=1; O=2; IO=3;
FNQ=0;      // None=0; F=1; N=2; Q=3; They form a tower: F < N < Q
ROpers = 0; // (Roper=0..63) Cap=1; Cup=2; Neg=4; Composition=8; Star=16; id=32;
Misc=0;     // MuOper=1; RVMaps=2; FAgree=4;

trans=26;   // cup + o + *
reg=58;     // trans + id

//----------------------------
function InitVars() // Initialize integer variables, and adjust "as is" values
{

 SS = (AxTrans?  1:0);
 HH = (AxHierar? 1:0);
 II = (RInver?   1:0);
 OO = (Nominals? 1:0);

 RR = (AxCRI?    1:0);
 KK = (AxMisc?   1:0);

//--------------------
 MM = (MuOper?   1:0);
 RV = (RVMaps?   1:0);
 CC = (FAgree?   1:0);
//--------------------
 RCap = (RInter? 1:0);
 RCup = (RUnion? 1:0);
 RNeg = (RCompl? 1:0);

           // If we have Cap and Cup and no other operators, then Atomic->Full:
 var RCF = RComplFull || (RComplAtomic && RInter && RUnion && !RCompo && !RStar && !idC);

 RNegA= (RCompl && !RCF)? 1:0;
 RNegF= (RCompl &&  RCF)? 1:0;
 RCrc = (RCompo? 1:0);
 RStr = (RStar?  1:0);
 RIdC = (idC?    1:0);
 RinN = (BRinN?  1:0);

                     // Aggregated variables, using binary bits
 SH     = SS + 2*HH;
 IO     = II + 2*OO;
 FNQ    = QNRestr? 3: (NRestr? 2: (Func? 1:0) );
 ROpers = RCap + 2*RCup + 4*RNeg + 8*RCrc + 16*RStr + 32*RIdC;
 Misc   = MM + 2*CC + 4*CC;

 TBoxIsEmpty = (TBoxOption==EmptyTB) || (TBoxOption==InterTB);
 TBoxIsAcycl = (TBoxOption==AcyclTB) || (TBoxOption==InterTB);
 TBoxIsCycle = (TBoxOption==CycleTB) || (TBoxOption==InterTB);
}

// ########################################################

// The next 3 functions do NOT take into account MuOper, RVMAps, FAgree!

function Logic(iSH,iIO,iFNQ,iROpers)
{
 return ((SH==iSH) && (IO==iIO) && (FNQ==iFNQ) && (ROpers==iROpers));
}

function LogicInterval(SH1,IO1,FNQ1,ROpers1,SH2,IO2,FNQ2,ROpers2)
{
 return ( SH1 <= SH && IO1 <= IO && FNQ1 <= FNQ && ROpers1 <=ROpers &&
          SH2 >= SH && IO2 >= IO && FNQ2 >= FNQ && ROpers2 >=ROpers );
}

function LogicBetween(S1,H1,I1,O1,FNQ1,Cap1,Cup1,Neg1,Circ1,Star1,Id1,
                      S2,H2,I2,O2,FNQ2,Cap2,Cup2,Neg2,Circ2,Star2,Id2)
{
 return ( S1<=SS && H1<=HH && I1<=II && O1<=OO && FNQ1<=FNQ &&
          S2>=SS && H2>=HH && I2>=II && O2>=OO && FNQ2>=FNQ &&
  Cap1<=RCap && Cup1<=RCup && Neg1<=RNeg && Circ1<=RCrc && Star1<=RStr && Id1<=RIdC &&
  Cap2>=RCap && Cup2>=RCup && Neg2>=RNeg && Circ2>=RCrc && Star2>=RStr && Id2>=RIdC );
}
