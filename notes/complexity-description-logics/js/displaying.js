var  // Output strings

SATComplexity   ='';
SATComment      ='';
ABoxComplexity  ='';
ABoxComment     ='';

//QueryComplexity ='';
//QueryComment    ='';
//LDComplexity    ='';
//LDComment       ='';

TreeAnswer      ='';
TreeComment     ='';
FiniteAnswer    ='';
FiniteComment   ='';


var
PS='PSpace-complete';
EX='ExpTime-complete';
NE='NExpTime-complete';
UN='Undecidable';
DE='Decidable';
iPS='In&nbsp;PSpace';
iEX='In&nbsp;ExpTime';
iNE='In&nbsp;NExpTime';
hPS='PSpace-hard';
hEX='ExpTime-hard';
hNE='NExpTime-hard';
EEX='2-ExpTime-complete';

// ===============================================================================================

function ShowID(ID,iHTML)
{
 document.getElementById(ID).innerHTML=iHTML;
}


function DisplayResults()
{

 ShowID('ConcSatC',SATComplexity);
 ShowID('ConcSatR',SATComment);

 ShowID('ABoxConsC',ABoxComplexity);
 ShowID('ABoxConsR',ABoxComment);
/*
 ShowID('ConcrC',LDComplexity);
 ShowID('ConcrR',LDComment);

 ShowID('QueryC',QueryComplexity);
 ShowID('QueryR',QueryComment);
*/
 ShowID('FiniteC',FiniteAnswer);
 ShowID('FiniteR',FiniteComment);

 ShowID('TreeC',TreeAnswer);
 ShowID('TreeR',TreeComment);

}


// ===============================================================================================

function ShowComplexity()
{
 SATComplexity   = Dunno;
 SATComment      = SPACE;
 ABoxComplexity  = Dunno;
 ABoxComment     = SPACE;
/*
 QueryComplexity = Dunno;
 QueryComment    = SPACE;
 LDComplexity    = Dunno;
 LDComment       = SPACE;
*/

 TreeAnswer      = Dunno;
 TreeComment     = SPACE;
 FiniteAnswer    = Dunno;
 FiniteComment   = SPACE;


 ConceptSAT();
 ABoxConsistency();
// ConjunctiveQuery();
// ConceptSAT_LD();
 TreeModelProp();
 FiniteModelProp();

 DisplayResults();

}


// ########################################################

function LogicName()
{
var
 LogPrefix=
 (AxCRI? ((AxMisc? 's':'')+'R'):
 (AxTrans? 'S':'ALC') + (AxHierar? 'H':''));

 LogSuffix= ( Nominals? 'O':'' )+
            ( RInver?   'I':'' )+
            ( QNRestr?  'Q':(NRestr?'N':(Func?'F':'')));

 LogRoleOpers='';

 if(ROpers!=0 && MM==0)
 { // RInter RUnion RCompl RCompo RStar idC
   //   1      2      4      8     16    32

  if(ROpers==26) LogRoleOpers='<sub><i>trans</i></sub>';
  else
  {
   if(ROpers==58) LogRoleOpers='<sub><i>reg</i></sub>';
   else
   {
     var OperArray=new Array();

     if (RInter) OperArray[OperArray.length]='&cap;';
     if (RUnion) OperArray[OperArray.length]='&cup;';
     if (RCompo) OperArray[OperArray.length]='o';
     if (RCompl) OperArray[OperArray.length]='&not;'+
     ( document.LogicForm.NegType.disabled? '': (RComplFull? '(full)':'(atomic)') );
     if (RStar)  OperArray[OperArray.length]='*';
     if (idC)    OperArray[OperArray.length]='<i>id</i>';

    LogRoleOpers='(';
    for(var i=0;i<OperArray.length;i++)
    {
     LogRoleOpers+=OperArray[i]+((i+1<OperArray.length)? ",":"");
    }
    LogRoleOpers+=")";
   }
  }
 }

 return ( '<em>'+
  (MuOper? '&mu;':'')+
  LogPrefix + LogSuffix + '</em><sub>&nbsp;</sub>' +
  LogRoleOpers
//  +(RVMaps? ' + Role-value-maps':'')
//  +(FAgree? ' + \'\'same-as\'\'':'')
//  +( document.LogicForm.NegType.disabled? '':
//     ( '&nbsp;[role&nbsp;complement:&nbsp;'+ (RComplFull? 'full':'atomic') +']') )
  );

//  +( (document.LogicForm.ROpInN.disabled)? '':
//   ( '<br>[complex roles in num. restrictions:&nbsp;'+ (BRinN? 'allowed':'forbidden') +']') )

// if(!document.LogicForm.ROpInN.disabled)
// {
//  CRNRField
// }

}

function ShowLogic()
{
  ShowID('LogicChosen',LogicName());
  ShowID('CRNRField', ( document.LogicForm.ROpInN.disabled? '':'<sub><em>&nbsp;</em></sub><br>Complex roles in number restrictions are:') );
  ShowID('CRNRStatus',( document.LogicForm.ROpInN.disabled? '': ('<br>'+(BRinN? '<span style="color:green">allowed</span>':'<span style="color:red">forbidden</span>') ) ) );
}

var MuOperHasBeenBefore=false;
    CRIHasBeenBefore=false;

function CheckDependencies()
{
 with(document.LogicForm)
 {
   F.disabled = ( NRestr || QNRestr ); // More expressive constructs
   N.disabled = QNRestr;               // absorb weaker ones.

  if(RCompl && RComplFull)
  {
    if(RUnion) { Intersect.checked=true; RInter=true; } // Not only show adjusted checkboxes,
    if(RInter) {     Union.checked=true; RUnion=true; } // but also amend boolean variables!
  }

  if(MuOper)
  { // mu-ALC contains ALC_reg (but since we have no role operators EXPLICITLY,
    // there is no way to allow or forbid them in number restrictions).

    // Check and disable boxes: RUnion, RCompo, RStar, id(C). Adjust boolean variables.

      Union.checked = true;    Union.disabled = true; RUnion = true;
      Chain.checked = true;    Chain.disabled = true; RCompo = true;
     Kleene.checked = true;   Kleene.disabled = true;  RStar = true;
   Identity.checked = true; Identity.disabled = true;    idC = true;

    // For safety and simplicity, uncheck and disable the rest of role operators (except inverse).
    // Anyway, noone considered such logics.

  Intersect.checked = false;  Intersect.disabled = true; RInter = false;
 Complement.checked = false; Complement.disabled = true; RCompl = false;

    // Although this does not matter, but for transparent interface: disable "TRANS" and "REG" buttons.

     TransButton.disabled = true; 
       RegButton.disabled = true; 

    // Put the selector "RinN" into "Forbid" state (and disable it).

     ROpInN[0].selected = true;

     MuOperHasBeenBefore=true;

  }else{
   if(MuOperHasBeenBefore)
   {
    // Undo all the above (leaving unchanged the values of Intersect, Complement, RinN,
    // //////// and still disable RinN, even if it is enabled mistakenly by its own logic - before MuOp)
    
       Union.checked = false;    Union.disabled = false; RUnion = false;
       Chain.checked = false;    Chain.disabled = false; RCompo = false;
      Kleene.checked = false;   Kleene.disabled = false;  RStar = false;
    Identity.checked = false; Identity.disabled = false;    idC = false;
    
        Intersect.disabled = false;
       Complement.disabled = false;
    
      TransButton.disabled = false; 
        RegButton.disabled = false; 

       MuOperHasBeenBefore = false;
   }
  } // end of Mu

  if(AxCRI)
  {
     OtherStuff.disabled = false;

     // Complex role inclusions include "S" and "H"
     Transitivity.checked = true; AxTrans  = true; Transitivity.disabled = true;
        Hierarchy.checked = true; AxHierar = true;    Hierarchy.disabled = true;

     CRIHasBeenBefore=true;
  }
  else
  {
    if(CRIHasBeenBefore)
    {
      Transitivity.checked = false; AxTrans  = false;  Transitivity.disabled = false;
         Hierarchy.checked = false; AxHierar = false;  Hierarchy.disabled = false;

       OtherStuff.checked  = false;  AxMisc = false;
       OtherStuff.disabled = true;

      CRIHasBeenBefore=false;
    }
  }

  // The distinction of "atomic" and "full" negation makes sence when we have
  // role negation, any other role operation, but (???) it is not the case that we have
  // only negation, union and intersection (in this case "atomic"="full").

  NegType.disabled = !( RCompl && (RInter || RUnion ||  RCompo ||  RStar ||  idC));
                            // && !(RInter && RUnion && !RCompo && !RStar && !idC));

  ROpInN.disabled = MuOper || !( (Func || NRestr || QNRestr) &&
                                 (RInter || RUnion || RCompl || RCompo || RStar || idC) );

  // It is essential that this goes after "if(RCompl && RComplFull)"
  if((RInver && Nominals) || (AxTrans && AxHierar) || (RUnion && RStar) || MuOper)
  {
   TBoxOpt[0].disabled=true;
   TBoxOpt[1].disabled=true;
   TBoxOpt[2].disabled=true;
   ShowID('TBoxInternalize','<span style=\"font-weight:normal;font-size:12pt\"> is <i>internalizable</i> in extensions of '+
   ( (RInver && Nominals)? '<em>ALCIO</em>, see ['+Tobies2000+',&nbsp;Lemma&nbsp;4.12], ['+LutzImproved2004+',&nbsp;p.3]':
   ( (AxTrans && AxHierar)? '<em>SH</em>, see ['+HorrocksSattlerSHI1999+',&nbsp;'+HorrocksSattlerPract2000+'].':
   ( (MuOper)? '<em>&mu;ALC</em>, see ['+DeGiacomoLenzerini1997+',&nbsp;Theorem&nbsp;5].':
   ( (RUnion && RStar)? '<em>ALC</em>(&cup;,*), see ['+DLBook+',&nbsp;p.186].':'this mesg will never show!') ))) );
   TBoxOption=InterTB;
  }
  else
  {
   for (j=0;j<3;j++) TBoxOpt[j].disabled=false;
   ShowID('TBoxInternalize',':');
  }

 } // end of "with"
}

function CheckTrans()
{with(document.LogicForm)
 {
  Intersect.checked=false;
  Complement.checked=false;
  Union.checked=true;
  Chain.checked=true;
  Kleene.checked=true;
  Identity.checked=false;
 }
}

function CheckReg()
{ CheckTrans();
  document.LogicForm.Identity.checked=true;
}

function CheckOWLLite()
{with(document.LogicForm)
 { AllReset();
  Transitivity.checked = true;
     Hierarchy.checked = true;
      Inverses.checked = true;
             F.checked = true;
 }
}

function CheckOWLDL()
{with(document.LogicForm)
 {  AllReset();
  Transitivity.checked = true;
     Hierarchy.checked = true;
      Inverses.checked = true;
             O.checked = true;
             N.checked = true;
 }
}

function CheckOWL11()
{with(document.LogicForm)
 { AllReset();
  Transitivity.checked = true;
     Hierarchy.checked = true;
 ComplRoleIncl.checked = true;
    OtherStuff.checked = true;
      Inverses.checked = true;
             O.checked = true;
             Q.checked = true;
 }
}

// ########################################################

function ShowAll()
{
ReadInput();
CheckDependencies();
InitVars();
ShowLogic();
ShowComplexity();
}

// ########################################################

function AllReset()
{
document.LogicForm.reset();
ShowAll();
}



function ShowBeta()
{
var WW=window.open('','WWname','width=200,height=200,resizable=yes');
//WW.window.document.title='What is beta?';
WW.window.document.write(
'<html><head><title>What is beta?</title></head><body>'+
'<div style="font-size:11pt;font-style:italic;text-align:right;">'+
'The term "beta" is<br>an abbreviation for the phrase<br>"beta than nothing",'+
'<br>which is exactly what<br>beta software is.<br><br>'+
'Guy Kawasaki<br><a target="_blank" href="http://scribd.com/doc/68449509/The-Macintosh-Way-Guy-Kawasaki">"The Macintosh Way"</a></div></body></html>');

}

// ==================================================================================

 var NamingScheme = '_Anchor';
     EmptyString='';
     OMOString = 'Go to the reference [';
     OMOEnd=']...';

function GoToRef(VN)
{
// window.location.hash=VN;

   var currentURL = window.location.href;
       wherehash  = currentURL.lastIndexOf('#');
       newURL     = ( (wherehash>0)? currentURL.substring(0,wherehash) : currentURL ) +'#'+VN;
//   window.location.replace(newURL);
   window.location.href=newURL;

}

function CreateRefLink(VarName) // Creates a variable with this name and puts into it the tag <a href="#..."></a>
{                               // Additionally, writes into HTML file the anchor: <a name="..."></a>
                                // This "..." will be VarName_Anchor
                                // Side effect: increments RefLabel !

 NamingScheme = VarName+'_Anchor';

 // Old: eval(VarName+'=(++RefLabel)');

// Simple:  eval(VarName+'= \'<a href=#'+NamingScheme+'>'+(++RefLabel)+'</a>\';');

 RefLabel++;

 eval(VarName+'= \'<a target="_self" style="color:blue" href="javascript:void(0);" '+
 'onMouseOver="window.status=OMOString+'+RefLabel+'+OMOEnd;return true;" '+
 'onMouseOut="window.status=EmptyString;" '+
 'onClick=GoToRef(\"'+NamingScheme+'\");>'+RefLabel+'</a>\';');

 document.writeln('<a name="'+NamingScheme+'"></a>');

}

// -----------------------------------------------

function SwapValues(CurrentValue,Value1,Value2)
{
  return (  (CurrentValue==Value1)? Value2 : Value1 );
}

/* -----------------------------------------------
   This function searches for all tags <TagName class="ClassName"></TagName>
   and makes them all visible or invisible simultaneously.
   We could simply use document.getElementsByClassName("ClassName"), but
   this method is not realized in Internet Explorer, alas!
   DisplayStyle = 'inline' / 'block' / ...
*/

function ToggleElementsByClassName(TagName,ClassName,DisplayStyle)
{ var spans=document.getElementsByTagName(TagName);

  for(var i=0;i<spans.length;i++)
	if(spans[i].className.indexOf(ClassName)>=0)
	{  var before = spans[i].style.display || 'none';
		spans[i].style.display= SwapValues(before,'none',DisplayStyle);
	}
}

var ShowAbstr = 'Abstract';
var HideAbstr = 'Hide Abstract';

var ShowBib = 'BibTeX';
var HideBib = 'Hide BibTeX';

/* -------------------------------------------------
   This function shows/hides the <DIV> block with abstract
   and changes the link text: "Show Abstract" / "Hide Abstract"
*/ 
function FlipAbstract(refID,anchorObj,DivSuffix,Text1,Text2,FlipAnchorText)
{
 var before=document.getElementById(refID+'_'+DivSuffix).style.display || 'none';

     // Initially, it is ''; after two flips it is 'none'.
     // So we reduced its value to 'none' in both cases.

 document.getElementById(refID+'_'+DivSuffix).style.display=
 SwapValues(before,'none','block');

   // Decided to not flip the text, since "Show All Abstracts" button
   // will not flip all these texts (I'm lazy to program it)

if(FlipAnchorText) anchorObj.innerHTML = SwapValues(anchorObj.innerHTML,Text1,Text2);

}

// -------------------------------------------------

function CreateAbstractLink(refID)
{
 document.writeln('<a target="_self" href="javascript:void(0);" '+
 'onclick="FlipAbstract(\''+refID+'\',this,\'abstract\',ShowAbstr,HideAbstr,1);">'+ShowAbstr+'</a>');
}

function CreateBibTeXLink(refID)
{
 document.writeln('<a target="_self" href="javascript:void(0);" '+
 'onclick="FlipAbstract(\''+refID+'\',this,\'bibtex\',ShowBib,HideBib,true);">'+ShowBib+'</a>');
}

function CreateAbstractBibTeXLinks(refID)
{
 CreateAbstractLink(refID);
 document.writeln(' | ');
 CreateBibTeXLink(refID);
}













function FinishContent()
{
 var LM=new Date(document.lastModified);

       yy = LM.getYear();
       mm = LM.getMonth(); // JAN=0; FEB=1; ...
       dd = LM.getDate();

       hour  = LM.getHours();
       mins = LM.getMinutes();
       secs = LM.getSeconds();

       DD = ((dd<10)? "0" : "")+dd;
       MM = ((mm<9)? "0" : "")+ (mm+1);
       YYYY = (  (yy<2000)? (1900+yy) : (yy)  );
       // Under some browsers yy=2005, not usual 105 !! 
       Hour = ((hour<10)? "0" : "") + hour;
       Mins = ((mins<10)? "0" : "") + mins;
       Secs = ((secs<10)? "0" : "") + secs;

       DateString = DD + "/" + MM + "/" + YYYY;
       TimeString= Hour + ":" + Mins; // + ":" + Secs;

 document.writeln('<div>Last update: '+
 DateString + "&nbsp;" + TimeString +'</div>');

}


function NoSpamMail(sobaka)
{
var MailString='mailto:'+'ezolin'+sobaka+'cs.man.ac.uk?subject=DL%20Complexity%20Navigator&body=Hi%20Evgeny!';
 location.href=MailString;
}
