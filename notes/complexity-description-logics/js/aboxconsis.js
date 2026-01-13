// SHIQ + TBox + ABox: http://arxiv.org/abs/cs/0005017

function ABoxConsistency() // Do we know something about ABox Consistency problem in this Logic?
{

var  AboxHarderConcepts='<li><u>Hardness</u> follows from that for concept satisfiability.';

 AppendixA='<ul>'+AboxHarderConcepts+
              '<li><u>Upper bound</u> for <em>ALCQO</em>'+
              ((FNQ>1)?' even with numbers coded in binary':'')+': see ['+
              LTCSRep2004+',&nbsp;Appendix&nbsp;A].</ul>';

    YuDing = '<ul>'+AboxHarderConcepts+
             '<li><u>Upper bound</u> is obtained in ['+DingHaWiDL2007+',&nbsp;Theorem&nbsp;4] '+
             'by a polynomial translation (that preserves satisfiability) into the language without inverse roles.</ul>';

// First - some general reductions

 if(SATComplexity==UN)
 { ABoxComplexity = SATComplexity;
   ABoxComment    = 'ABox consistency is at least as hard as concept satisfiability.';
   return;
 }

 if(Nominals)
 {
  ABoxComplexity = SATComplexity;
  ABoxComment = (ABoxComplexity==Dunno)? '': 'By reduction to concept satisfiability problem in presence of nominals shown in ['+Schaerf1994b+', Theorem&nbsp;3.7].';
  return;
 }

// Now consider logics in details

if(RR==0)
{ // Logics without "Complex Role Inclusion Axioms"

if(MM==0)
{  // Logics without Mu-operator

if(ROpers==0)
{

 // --------------------------
 if(TBoxIsEmpty)
 {
   if(SH==0 && IO==0 ) // (ALC..ALCQ) + AcyclicTBox = PSpace-complete!
    { ABoxComplexity = PS;
      ABoxComment    = AppendixA;
      return;
    }

   if(SH==0 && IO==1)
    { ABoxComplexity = PS;
      ABoxComment    = YuDing;
      return;
    }
 }

 // --------------------------
 if(TBoxIsAcycl)
 {
   if(SH==0 && IO==0 ) // (ALC..ALCQ) + AcyclicTBox = PSpace-complete!
    { ABoxComplexity = PS;
      ABoxComment    = AppendixA;
      return;
    }
   if(SH==0 && IO==1)
    { ABoxComplexity = PS;
      ABoxComment    = YuDing;
      return;
    }
 }

 // --------------------------
 if(TBoxIsCycle)
 {

  if(LogicInterval(0,0,0,0, 3,1,3,0)) // S or H < L < SHIQ
  {
   ABoxComplexity=EX;
   ABoxComment='<ul>'+
   '<li><u>Hardness</u> follows from ExpTime-hardness of concept satisfiability w.r.t. general TBoxes.<br>'+
   '<li><u>Upper bound</u> even for <em>SHIQ</em> was proved in ['+
    TobiesPhD2001+',&nbsp;Corollary&nbsp;6.30]'+((FNQ>1)?' even with numbers coded in binary.':'.')
   +'</ul>';
   return;
  }



 }

}else{ // Role operators

// Independently of TBoxes:

   // ALC(cap,neg) < L < ALCQIO(boolean)  or  ALCFIO < L < ALCQIO(boolean)
   if( LogicBetween(0,0,0,0,0,1,0,1,0,0,0,
                    0,0,1,1,3,1,1,1,0,0,0) || LogicInterval(0,3,1,0, 0,3,3,7) )
   {
    ABoxComplexity=NE;
    ABoxComment='<ul><li><u>Hardness</u>: see lower bound for concept satisfiability in '+
    ( (LogicBetween(0,0,0,0,0,1,0,1,0,0,0,
                    0,0,1,1,3,1,1,1,0,0,0))? '<em>ALC<sub>&nbsp;</sub></em>(&cap;,&not;).' : '<em>ALCFIO</em>.' )
     + '<li><u>Upper bound</u>: see upper bound for ABox consistency in <em>ALCQIO<sub>&nbsp;</sub></em>(&cap;,&cup;,&not;).'+'</ul>';
    return;
   }

   // ALC  < L < ALC (id,o,U) - the same as for ALC  (for each TBox option)
   // ALCI < L < ALCI(id,o,U) - the same as for ALCI (for each TBox option)
   // The same for nominals is redundant (the result for ABox is already automatically copied from CSAT)

  if(LogicBetween(0,0,0,0,0,0,0,0,0,0,0,
                  0,0,1,0,0,0,1,0,1,0,1))
  {
   ABoxComplexity=SATComplexity; // Actually, we must copy ABoxComplexity(L without role operators), not SATComplexity! However, for THESE logics, they coincide!
   var LLL=(II==1)? '<em>ALCI</em>' : '<em>ALC</em>'; 
   ABoxComment='<ul><li>Role operators are eliminable in '+LLL+' (see above).'
	+ '<li>Therefore, the complexity is the same as for the logic '+LLL+'.'
   + '</ul>';
   return;
  }

 // --------------------------
 if(TBoxIsEmpty)
 {

 }

 // --------------------------
 if(TBoxIsAcycl)
 {

 }

 // --------------------------
 if(TBoxIsCycle)
 {
  if(LogicBetween(0,0,0,0,0,0,0,0,0,0,0,
                  0,0,1,0,3,1,1,0,0,0,0)) // ALC < L < ALCQI(cap,cup)
  {
   ABoxComplexity=EX;
   ABoxComment='See ['+TobiesPhD2001+',&nbsp;Theorem&nbsp;4.42].'+((FNQ>1)?' This holds even if numbers are coded in binary.':'');
   return;
  }
 }
} //End of role operations

}else{ // Logics with Mu-Operator

}

} // End "No Complex Role Inclusions"
else // Complex Role Inclusions: RIQ, SRIQ, SROIQ
{  

}

}
