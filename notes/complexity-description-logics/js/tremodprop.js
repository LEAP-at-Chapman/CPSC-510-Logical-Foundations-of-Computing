function TreeModelProp() // Do we know something about Tree Model Property of the Logic?
{

 // ========= Negative ===========================================

 if(RNeg) //  Extensions of ALC(neg)
 {
  TreeAnswer='No';
  TreeComment='The concept <nobr><span class="bl"><i>A</i>&nbsp;'+sAND+
	'&nbsp;&forall;(&not;R).&not;<i>A</i></span></nobr> is satisfiable, but has no tree models.'+
  ' See&nbsp;['+LutzSattler2001+',&nbsp;Sect.2].';
   return;
 }

 if(FNQ>0 && RCrc==1 && RinN) // ALCF(o) with complex roles in F
 {
  TreeAnswer='No';
  TreeComment='The <em>ALCF</em>(o)-concept <nobr><span class="bl">(&ge;2&nbsp;<i>R</i>)&nbsp;'+
  sAND+'&nbsp;(&forall;<i>R</i>.&exist;<i>S</i>.T)&nbsp;'+
  sAND+'&nbsp;(&le;2&nbsp;<i>R</i>o<i>S</i>)</span></nobr> is satisfiable, but has no tree models.'+
  ' See&nbsp;['+BaaderSattler1999+',&nbsp;Sect.&nbsp;3].';  
  return;
 }

 if(II==1 && HH==1) // Extensions of ALCHI, thanks to Birte Glimm
 {
  TreeAnswer='No';
  TreeComment='In <em>ALCHI</em>, symmetric roles are expressible by a TBox '+
  '<span class="bl">{&nbsp;<i>R</i>&nbsp;&sube;&nbsp;<i>R</i><sup>&#151;</sup>&nbsp;}</span>, '+
  'so that the concept <span class="bl">&exist;<i>R</i>.T</span> has no tree models. '+
  '(Or maybe this kind of models are still countered as tree-like?).';
  return;
 }

// Now positive, for concrete logics

if(RR==0)
{ // Logics without "Complex Role Inclusion Axioms"

 if(MM==0)
 {
 // ========= Positive ===========================================

  if(Logic(0,0,0,0) && TBoxIsEmpty) // ALC = K. So - see Modal Logic!
  {
   TreeAnswer='Yes';
   TreeComment='<em>ALC</em> is a notational variant of the multi-modal logic <b>K<sub>m</sub></b> (cf. ['+Schild1991+']), '+
   'for which the tree model property can be found in ['+MLBook+', Proposition&nbsp;2.15].';
   return;
  }


  if(LogicBetween(0,0,0,0,0,0,0,0,0,0,0,
                  0,0,1,0,1,0,1,0,1,1,1) && !RinN) // All logics below ALCFI_trans
  {
   TreeAnswer='Yes';
   TreeComment='For all sublogics of <em>ALCFI</em><sub>reg</sub> with any TBoxes; see ['+
                DLBook+',&nbsp;p.189, Theorem&nbsp;5.6].';
   return;
  }


}else{ // Logics with Mu-Operator
  if(Logic(0,0,0,reg)) // mu-ALC
  {
  TreeAnswer='Yes';
  TreeComment='See ['+StreettEmerson1989+'].';
  return;
  } 

  if(LogicInterval(0,2,0,reg, 0,3,0,reg)) // mu-ALCO < L < mu-ALCIO -- No (?)
  {
  TreeAnswer='No';
  TreeComment='See ['+SattlerVardi2001+'].';
  return;
  } 

} // end of "Mu-Operator".

} // End "No Complex Role Inclusions"
else // Complex Role Inclusions: RIQ, SRIQ, SROIQ
{  

}


}
