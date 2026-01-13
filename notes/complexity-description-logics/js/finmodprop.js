function FiniteModelProp() // Do we know something about Finite Model Property of the Logic?
{

 // ========= Negative ===========================================

 if(SH==3 && II==1 && FNQ>0) // Extensions of SHIF has no FMP
 {
  FiniteAnswer='No';
  FiniteComment='The <em>SHIF</em>-concept '+
  '<nobr><span class="bl">&not;<i>A</i>&nbsp;'+sAND+'&nbsp;<i>C</i>&nbsp;'+sAND+
  '&nbsp;&forall;<i>U</i><sup>&#151;</sup>.<i>C</i></span></nobr>, '+
  'where <span class="bl"><nobr><i>C</i>&nbsp;&equiv;&nbsp;&exist;<i>R</i><sup>&#151;</sup>.<i>A</i>&nbsp;'+sAND+
  '&nbsp;(&le;1&nbsp;<i>R</i>)</span></nobr>, has only infinite models '+
  'w.r.t. the TBox: <nobr><span class="bl">{&nbsp;<i>R</i>&nbsp;&sube;&nbsp;<i>U</i>,&nbsp;Tr(<i>U</i>)&nbsp;}</span>.</nobr> '+
  'See&nbsp;['+HorrocksSattlerPract2000+',&nbsp;Sect.3.4].';
  return;
 }

 if(II==1 && FNQ>0 && RStr==1) // Extensions of ALCIF(*)
 {
  FiniteAnswer='No';
  FiniteComment=
  'The <em>ALCIF</em>(*)-concept '+
  '<nobr><span class="bl">&not;<i>A</i>&nbsp;'+sAND+
  '&nbsp;&forall;<i>R</i>*.[&exist;<i>R</i>.<i>A</i>&nbsp;'+sAND+  '&nbsp;(&le;1&nbsp;<i>R</i><sup>&#151;</sup>)]</span></nobr> '+
  'has only infinite models.</nobr> '+
  'See&nbsp;['+DLBook+',&nbsp;p.92].';
  return;
 }

 if(II==1 && FNQ>0 && TBoxIsCycle) // Extensions of ALCIF + general TBox
 {
  FiniteAnswer='No';
  FiniteComment='<ul>'+
  '<li>The <em>ALCFI</em>-concept <span class="bl"><i>A</i></span> is has only infinite models w.r.t. the following TBox:<br>'+
  '<span class="bl">{&nbsp;T&nbsp;&sube;&nbsp;&exist;<i>R</i>.&not;<i>A</i>; &nbsp; '+
  'T&nbsp;&sube;&nbsp;(&le;1&nbsp;<i>R</i><sup>&#151;</sup>)&nbsp;}</span>. '+
//  '{&nbsp;<i>A</i>&nbsp;&sube;&nbsp;<i>B</i>&nbsp;'+sAND+'&nbsp;&not;&exist;<i>R</i><sup>&#151;</sup>;&nbsp;&nbsp;'+
//  '<i>B</i>&nbsp;&sube;&nbsp;&exist;R&nbsp;'+sAND+'&nbsp;(&le;1&nbsp;<i>R</i><sup>&#151;</sup>)&nbsp;'+sAND+
//  '&nbsp;&forall;<i>R</i>.B&nbsp;}.'+
  'See also ['+DLBook+',&nbsp;p.209].'+
  '<li><u>Finite model</u> reasoning w.r.t. <em>ALCQI</em> TBoxes (and ABoxes!) is <b>ExpTime-complete</b>, '+
  'even with binary encoding of numbers. See&nbsp;['+LutzSattlerTendera2005+'].'+
  '<li>An intermediate result that the finite model reasoning w.r.t. <em>ALCQI</em> TBoxes '+
  'is decidable in deterministic ExpExpTime was obtained in&nbsp;['+Calvanese1996a+']; '+
  'see also ['+DLBook+',&nbsp;p.214,&nbsp;Theorem&nbsp;5.26].'+
  '</ul>';
  return;
 }

 // ALC_reg(cap) has not FMP. More exactly: (cap,o,*,id(T)) or (cap,cup,+,id(T))
 if(RStr==1 && RCap==1 && RIdC==1 && RCrc==1)
 {
  FiniteAnswer='No';
  FiniteComment='The <em>ALC</em>(&cap;,o,*,id(T))-concept '
  +'<nobr><span class="bl">&forall;<i>R</i>*.(&exist;<i>R</i>.T &cap; &forall;(<i>R</i><sup>+</sup>&cap;<i>id</i>(T)).&perp;)</span></nobr>, where '
  +'<nobr><span class="bl"><i>R</i><sup>+</sup> := <i>R</i> o <i>R</i>*</span></nobr>,'
  +' is satisfiable, but every its model has an infinite acyclic chain ['+Harel1984+',&nbsp;Theorem&nbsp;2.35].';
 }

// Now positive, for concrete logics

if(RR==0)
{ // Logics without "Complex Role Inclusion Axioms"

 if(MM==0)
 {
 // ========= Positive ===========================================

  if(Logic(0,0,0,0) && TBoxIsEmpty) // ALC = K. So - see Modal Logic!
  { 
   FiniteAnswer='Yes';
   FiniteComment='<em>ALC</em> is a notational variant of the multi-modal logic <b>K<sub><i>m</i></sub></b> (cf. ['+Schild1991+']), '+
   'for which the finite model property can be found in ['+MLBook+', Sect.&nbsp;2.3].';
   return;
  }

  if(LogicInterval(0,0,1,0, 0,0,3,0) && TBoxIsEmpty) // All logics below ALCQ, thanks Birte!
  {
   FiniteAnswer='Yes';
   FiniteComment='For all sublogics of <em>ALCQ<sub>&nbsp;</sub></em>, which corresponds to Graded Modal Logic ['+
	WvanderHoek1992+',&nbsp;'+MdeRijke2000Graded+'].';
   return;
  }

  if(LogicInterval(0,0,0,0, 1,1,0,0) && TBoxIsEmpty) // All logics below SI, thanks Birte! 
  {
   FiniteAnswer='Yes';
   FiniteComment='For all sublogics of <em>SI</em>. This follows from the results in ['+HorrocksSattlerTobies1998+']: '+
   'for a satisfiable concept, one can build a finite tableaux (see Lemma&nbsp;6), '+
   'which can be used to build a finite model (see Lemma&nbsp;3). '+
   'See also the corresponding Lemmas 6.7 and 6.3 in&nbsp;['+TobiesPhD2001+'].';
   return;
  }

  if(LogicInterval(0,0,0,0, 1,1,2,0) && TBoxIsEmpty) // All logics below SIN, thanks Birte! 
  {
   FiniteAnswer='Yes';
   FiniteComment='For all sublogics of <em>SIN</em>. This follows from the results in ['+HorrocksSattlerTobies1998+']: '+
   'for a satisfiable concept, one can build a finite tableaux (see Lemma&nbsp;25), '+
   'which can be used to build a finite model (see Lemma&nbsp;21).';
   return;
  }

  if(LogicInterval(0,0,0,0, 3,0,3,0) ||
     LogicInterval(0,2,0,0, 3,2,3,0) ) // All logics below SHOQ! i.e. (ALC,SHQ) + (ALCO,SHOQ)
  {
   FiniteAnswer='Yes';
   FiniteComment='For all sublogics of <em>SHOQ</em>. This is mentioned in ['+LutzArecHorSat2004+
   '], where a similar result is obtained in Corollary 4.3 for <em>SHOQ</em> extended with concrete domains and keys. '+
   '(I did not find a \"proper\" reference for <em>SHOQ</em> or its sublogics.)';
   return;
  }

  if(LogicBetween(0,0,0,0,0,0,0,0,0,0,0,
                  0,0,1,0,0,0,1,0,1,1,1)) // All logics below ALCI_reg + any TBoxes
  {
   FiniteAnswer='Yes';
   FiniteComment='For all sublogics of '+((II==0)?
   '<em>ALC</em><sub>reg</sub>  with any TBoxes; see ['+FischerLadner1979+',&nbsp;Theorem&nbsp;3.2].':
   '<em>ALCI</em><sub>reg</sub> with any TBoxes; see ['+FischerLadner1979+',&nbsp;Theorem&nbsp;3.2 and discussion after Theorem&nbsp;3.3].');
   return;
  }

  if(LogicBetween(0,0,0,0,0,0,0,0,0,0,0,
                  0,0,0,0,2,1,0,0,0,0,0)) // All logics below ALCN(cap) + any TBoxes, thanks Birte!
  {
   FiniteAnswer='Yes';
   FiniteComment='For the logic <em>ALCN</em>(&cap;) with any TBoxes, see the very end of Sect.&nbsp;3 in ['+Buchheit_etal_1993a+'].';
   return;
  }

  if(Logic(0,0,0,4) && TBoxIsEmpty) // ALC(neg)
  {
   FiniteAnswer='Yes';
   FiniteComment='See ['+Gargov_etal_1987+'].';
   return;
  }


}else{ // Logics with Mu-operator

  if(Logic(0,0,0,reg)) // mu-ALC (We have to put "reg" here, since mu automatically checks them!)
  {
  FiniteAnswer='Yes';
  FiniteComment='See ['+Kozen1988+', Theorem&nbsp;6.1].';
  } 
}

} // End "No Complex Role Inclusions"
else
{ // Complex Role Inclusions: RIQ, SRIQ, sROIQ 

}


}
