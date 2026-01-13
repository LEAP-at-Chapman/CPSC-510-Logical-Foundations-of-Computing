function ConceptSAT() // Do we know anything about Concept SAT problem in this Logic?
{

// We have to assign the string constants inside the function; otherwise references to literature in them are undefined!

var LowALC='<u>Hardness</u> for <em>ALC</em>: see ['+SchmidtSchauBSmolka1991+'].';

 AppendixA='<li><u>Upper bound</u> for <em>ALCQO</em>'+((FNQ>1)?' with numbers coded in unary':'')+': see ['+
               LTCSRep2004+',&nbsp;Appendix&nbsp;A].';

 ALCFIOhard='<li><u>Hardness</u> of even <em>ALCFIO</em> is proved in&nbsp;['+Tobies2000+', Corollary&nbsp;4.13]. '+
              ((FNQ<3)?'In that paper, the result is formulated for <em>ALCQIO</em>, but only number restrictions of the form (&le;1<i>R</i>) are used in the proof.':'')+
              '<li>A different proof of the NExpTime-hardness for <em>ALCFIO</em> is given in&nbsp;['+LutzImproved2004+'] (even with 1 nominal, and inverse roles not used in number restrictions).'

 NExpTExplain=ALCFIOhard+
              '<li><u>Upper bound</u> for <em>SHOIQ</em> is proved in ['+TobiesPhD2001+',&nbsp;Corollary&nbsp;6.31]'+
              ((FNQ>=2)?' with numbers coded in unary (for binary coding, the upper bound remains an open problem for all logics in between <em>ALCNIO</em> and <em>SHOIQ</em>).':'.');

  ExpTAdditions=((IO==1 && FNQ==3)? /* SHIQ */ '<li>A tableaux system for <em>SHIQ</em> is described in ['+HladikModelDL2004+'].':
                 (IO==2 && FNQ==3)? /* SHOQ */ '<li>A reasoning procedure for the extension of <em>SHOQ</em> '+
                'with concrete datatypes &#150; <em>SHOQ</em>(<b>D</b>) &#150; is described in ['+HorrSattSHOQD+
                '], and for the extension of <em>SHOQ</em> with <i>n</i>-ary datatype predicates '+
                '&#150; <em>SHOQ</em>(<b>D</b><sub>n</sub>) &#150; is described in ['+PanHorrSHOQDn+'].': '');

  ExpTExplain= '<li><u>Hardness</u> follows from internalization of TBoxes in any extension of <em>SH</em> and ExpTime-hardness of <em>ALC</em>-concept satisfiability w.r.t. general TBoxes.'+
               '<li><u>Upper bound</u> for <em>SHIQ</em> see ['+TobiesPhD2001+',&nbsp;Corollary&nbsp;6.29,&nbsp;6.30]; for <em>SHIO</em> see ['+HladikIJCAR2004+',&nbsp;Th.3]; for <em>SHOQ</em> see [?].'+
               ((FNQ>1)? ' This holds even for numbers are coded in binary.':'')+ExpTAdditions;

  SimpleRoleExplain=((FNQ>0)? '<li><b>Important:</b> in number restrictions, only <i>simple</i> roles (i.e. which are neither transitive nor have a transitive subroles) are allowed; '+
               ((FNQ>1)? 'otherwise we gain undecidability even in <em>SHN</em>; see ['+HorrocksSattlerPract2000+'].' :
                         'however, according to ['+HorrocksSattlerPract2000+'], it is an open problem whether <em>SHF</em> or <em>SHIF</em> becomes undecidable without this restriction.') +
               '<li><b>Remark:</b> recently ['+KazSatZolin2007+'] it was observed that, in many cases, one can ' +
               'use transitive roles in number restrictions &#150; and still have a decidable logic! '+
               'So the above notion of a <i>simple</i> role could be substantially extended.' : '');

  TableauxSHOIQ='<li>A tableaux algorithm for <em>SHOIQ</em> is presented in&nbsp;['+HorrSattSHOIQ2005+'].';


  ALCBoolean='<u>Hardness</u> for <em>ALC</em>(&cap;,&not;) is proved in&nbsp;['+LutzSattler2001+'].';

    TwoVarFOLCount='<u>Upper bound</u> follows from embedding into the logic <i>C</i><sup>2</sup> '+
                   '(first-order predicate logic with two variables and counting), '+
                   'which is NExpTime-complete even with numbers coded in binary, see ['+PrattHartmann_2005+'] '+
                   '(previously NExpTime-completeness of <i>C</i><sup>2</sup> was proved in ['+
                    Gradel_etal_1997b+'],&nbsp;['+Pacholski_etal_2000+'] '+
                   'only for unary encoding of numbers).';

    BoundNumOfRoles = 'If the number of role names is bounded, then the logic becomes <b>ExpTime-complete</b>';

      SafeBool = '<li>If we restrict role expressions to <i>safe boolean</i> combinations '+
                 '(i.e. whose DNF have at least one non-negated role in each disjunct), '+
                 'then such an extension of even <em>ALCQI</em> is <b>PSpace-complete</b>'+
                  ((FNQ>1)?' (even with numbers coded in binary)':'') + ': see&nbsp;['+
                  TobiesPhD2001+',&nbsp;Theorem&nbsp;4.29].';


 SafeBoolExp = '<li>If we restrict role expressions to <i>safe boolean</i> combinations '+
               '(i.e. whose DNF have at least one non-negated role in each disjunct), '+
               'then such an extension of even <em>ALCQI</em> is <b>ExpTime-complete</b>'+
                ((FNQ>1)?' (even with numbers coded in binary)':'') + ': see&nbsp;['+
                TobiesPhD2001+',&nbsp;Theorem&nbsp;4.38].';




 // First - Undecidability facts!

 if (RCap==1 && RCrc==1 && RNegF==1) // Extensions of ALC(cap,negFull,o)
 { SATComplexity=UN;
   SATComment='Undecidability of <em>ALC</em>(&cap;,&not;,o) is proved in&nbsp;['+Schild1989+']. '
   +'See also ['+Harel1984+',&nbsp;Theorem&nbsp;2.34].';
   return;
 }

// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% THESE ARE LIFTED FROM BELOW

   if(FNQ>0 && RCup && RCrc && RStr && RinN) // Extensions of ALCF_trans with "Allow" are UNdecidable
   {
    SATComplexity=UN;
    SATComment='See&nbsp;['+DLBook+',&nbsp;p.217]. Key: '+
    'NxN-grid can be expressed by a <em>ALCF</em><sub>trans</sub>-concept: '+
    '<nobr>&forall;(right&nbsp;o&nbsp;up)*.&nbsp;(&exist;<sup>=1</sup>up&nbsp;'+sAND+'&nbsp;&exist;<sup>=1</sup>right&nbsp;'+sAND+'&nbsp;&le;1&nbsp;'+
    '((right&nbsp;o&nbsp;up)&cup;(up&nbsp;o&nbsp;right)))</nobr>.';
    return;
   }



   if(FNQ>1 && RCrc==1 && RStr==1 && RinN) // ALCN(o,*), Allow!
   { SATComplexity=UN;
     SATComment='<ul>'
     +'<li>Undecidability of <em>ALCN</em>(o,*) is shown in&nbsp;['+BaaderSattler1999+', Theorem&nbsp;6] '
     +'even without transitive closure operator inside number restrictions.'
     +'<li>Note that ['+BaaderSattler1999+'] deals with the transitive (+) instead of reflexive-transitive (*) closure operator.'
     +'</ul>';
     return;
   }

   if(FNQ>1 && RCap==1 && RCrc==1 && RinN) // ALCN(cap,o), Allow!
   { SATComplexity=UN;
     SATComment='Undecidability of <em>ALCN</em>(&cap;,*) is shown in&nbsp;['+BaaderSattler1999+', Theorem&nbsp;5].';
     return;
   }

   if(FNQ>1 && II==1 && RCup==1 && RCrc==1 && RinN) // ALCIN(cup,o), Allow!
   { SATComplexity=UN;
     SATComment='Undecidability of <em>ALCIN</em>(&cup;,o) is shown in&nbsp;['+BaaderSattler1999+', Theorem&nbsp;5] '
     +'even when inverse is applied to atomic roles only.';
     return;
   }

   if(FNQ>1 && II==1 && RCrc==1 && RinN) // ALCIN(o), Allow!
   { SATComplexity=UN;
     SATComment='Undecidability of <em>ALCIN</em>(o) (where inverse roles are allowed both in '
     +'&exist;<i>R</i>.<i>C</i> and in <nobr>&ge;<i>n</i> <i>R</i></nobr>) '
     +'is proved in ['+GrandiLPAR2002+',&nbsp;Theorem&nbsp;1] by reduction from the domino problem&nbsp;['+Berger1966+'].';
     return;
   }

   var GrandiDL2001Plus='<li>Note that ['+GrandiDL2001+'] deals with the transitive (+) instead of reflexive-transitive (*) closure operator.';

   if(FNQ>1 && RCap==1 && RStr==1 && RinN) // ALCN(cap,+), Allow! (+ instead of *, but does it matter?)
   { SATComplexity=UN;
     SATComment='<ul>'
     +'<li>Undecidability of <em>ALCN</em>(&cap;,*) is shown in&nbsp;['+GrandiDL2001+', Theorem&nbsp;2] '
     +'even without &cap; inside quantifiers.' + GrandiDL2001Plus + '</ul>';
     return;
   }

   if(FNQ>1 && RCup==1 && RStr==1 && RinN) // ALCN(cup,+), Allow! (+ instead of *, but does it matter?)
   { SATComplexity=UN;
     SATComment='<ul>'
     +'<li>Undecidability of <em>ALCN</em>(&cup;,*) is shown in&nbsp;['+GrandiDL2001+', Theorem&nbsp;1] '
     +'even without &cup; inside quantifiers.' + GrandiDL2001Plus + '</ul>';
     return;
   }

// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%





if(RR==0)
{ // Logics without "Complex Role Inclusion Axioms"

if(MM==0)
{ // Logics without Mu-operator

if(ROpers==0)
{ 

// --------------------------
 if(TBoxIsEmpty)
 {
  // First calculate the complexity
   if(SH<2)  SATComplexity = (IO<3)? PS: ((FNQ==0)? EX:NE);
   if(SH==3) SATComplexity = (IO==3 && FNQ>0)? NE:EX;
   if(SH==2)
   { // Only partial case is known to me
    if(IO==3) SATComplexity = (FNQ==0)? EX:NE;
   }

  // Now add comments
   if(SH==0)
   {
     if(IO==0) SATComment = '<ul><li>'+LowALC+'<li><u>Upper bound</u> for <em>ALCQ</em>'+
                             ((FNQ>1)? ' even with numbers coded in binary':'')+
                            ': see ['+TobiesPhD2001+',&nbsp;Theorem&nbsp;4.6].</ul>';

     if(IO==1) SATComment = '<ul><li>'+LowALC+'<li><u>Upper bound</u> for <em>ALCQI</em>'+
                             ((FNQ>1)?' even with numbers coded in binary':'')+
                            ': see ['+TobiesPhD2001+',&nbsp;Theorem&nbsp;4.29].</ul>';

     if(IO==2) SATComment = '<ul><li>'+LowALC+AppendixA+'</ul>';

     if(IO==3 && FNQ==0)
               SATComment = 'See ['+Tobies2000+']; hardness is proved there even in case of a single nominal.';
   }

   if(LogicInterval(1,3,0,0, 2,3,0,0))
   { SATComment = 'This logic is between <em>ALCIO</em> and <em>SHIO</em>.';
     return;
   }

   if(LogicInterval(1,0,0,0, 1,1,0,0))   // S and SI
   { SATComment = '<ul><li>'+LowALC+'<li><u>Upper bound</u> for <em>SI</em> is proved in ['
     +HorrocksSattlerPract1999+'] by presenting a tableaux algorithm.'
     +'<li>The same upper bound for <em>SI</em> (even with acyclic TBoxes) '
     +'is obtained in ['+BaaderHlaPen2008+'] by presenting an automata-based algorithm.'
     +'<li>The Description Logic <em>S</em> corresponds to a <i>fusion</i> of several copies of the PSpace-complete modal logics <b>K</b> and <b>K4</b>.'
     +'</ul>';
     return;
   }

   if(LogicInterval(1,0,1,0, 1,1,2,0))   // SF < L < SIN - Thanks Birte
   { SATComment = '<ul><li>'+LowALC+'<li><u>Upper bound</u> for <em>SIN</em> is proved in ['
     +HorrocksSattlerTobies1998+', Corollary&nbsp;33] by presenting a tableaux algorithm.'
     +'<li><b>Important:</b> In <em>SIN</em> it is assumed that transitive roles are <i>not</i> used in number restrictions, see ['+HorrocksSattlerTobies1998+', Definition&nbsp;19].'
     +'<li>However, the unrestricted Description Logic <em>SQ</em>&nbsp; (i.e. where transitive roles are allowed in number restrictions) corresponds to a <i>fusion</i> of the PSpace-complete graded modal logic <b>GrK<sub>m</sub></b> and NExpTime-complete graded modal logic <b>GrK4<sub>n</sub></b>, so it is decidable.'
     +'<li>On the contrary, for the unrestricted Description Logic <em>SIQ</em> (and even <em>SIN</em>), the problem of concept satisfiability w.r.t. general TBoxes is undecidable, see ['+KazSatZolin2007+', Theorem&nbsp;3].'
     +'</ul>';
     return;
   }

   if(SH==3)
   {
    SATComment= '<ul>'+( (IO==3 && FNQ>0)? ( NExpTExplain + ((FNQ==3)? TableauxSHOIQ:''))
                                            : ExpTExplain ) + SimpleRoleExplain+'</ul>';
    return;
   }

   if(IO==3 && FNQ>0) // NExpTime logics, other than extensions of SH
   {
    SATComment='<ul>'+NExpTExplain+'</ul>';
    return;
   }
 }

// ALCIO + ACyclicTBox = ExpTimeComplete [Areces, Blackburn, Marx]
//

// --------------------------
 if(TBoxIsAcycl)
 {
   if(SH==0 && (IO==0 || IO==2) ) // (ALC..ALCQO) + AcyclicTBox = PSpace-complete!
    { SATComplexity = PS;
      SATComment    = '<ul><li><u>Hardness</u>: see empty TBox.<br>'
                      +AppendixA
                      +((IO==0)?'<li>An automata-based PSpace algorithm for <em>ALC</em> with acyclic TBoxes is given in ['+HladikPenalozaDL06+'].':'')
                      +'</ul>';
      return;
    }

   if(SH<=1 && IO<=1 && FNQ==0 ) // (ALC..SI) + AcyclicTBox = PSpace-complete!
    { SATComplexity = PS;
      SATComment    = '<ul><li><u>Hardness</u>: see empty TBox.'
                      +'<li><u>Upper bound</u> for <em>SI</em> with acyclic TBoxes '
                      +'is obtained in ['+BaaderHlaPen2008+'] by presenting an automata-based algorithm.'
                      +'</ul>';
      return;
    }


 }


var ALC_GenTBox='<li><u>Hardness</u>: originally proved in ['+Schild1991+']; see also ['+DLBook+',&nbsp;Theorem&nbsp;3.27].'+
                '<li><u>Upper bound</u>: an ExpTime tableaux algorithm is given in ['+DoniniMassacci2000+'].';
  Other_GenTBox='<li><u>Hardness</u>: see <em>ALC</em> with general TBoxes.'+
                '<li><u>Upper bound</u> for <em>SHOQ</em>, <em>SHIQ</em>, and <em>SHOI</em>: by internalization of TBox.'+
                '<li>The unrestricted Description Logic <em>SIQ</em> and even <em>SIN</em> (i.e. where transitive roles are allowed in number restrictions), the problem of concept satisfiability w.r.t. general TBoxes is undecidable, see ['+KazSatZolin2007+', Theorem&nbsp;3].';

// --------------------------
 if(TBoxIsCycle)
 {
   SATComplexity = (IO==3 && FNQ!=0)? NE:EX;
         // But for NExpTime (and some of ExpTime) we will never come here! (TBox internalization)

   if(!(IO==3 && FNQ>0)) SATComment= '<ul>'+ ( (IO==0 && FNQ==0)? ALC_GenTBox : Other_GenTBox ) +'</ul>';
    
  return;
 }

} // End: ROpers==0

else

{ // Role Operators

// Next - results that are independent of a TBox:

   // ALC(cap,neg) < L < ALCQIO(boolean)  or  ALCFIO < L < ALCQIO(boolean)
   if( LogicBetween(0,0,0,0,0,1,0,1,0,0,0,
                    0,0,1,1,3,1,1,1,0,0,0) || LogicInterval(0,3,1,0, 0,3,3,7) )
   {
    SATComplexity=NE;
    SATComment='<ul><li>'+ALCBoolean+
                '<li><u>Upper bound</u> even for <em>ALCQI'+
                ((OO>0)?'O':'')+'</em>(&cap;,&cup;,&not;) is shown in ['+
                TobiesPhD2001+', Corollary&nbsp;'+((OO>0)?'5.31':'5.34')+']'+
                ((FNQ>1)?' for <i>unary</i> number encoding only.':'.')+         
                ((OO>0)? '':((TBoxIsEmpty)? SafeBool: ((TBoxIsCycle)? SafeBoolExp:
                '' // for acyclic TBoxes it is unknown...
                )) )+'</ul>';
    return;
   }


   // We want to write something like:
   // if L is between ALC and ALCIO(id,o,U)
   // then everything is the same as for L without (id,o,U)
   // and add into comments how the constructors are eliminated.
   // Instead, we have to do this manually:

   // ALC  < L < ALC (id,o,U) - the same as for ALC  (for each TBox option)
   // ALCI < L < ALCI(id,o,U) - the same as for ALCI (for each TBox option)

   var ElimConstructors =
   ( (RCup==1)? '<li>The constructor <span class="bl"><i>R</i>&cup;<i>S</i></span> can be eliminated: '+
                  '<span class="bl">&exist;(<i>R</i>&cup;<i>S</i>).<i>C</i>&nbsp;&equiv;&nbsp;(&exist;<i>R</i>.<i>C</i>)&or;(&exist;<i>S</i>.<i>C</i>)</span>' : '')
	+ ( (RCrc==1)? '<li>The constructor <span class="bl"><i>R</i>o<i>S</i></span> can be eliminated: '+
                  '<span class="bl">&exist;(<i>R</i>o<i>S</i>).<i>C</i>&nbsp;&equiv;&nbsp;&exist;<i>R</i>.&exist;<i>S</i>.<i>C</i></span>'  : '')
	+ ( (RIdC==1)? '<li>The constructor <span class="bl"><i>id</i>(<i>C</i>)</span> can be eliminated: '+
                  '<span class="bl">&exist;[<i>id</i>(<i>C</i>)].D&nbsp;&equiv;&nbsp;C&and;D</span>' : '');

  if(LogicBetween(0,0,0,0,0,0,0,0,0,0,0,
                  0,0,1,0,0,0,1,0,1,0,1))
  {
   SATComplexity= (TBoxIsEmpty || TBoxIsAcycl)? PS : EX ;
   var LLL=(II==1)? '<em>ALCI</em>' : '<em>ALC</em>'; 
   SATComment='<ul>' + ElimConstructors
	+ '<li>Therefore, the complexity is the same as for the logic '+LLL+'.'
   + '</ul>';
   return;
  }

  // The same as above, but for logics with nominals: ALCO and ALCIO. All complexities become ExpTime-complete.
  // Here we actually need to COPY the results for the corresponding logic without role coustructors.

  if(LogicBetween(0,0,0,1,0,0,0,0,0,0,0,
                  0,0,1,1,0,0,1,0,1,0,1))
  {
   SATComplexity= // If I is present, then ExpTime; else PSpace or ExpTime, depends on TBox
   (II==1)? EX : ((TBoxIsEmpty || TBoxIsAcycl)? PS : EX) ;
   var LLL=(II==1)? '<em>ALCOI</em>' : '<em>ALCO</em>'; 
   SATComment='<ul>' + ElimConstructors
	+ '<li>Therefore, the complexity is the same as for the logic '+LLL+'.'
   + '</ul>';
   return;
  }



// And now results dependent of a TBox

// -------------------------- 
 if(TBoxIsEmpty)
 {
   if(LogicBetween(0,0,0,0,0,0,0,0,0,0,0,
                   0,0,0,0,0,1,1,0,1,0,0)) // ALC < L < ALC(cap,cup,o)
   { SATComplexity=PS;
     SATComment=LowALC+'<br><u>Upper bound</u> for <em>ALC</em>(&cap;,&cup;,o) is proved in ['+Massacci2001+'].';
     return;
   }

// ============================== BOOLEAN ===========================================


   if(LogicInterval(0,0,0,1, 0,1,3,1)) // ALC(cap) < L < ALCQI(cap) = PSpace, Allowed!
   { SATComplexity=PS;
     SATComment=LowALC+'<br><u>Upper bound</u> for <em>ALCQI</em>(&cap;)'+
                ((FNQ>1)?' even with numbers coded in binary':'')+': see ['+
                TobiesPhD2001+',&nbsp;Theorem&nbsp;4.29].';
     return;
   }

   if(LogicInterval(0,0,0,2, 0,1,3,2)) // ALC(cup) < L < ALCQI(cup) = PSpace, Allowed!
   { SATComplexity=PS;
     SATComment=LowALC+'<br><u>Upper bound</u> for <em>ALCQI</em>(&cup;)'+
                ((FNQ>1)?' even with numbers coded in binary':'')+': see ['+
                TobiesPhD2001+',&nbsp;Theorem&nbsp;4.29].';
     return;
   }

   if(Logic(0,0,0,4)) // ALC(neg)
   { SATComplexity=EX;
     SATComment   ='See ['+LutzSattler2001+'].';
     return;
   }

   if(Logic(0,0,0,6) && RNegA) // ALC(cup,neg(atomic))
   { SATComplexity=EX;
     SATComment   ='<ul><li>See ['+LutzSattler2001+']. Key note: &forall;(R&cup;S).C&equiv;&forall;R.C&and;&forall;S.C.'+
                    SafeBool+'</ul>';
     return;
   }

   if(Logic(0,0,0,5) && RNegA) // ALC(cap,neg(atomic))
   { SATComplexity=NE;
     SATComment='<ul><li>See ['+LutzSattler2001+'].' + SafeBool +'</ul>';
     return;
   }

   if(Logic(0,0,0,7)) // ALC(cap,cup,neg), any Neg
   { SATComplexity=NE;
     SATComment='<ul><li>'+'See ['+LutzSattler2001+']. Corresponds to Full Boolean Modal Logic.'
     +'<li>'+BoundNumOfRoles+' ['+LutzSattler2001+', Section&nbsp;5, Theorem&nbsp;25].'
     + SafeBool + '</ul>';
     return;
   }

   if(LogicInterval(0,0,0,7, 0,1,2,7)) // ALC(boolean) < L < ALCIN(boolean), Allowed!
   {
    SATComplexity=NE;
    SATComment='<ul><li>'+ALCBoolean
    +'<li>'+TwoVarFOLCount
       // For ALCI(boolean) the restricted number of roles turns it into ExpTime!
    + ((FNQ==0)? '<li>'+BoundNumOfRoles+' ['+LutzSattlerWolter2001+', Theorem&nbsp;2].':'')
    + SafeBool+'</ul>';
    return;
   }

   if(LogicInterval(0,0,0,3, 0,1,3,3)) // ALC(cap,cup) < L < ALCQI(cap,cup)
   {
    SATComplexity=PS;
    SATComment='See&nbsp;['+TobiesPhD2001+',&nbsp;Theorem&nbsp;4.29].'+
               ((FNQ>1)?' This holds even if numbers are coded in binary.':'');
    return;
   }

   // ALC(boolean,id) < L < ALCI(boolean,id) = NExpTime-complete; or ExpTime, if bounded num. of roles
   if(LogicInterval(0,0,0,39, 0,1,0,39))
   {
    SATComplexity=NE;
    SATComment='<ul><li>'+ALCBoolean
    +'<li>'+TwoVarFOLCount
    +'<li>'+BoundNumOfRoles+' ['+LutzSattlerWolter2001+', Th.2] '
    +'(this was proved there for the logic with <i>id</i>(T) only, but the proof carries out '
    +'easily for the logic with <i>id</i>(<i>C</i>).).'+'</ul>';
    return;
   }



  // ========================================= TRANSITIVE (REGULAR) ======================

 var ALCStar='<u>Hardness</u> for <em>ALC</em>(*) was proved in ['+FischerLadner1979+'],&nbsp;['+Pratt1979+'].';

  if(!RinN)
  {
   if( LogicBetween(0,0,0,0,0,0,0,0,0,1,0,
                    0,0,1,0,3,0,1,0,1,1,1)  ||
       LogicBetween(0,0,0,0,0,0,0,0,0,1,0,
                    0,0,0,1,3,0,1,0,1,1,1)  ||
       LogicBetween(0,0,0,0,0,0,0,0,0,1,0,
                    0,0,1,1,0,0,1,0,1,1,1)) // ALC(*) < L < ALCQI_reg or ACLQO_reg or ACLIO_reg
   {
    SATComplexity=EX;
    SATComment='<ul><li>'+ALCStar+'<li><u>Upper bound</u> ';

    if(LogicBetween(0,0,0,0,0,0,0,0,0,1,0,
                    0,0,0,0,0,0,1,0,1,1,1)) // ALC(*) < L < ALC_reg
       SATComment+=('for <em>ALC</em><sub>reg</sub> was proved in&nbsp;['+FischerLadner1979+'],&nbsp;['+Pratt1979+'].'+
                    '<li>Corresponds to PDL (Propositional Dynamic Logic).');

    if(LogicBetween(0,0,1,0,0,0,0,0,0,1,0,
                    0,0,1,0,0,0,1,0,1,1,1)) // ALCI(*) < L < ALCI_reg
       SATComment+='was proved: for <em>ALCI</em><sub>trans</sub> in&nbsp;['+
                    Vardi1985+'], for for <em>ALCI</em><sub>reg</sub> in ['+Baader1991+'],&nbsp;['+Schild1991+'].';

    if(LogicBetween(0,0,0,0,1,0,0,0,0,1,0,
                    0,0,1,0,3,0,1,0,1,1,1)) // ALCF(*) < L < ALCQI_reg
       SATComment+='for <em>ALCQI</em><sub>reg</sub> was proved in&nbsp;['+
                   DLBook+', p.200, Theorem 5.18]; originally in ['+DeGiacomoLenzerini1996+'].';

    if(LogicBetween(0,0,0,1,0,0,0,0,0,1,0,
                    0,0,0,1,3,0,1,0,1,1,1)) // ALCO(*) < L < ALCQO_reg
       SATComment+='for <em>ALCQO</em><sub>reg</sub> was proved in&nbsp;['+DeGiacomoLenzerini1994a+'].';

    if(LogicBetween(0,0,1,1,0,0,0,0,0,1,0,
                    0,0,1,1,0,0,1,0,1,1,1)) // ALCIO(*) < L < ALCIO_reg
       SATComment+='for <em>ALCIO</em><sub>reg</sub> was proved in&nbsp;['+DeGiacomo1995+'].';

    SATComment+='</ul>';
    return;
   }

   if( LogicBetween(0,0,1,1,1,0,0,0,0,1,0,
                    0,0,1,1,3,0,1,0,1,1,1)) // ALCFIO(*) < L < ALCQIO_reg
   {
    SATComplexity=hNE;
    SATComment='<ul>'
    +'<li>For hardness - see <em>ALCFIO</em>. '
    +'<li>Decidability (for <em>ALCQIO</em><sub>reg</sub>) is an open problem, according to ['+DLBook+',&nbsp;p.200].'
    +'</ul>';
    return;
   }
   
  }

   // PDL + Atomic Negation = ExpTime-complete
   if(RNegA && LogicBetween(0,0,0,0,0,0,0,1,0,1,0,
                            0,0,0,0,0,0,1,1,1,1,1) )
   {
    SATComplexity=EX;
    SATComment='<ul><li>'+ALCStar+'<li><u>Upper bound</u> is established in ['+LutzWalther2004+'].</ul>';
    return;
   }

   if(Logic(0,0,0,27) || Logic(0,0,0,59)) // PDL + Intersection (with or without id(C)) = 2-ExpTime-complete
   {
    SATComplexity=EEX;
    SATComment='<ul><li>Corresponds to IPDL (PDL with intersection'
    + ((RIdC==0)? ' without the test operator' : '')+').'
    +'<li>'+'<u>Hardness</u> is established in ['+LangeLutz2005+'].'
    +'<li>'+'As an intermediate result, the <b>ExpSpace</b>-hardness was established in ['+LangeEXPSPACE+'].'
    +'<li>'+'<u>Upper bound </u> was obtained in ['+Danecki1984+'].'
    +' A simpler proof can be found in ['+LutzICPDL2005+'].'+'</ul>';
    return;
   }

   // PDL + Intersection + Converse = Decidable.
   if(LogicBetween(0,0,1,0,0,1,1,0,1,1,1,
                   0,0,1,0,0,1,1,0,1,1,1))
   {
    SATComplexity=DE;
    SATComment='<ul>'
    +'<li>Corresponds to ICPDL (PDL with intersection and converse). '
    +'<li>Decidability is proved in ['+LutzICPDL2005+'] by translation into monadic second-order logic '
    +'(which yields only a non-elementary upper bound). '
    +'<li>It is conjectured in ['+LutzICPDL2005+'] that the logic is <b>2-ExpTime-complete</b>.'
    +'</ul>';
   return;
   }

   // Here I had undecidable ALCF_trans with "Allow" -- but later pushed it upwards.

  // ============================================== ALCN(various) + Allow role ops in num.restr!

   if(LogicInterval(0,0,1,8, 0,0,3,8) && RinN) // ALCQ(o); Allow or Disallow - only decidability is known!
   { SATComplexity=iNE;
     SATComment=
     (FNQ<3)?
     '<ul><li>A tableaux algorithm for <em>ALCN</em>(o) is given in&nbsp;['+BaaderSattler1999+', Theorem&nbsp;9]. '
     +'<li>Moreover, the algorithm is extended to the logic exended with number restrictions '
     +'on intersection or union of role chains of the same length, i.e., expressions of the form '
     +'<nobr>&ge;n((<i>R<sub>1</sub></i> o...o <i>R<sub>n</sub></i>)&cap;(<i>S<sub>1</sub></i> o...o <i>S<sub>n</sub></i>))</nobr> '
     +'and similarly for&nbsp;&cup;; see ['+BaaderSattler1999+', Theorem&nbsp;11].'
     +'<li>The NExpTime upper bound is shown in&nbsp;['+GrandiLPAR2002+',&nbsp;Lemma&nbsp;4].'+'</ul>':
     'A tableaux algorithm for <em>ALCQ</em>(o) together with the upper complexity bound is presented '
     +'in&nbsp;['+GrandiLPAR2002+',&nbsp;Lemma&nbsp;4].';
     
     if(FNQ==2)
     { ABoxComplexity=DE+'?';
       ABoxComment='<ul>'
       +'<li>Consistency of ABoxes of a restricted form is shown to be decidable in&nbsp;['+Molitor1997+']. '
       +'<li>For general ABoxes, the problem is open, according to ['+BaaderSattler1999+',&nbsp;Sect.&nbsp;6].'
       +'</ul>';
     }
     return;
   }

   // Here I had undecidable ALCN(o,*), Allow! -- but later pushed it upwards.

   // Here I had undecidable ALCN(cap,o), Allow! -- but later pushed it upwards.

   if(Logic(0,0,2,10) && RinN) // ALCN(cup,o), Allow!
   { SATComplexity=DE+'?';
     SATComment='Open problem, according to ['+BaaderSattler1999+',&nbsp;end&nbsp;of&nbsp;Sect.&nbsp;3.2], ['+DLBook+',&nbsp;p.&nbsp;218].';
     return;
   }

   // Here I had undecidable ALCIN(o), Allow! -- but later pushed it upwards.

   // Here I had undecidable ALCIN(cup,o), Allow! -- but later pushed it upwards.

   // Here I had undecidable ALCN(cap,+), Allow! -- but later pushed it upwards.

   // Here I had undecidable ALCN(cup,+), Allow! -- but later pushed it upwards.


  // ============================================== Other *-logics

   if(RStar) // Extensions of ALC(*)
   { SATComplexity=hEX;
     SATComment=ALCStar;
     return;
   }

 }

 // --------------------------
 if(TBoxIsAcycl)
 {

 }

 // --------------------------
 if(TBoxIsCycle)
 {

  if(II==1 && FNQ>1 && RCrc==1 && RCup==1 && RinN) // ALCIN(o,U), operations are allowed in num.restr.
  { SATComplexity=UN;
    SATComment='Undecidability of <em>ALCIN</em>(&cup;,o) with general TBoxes is proved in ['+BaaderSattler1999+'].';
    return;
  }

  if(FNQ>1 && RCrc==1 && RCap==1 && RinN) // ALCN(o,cap)
  { SATComplexity=UN;
    SATComment='Undecidability of <em>ALCN</em>(&cap;,o) is proved in ['+BaaderSattler1999+'].';
    return;
  }

  if(LogicBetween(0,0,0,0,0,0,0,0,0,0,0,
                  0,0,1,0,3,1,1,0,0,0,0)) // ALC < L < ALCQI(cap,cup); Allow!
  {
   SATComplexity=EX;
   SATComment='See ['+TobiesPhD2001+',&nbsp;Theorem&nbsp;4.38].'+
              ((FNQ>1)?' This holds even if numbers are coded in binary.':'');
   return;
  }

  if(LogicBetween(0,0,0,0,0,0,0,1,0,0,0,
                  0,0,1,0,3,1,1,1,0,0,0)) // ALC(neg) < L < ALCQI(cap,cup,neg) Allow! Thanks Birte - about "safe"!
  { 
   SATComplexity= (RCap>0)? hNE:hEX;
   SATComment='<ul><li><u>Hardness</u> holds even for <em>ALC</em>('+((RCap>0)?'&cap;,':'')+
              '&not;): see ['+LutzSattler2001+'].'+
               SafeBoolExp+'</ul>';
   return;
  }

  if(Logic(0,0,2,1)) // ALCNR + GCI
  { SATComplexity=iNE;
    SATComment='See ['+Buchheit_etal_1993a+'].';
    return;
  }

 }
} // End: Role operators

}else{  // Logics with Mu-Operator; no TBox cases (since TBox is internalized)

  if(Logic(0,0,0,reg)) // mu-ALC = ExpTime
  {
   SATComplexity=EX;
   SATComment='<ul><li>See ['+DeGiacomoLenzerini1997+',&nbsp;Theorem&nbsp;7].'
   +'<li>Corresponds to Propositional <i>&mu;</i>-Calculus from ['+Kozen1983+'].'
   +'<li>Contains the logic <em>ALC</em><sub>reg</sub> ['+DLBook+',&nbsp;p.204].</ul>';
   return;
  }

 var HardnessmuALC='<u>Hardness</u> for <em>&mu;ALC</em> is shown in&nbsp;['+DeGiacomoLenzerini1997+',&nbsp;Theorem&nbsp;7].';

  if(LogicInterval(0,0,1,reg, 0,0,3,reg)) // mu-ALCF < L < mu-ALCQ = ExpTime
  {
   SATComplexity=EX;
   SATComment='<ul>'
   +'<li>'+HardnessmuALC
   +'<li><u>Upper bound</u> for <em>&mu;ALCQ</em> is shown in&nbsp;['+DeGiacomoLenzerini1997+',&nbsp;Theorem&nbsp;9] for numbers coded in unary.'
   +'<li>The same upper bound was established in ['+KupfSatVardi2002+', Corollary&nbsp;1] even for numbers coded in binary.'
   +'</ul>';
   return;
  }

  if(LogicInterval(0,1,0,reg, 0,1,3,reg)) // mu-ALCI < L < mu-ALCIQ = ExpTime
  {
   SATComplexity=EX;
   SATComment='<ul>'
   +'<li>'+HardnessmuALC
   +'<li><u>Upper bound</u> for <em>&mu;ALCQI</em> is shown in&nbsp;['+CalvaneseEtAl1999c+'] for numbers coded in unary.'
   +'<li>The same upper bound was established in ['+BonattiLutzICALP06+'] even for numbers coded in binary.'
   +((FNQ==0)?'<li>Corresponds to modal <i>&mu;</i>-calculus with inverse from ['+Vardi1998+'].':'')
   +'</ul>';
   return;
  }

  if(LogicInterval(0,2,0,reg, 0,3,0,reg)) // mu-ALCO < L < mu-ALCIO = ExpTime
  {
   SATComplexity=EX;
   SATComment='<ul>'
   +'<li>'+HardnessmuALC
   +'<li><u>Upper bound</u> for <em>&mu;ALCIO</em> is shown in&nbsp;['+SattlerVardi2001+'].'
   +'<li>Corresponds to hybrid <i>&mu;</i>-calculus'+((II==1)? ' (with inverse).':'.')
   +'</ul>';
   return;
  }

  if(LogicInterval(0,2,1,reg, 0,2,3,reg)) // mu-ALCOF < L < mu-ALCOQ -- ExpTime --- Thanks Maja Milicic!
  {
   SATComplexity=EX;
   SATComment='<ul>'
   +'<li>'+HardnessmuALC
   +'<li><u>Upper bound</u> for <em>&mu;ALCQO</em> is shown in&nbsp;['+BonattiLutzICALP06+', Theorem&nbsp;10]'
   +((FNQ>1)?' even for numbers coded in binary.':'.')
   +'</ul>';
  }

  if(IO==3 && FNQ>0) // mu-ALCIOF is undecidable (and its extensions)
  {
   SATComplexity=UN;
   SATComment='<ul>'
   +'<li>Undecidability of <em>&mu;ALCFIO</em> is proved in ['+BonattiPeron2004+'], '
   +'even if &mu;-operators are not nested and functionality constructs '
   +'(&le;1&nbsp;<i>R</i>.T) are applied to atomic roles <i>R</i> only.'
   +'<li>Moverover, in presence of TBoxes (which are internalizable in extensions '
   +'of <em>&mu;ALC</em>, see ['+DeGiacomoLenzerini1997+',&nbsp;Theorem&nbsp;5]), '
   +'the functionality constructs can be restricted to occur only in TBox assertions '
   +'of the form <nobr>T&nbsp;&sube;&nbsp;(&le;1&nbsp;<i>R</i>.T)</nobr> stating that '
   +'the role <i>R</i> is functional.'
   +'<li>Under the above restriction, this logic corresponds to hybrid &mu;-calculus '
   +'with inverses and deterministic atomic programs.'
   '</ul>';
   return;
  }

} // End Mu-opers

} // End "No Complex Role Inclusions"
else // Complex Role Inclusions: RIQ, SRIQ, SROIQ
{    // Here all logics "contain" SH, i.e. (3,0,0,0). TBox is always internalized!


var CRI_Acyclic =
  '<li><u>Important</u>: a set of complex role inclusions (and ordinary role inclusions) '
 + 'is supposed to be <i>acyclic</i> (in a non-standard way). Otherwise the logic becomes '
 +'undecidable: see ['+HorrSattRIQ+',&nbsp;Theorem&nbsp;6].';


 if(MM==0)
 { // Logics without Mu-operator
 
  if(ROpers==0)
  { 
 
    if(LogicInterval(3,0,0,0, 3,1,3,0) && KK==0) // R < L < RIQ are decidable
    { SATComplexity=hNE+',<br>'+DE;
      SATComment   ='<ul>'
           +'<li><u>Hardness</u> follows from the result for <em>SHOIQ</em>.'
           +'<li>Decidability of <em>RIQ</em> is proved in ['+HorrSattRIQ+'].'
           +CRI_Acyclic
           +'<li>An undecidability result for a similar Description Logic <em>ALC</em><sub>&nbsp;<i>RA</i></sub> is obtained in ['+WesselDL2001+'].'
           +'<li>Closely related are <i>context-free</i> grammar (modal) logics, which are undecidable too ['+BaldoniPhD+',&nbsp;'+BaldoniTableaux98+'].'
           +'<li>Also closely related are logics with <i>role-value maps</i>, again undecidable ['+SchmidtSchauBKLONE89+'].'
           +'</ul>';
      return;
    }

    if(LogicInterval(3,0,0,0, 3,1,3,0) && KK==1) // sR < L < sRIQ are decidable
    { SATComplexity=hNE+',<br>'+DE;
      SATComment   ='<ul>'
           +'<li><u>Hardness</u> follows from the result for <em>SHOIQ</em>.'
           +'<li>Decidability of <em>sRIQ</em> is proved in ['+HorrKutzSattlerSRIQ+'].'
           +CRI_Acyclic
           +'<li>The additional features in <em>sRIQ</em> are: disjoint roles (for <i>simple</i> roles); reflexive and irreflexive roles (for <i>simple</i> roles); '
           +'expressions of the form &not;<i>aRb</i> in an ABox; concept constructor &exist;R.Self '
           +'(which could be written as <i>diag</i>(<i>R</i>) to avoid confusion, since Self is not a concept &#150; E.Z.).'
           +'</ul>';
      return;
    }

    if(LogicInterval(3,2,0,0, 3,3,3,0)) // ROIQ < L < sROIQ are decidable
    { SATComplexity=hNE+',<br>'+DE;
      SATComment   ='<ul>'
           +'<li><u>Hardness</u> follows from the result for <em>SHOIQ</em>.'
           +'<li>Decidability of <em>sROIQ</em> is proved in ['+HorrKutzSattlerSROIQ+'].'
           +CRI_Acyclic
           +'<li>The additional features in <em>sROIQ</em> are: disjoint roles; reflexive and irreflexive roles; '
           +'asymmetric roles (all these axioms are for <i>simple</i> roles only); universal role; '
           +'expressions of the form &not;<i>aRb</i> in an ABox; concept constructor &exist;R.Self '
           +'(which could be written as <i>diag</i>(<i>R</i>) to avoid confusion, since Self is not a concept &#150; E.Z.).'
           +(Logic(3,3,3,0)?'<li>The logic <em>sROIQ</em>(<i>D</i>) is the logical basis of the Web Ontology Language '
           +'ver.1.1 [<a target=_blank href=http://owl1_1.cs.manchester.ac.uk/>OWL&nbsp;1.1</a>]. '
           +'Note that the latter has additionally datatype properties, which are not covered by our DL Complexity Navigator.':'')
           +'</ul>';
      return;
    }

  } // end ROpers
 } // end if(MM==0)

}

// ------ Here are hardness (but not completeness) results ----------------------------------

if (IO==3 && FNQ>0) // Any extension of ALCFIO is NExpTime-hard
{
 SATComplexity=hNE;
 SATComment='<ul>'+ALCFIOhard+'</ul>';
 return;
}


}
