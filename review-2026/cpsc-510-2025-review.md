# cpsc-510 2025 review 

## Grading guidelines

(as posted on Github and Discord)

- [Table of Contents, Etc](https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/0-intro.html)
- **Review and Feedback:**
    - There are 20 points out of a hundred (see the syllabus on canvas) for "reading and giving feedback on other student's work." If you want these points you need to give me evidence here on discord in the chapter specific channels of the feedback you have given. Just drop your remarks there. Can include small things such as typos, tips on layout, style of writing, highlight sections that are unclear, really anything that improves a chapter ...
    - One thing I am looking for is evidence of actionable feedback as well as evidence that suggestions have been taken on board.
- [How to Contribute](https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/how-to-contribute.html)
- References:
    - [How to cite](https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/how-to-cite.html#citations)
    - Cite your sources in the text ... it is important that the reader has a sense of why a particular reference is listed. Do not just put all references you found ... It is good to have a long list of references but you need to explain why these references are interesting. For example, ask yourself: Why did you choose a particular reference and not another one? How do the chosen references relate to the rest of the chapter? What function do they accomplish? Do you list a reference as a recommendation for the reader to check out for themselves?  Does a reference serve the function of backing up with evidence some claim you made in the text? Etc.
- Do not have  only a single subsection in a section.
- Make sure that the numbering of sections works out.
- Inline clickable links that lead to further reading. If you look at https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/1-propositional-logic.html you see that I tried to make it easy for readers to access further information. You may find this tedious, but interesting inline links add a lot of value ... I see that one of the main ways many chapters can be improved is by inline linking interesting resources for further reading. I find this is one of the main characteristic of good blogs: Not even the content of its own, but the amount of interesting resources linked.
- Link source code and other resources
- Avoid long code snippets that are uninterrupted by interesting explanations.

---

## Spencer Au - Isabelle

**Typos**:
```
Line 269: "Learn" → "Lean"
```

**References:**
- Duplicate "Research Papers" section

---

## Wayne Chong - Z3

**ToC**: Missing sections on Algorithms, Benchmarks and Competitions, Future Work.

**Typos:**
```
443: `model (Z3Prover Team, 2025).This example` | `model (Z3Prover Team, 2025). This example` | Missing space after period |
551: `It is of interest to because` | `It is of interest because` | Grammatical error (extra "to") |
571: `Communications of the ACM(1962)` | `Communications of the ACM (1962)` | Missing space before year |
572: `TACAS(2008)` | `TACAS (2008)` | Missing space before year |
```

**References:**
- Many references were not in the standard format (missing years in parentheses, inconsistent author formatting, missing Google Scholar links)
- Some references were missing venues
- Several references cited in text were missing from References section:
  - Marques-Silva, Planes & Kutz (2008)
  - Matiyasevich (1970)
  - Tarski (1951)
  - Pirzada et al. (2024)
  - Lopes et al. (2021)

**Content:**
Sections 4.2.5, 4.2.6, 4.3 are from the [lecture notes](https://github.com/LEAP-at-Chapman/CPSC-510-Logical-Foundations-of-Computing/blob/ba008bc5c8880f9100c34ac01b3aaaf18cfdd418/content/5-smt-solving.md)
Section "4.4. Applications in the Industry" does not cite references
No inline links
The code snippets in Section 4.6 are too long. It is not clear what the reader is supposed to learn from them. 
Section "4.7. Conclusion" works well.
Single subsections 4.6.1, 4.7.1, 4.6.1.2.1.

---

## Jack de Bruyn - Spin

**ToC:** Follows the suggested ToC.

**Typos**:

```
Line 9:  "reasource" → "resource"
Line 60: "Excercise" → "Exercise"
Line 62: "recieves" → "receives" (appears twice in same sentence)
Line 104: "Excercise" → "Exercise"
Line 107: "fourmula" → "formula" (appears 4 times)
Line 109: "fourmulas" → "formulas" (appears 3 times)
Line 111: "FOURMULA" → "FORMULA"
Line 134: "probabalistic" → "probabilistic"
Line 134: "are contain" → "contain" (removed redundant "are")
Line 154: "infinitly" → "infinitely"
Line 156: "langauage" → "language"
Line 170: "concurecy" → "concurrency"
Line 170: "exculsion" → "exclusion"
Line 170: "reasource" → "resource" (appears 3 times in same paragraph)
Line 172: "tripple" → "triple"
Line 174: "efficeny" → "efficient"
Line 174: "interuptions" → "interruptions"
Line 174: "efficent" → "efficient"
Line 178: "Schroedor" → "Schroeder" (in section heading)
Line 182: "Schroedor" → "Schroeder" (in text)
Line 180: "ustilized" → "utilized"
Line 180: "secrect" → "secret" (appears twice)
Line 182: "Schroedor" → "Schroeder" (in text)
Line 202: "formailze" → "formalize"
Line 202: "This aim" → "The aim" (grammar fix)
Line 204: "offically" → "officially"
Line 208: "possiblities" → "possibilities"
Line 208: "revaluate" → "reevaluate"
Line 208: "assumtion" → "assumption"
Line 208: "develope" → "develop"
Line 212: "propterties" → "properties"
Line 214: "alegbras" → "algebras"
Line 222: "offically" → "officially"
Line 226: "brining" → "bringing"
Line 226: "disscusions" → "discussions"
Line 232: "develves" → "delves"
Line 249: "Reasources" → "Resources"
Line 250: "indepth" → "in-depth"
Line 29: "☐ A means that B must be true" → "☐ A means that A must be true" (corrected variable reference)
```

**Content:**
Section "5.4. Challenge Excercise: The Farmer and the River" does not contain any links to code for this example. It is not clear what the reader is meant to take away from this example.
Section "5.6. Algorithms" should contain more information. "not NP-complete" ... what then? One could also add sth about extending propositional tableaux to LTL.
Inline links in Section 5.8 work well.
Section 5.9: "A program that can be used to find this flaw is located here. This program was written by Professor Kurtz." The name "Kurtz" is misspelled and the information is wrong, as explained [here](https://github.com/LEAP-at-Chapman/Intro-to-Model-Checking-with-Spin/) and [here](https://github.com/LEAP-at-Chapman/Intro-to-Model-Checking-with-Spin/blob/main/notes/Needham-Schroeder.md) the code was written by Stephan Merz.
5.10: History stops in 1989.

## Matt Favela - Minizinc

**Table of Contents**

| Section | Notes/Reason if Missing |
|---------|-------------------------|
| The Landscape of Tools | No overview of constraint programming |
| Algorithms | Not present |
| Benchmarks and Competitions | Not present |
| Applications in Industry | Not present |
| History | Not present |
| Formal Methods and AI | Not present |
| Current Developments | Not present |
| Future Work | Not present |

The chapter covers the core content well (Idea, Basic Theory, Examples, Case Study) but is missing several important sections from the suggested TOC. 

**Content:** The structure and the writing can be improved. Examples:
- The example is somewhat isolated. What should the reader take away from the example?
![image](https://hackmd.io/_uploads/S1_Puy2E-g.png =400x)
It also would be good to link to examples the user can run and modify (learning by doing). 
- There are two sections called Employee (Shift) Scheduling. How do they hang together? Why does the first one mention N-Queens? 
- Why is 3.9 a separate section? All of 3.7-3.9 seem to belong together in one section. 
- One could add an interactive example using a Python notebook (see the Z3 chapter).

---

## Brandon Foley - Prolog

**Typos:**
```
"futher" → "further" (line 82)
"querys" → "queries" (line 160)
"empahsis" → "emphasis" (line 194)
"most best" → "best" (line 428)
double comma ",," → single comma "," (line 428)
"isnt" → "isn't" (line 31)
"its" → "it's" (line 536)
```

**References:**
- All references need to be reformatted to `Author(s) (Year) [Title](link), Venue`
- Most references don't have venues specified
- References do not have google scholar links
- References mix different citation styles
- Carlsson and Mildner (2012): Links to ResearchGate instead of Google Scholar
- Alberi (2021): Blog post - needs proper venue (blog name)
- Missing in-text citations

There are single subsections such as 2.2.1, 2.3.1

2.9 "The Water Jug Problem is a classic puzzle": lacks reference

2.10 History is lacking references

---

## John Mulhern

**Table of Contents**: "Future Work" missing

**Typos**:
Line 24: Fixed "lense" → "lens"
Line 729: Fixed "Referenes" → "References" 

**References**

- Bramblett et al. (2023) - "Epistemic Planning for Heterogeneous Robotic Systems" - In the References section but are NOT cited in the chapter text
- Muise et al. - "Epistemic Planning" (cited on line 645) but NOT in References
- van Ditmarsch (2000) - Cited on line 643 as "van Ditmarsch (2000)" for muddy children but NOT in References

Section 6.13 on Drone Rescue is an interesting idea but lacking substance.

---

## Khoa Nguyen

**Typos, etc**
"Dependent Type Theory(DTT)" - space (line 15)
methematics" → "mathematics" (line 16)
"Dependenty" → "Dependent" (line 21)
"pradigm" → "paradigm" (line 21)
"establising" → "establishing" (line 33)
"formal methids" → "formal methods" (line 72)
"methematics" → "mathematics", "verfication" →"verification" (line 120)
"aument" → "augment", "theorm" → "theorem" (line 236)
"the author identify" → "the authors identify" (line 240)
"compile" → "compiles" (line 248)
"the author argues" → "the authors argue" (line 250)
"indepthly" → "in depth", "was" → "were" (line 648)
"proof assistants handle" → "how proof assistants handle" (line 120)

**References:**

The following appear to be uncited references:
- Barnes (2011) - mentioned in text but not cited
- Ganesh, Seshia, and Jha (2022) - mentioned in text but not cited
- Gleirscher and Marmsoler (2020) - mentioned in text but not cited
- Groote and Huisman (2024) - mentioned in text but not cited
- Iliasov et al. (2021) - mentioned in text but not cited
- Miranda et al. (2025) - mentioned in text but not cited
- Singh et al. (2019) - mentioned in text but not cited
- Stock, Dunkelau, and Mashkoor (2025) - mentioned in text but not cited
- Wadler (2015) - not cited
- Bauer and Komel (2020) - not cited
- de Moura et al. (2021) - not cited
- Dunfield and Krishnaswami (2021) - not cited
- Ebner et al. (2017) - not cited
- Felicissimo (2024) - not cited
- Ko and Gibbons (2024) - not cited
- Maybe others

**Content:**

One of the most complete chapters and one of the few that developed their own case study.

---

## Jack Triester

Table of Contents follows outline.

Typos:
```
"considered to the open source"  → "considered to be the open source" (line 129)
"tha" → "that" (line 401)
"spitting" → "splitting" (line 409)
"benefical" → "beneficial" (lines 409, 542)
"f=part" → "part" (line 409)
"auxillary" → "auxiliary" (line 542)
"in better" → "is better" (line 542)
"satifying" → "satisfying" (line 11)
"unsatifiable" → "unsatisfiable" (line 14)
"impliation" → "implication" (line 387)
"sudoku.py" → "sudoku-encode.py" (line 462)
"Contributers" → "Contributors" (line 586)
```

**References**:
| Alouneh et al. (2019) | Missing link entirely |
| Froleyks, Yu, and Biere (2023) | Missing link entirely |
| Sun et al. (2025) | Should link to Google Scholar |

- Some references are in subsections, others are not? What is the organizational principle here?
- Why is "Biere, Heule, Van Maaren, and Walsh (2021). Handbook of Satisfiability, Frontiers in Artificial Intelligence and Applications" under "Early Work"?
- Some references do not specify the venue.
- Missing in-text citations

**Content:**

Style is somewhat informal. Too informal for a book?

There are single subsections such as 1.7.1, 1.13.1

The case study is taken from a website, not an original development.

Section 1.8 is too short.

---

## Alex Zermeno - Dafny

**Table of Contents**: The chapter covers most of the suggested TOC sections. The main gaps are:
- Algorithms: Could benefit from explaining how Dafny's verification algorithms work (e.g., weakest precondition calculus, SMT solving)
- Typical Use Cases: While applications are covered, a dedicated section on typical use cases would be helpful
- Case Study: A complete case study showing verification of a real-world program would strengthen the chapter
- Formal Methods and AI: Mentioned in Future Work but could be expanded into its own section
- Current Developments: Could add a section on recent advances in Dafny and Hoare Logic tools
- Contributors: Should add a Contributors section per the TOC guidelines

**Typos, etc:**
```
typo: "Dafyny" → "Dafny" (line 225)
technical error: "precondition C" → "precondition P" (line 21)
technical error: "program P" → "program S", "precondition C" → "precondition P" (line 438)
grammar: "implement Hoare Logic" → "systems implement Hoare Logic" (line 426)
grammar: "reason all program states" → "reason about all program states" (line 430)
reference formatting: "Krzysztof and Ernst-Rudiger" → "Apt and Olderog" (line 472)
reference formatting: "Josh Rushby" → "Rushby" (line 474)
reference formatting: "Alex Cappiello" → "Cappiello" (line 476)
reference formatting: "Rustan and Leino" → "Leino" (line 480)
reference formatting: "Alexander Kurz" → "Kurz" (line 470)
```

**Layout and Organization:**

Numbering is wrong in

![image](https://hackmd.io/_uploads/HJCi0ScV-x.png =300x)

**References:**

Dont follow the specified format. 

The section on F* does not contain any references or links for further reading.

Some references are not cited in the main text
```
Kurz (2022) - HackMD tutorial on Hoare Logic examples
Apt and Olderog (2019) - "Fifty Years of Hoare's Logic"
Pierce et al. (2024) - Software Foundations Volume 2
Dafny Project (2024) - Dafny Reference Manual
```




