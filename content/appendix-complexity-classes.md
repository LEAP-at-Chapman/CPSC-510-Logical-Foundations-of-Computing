# Complexity Classes Overview

(draft, needs verification and more work)

See also [Complexity of reasoning in Description Logics](https://www.cs.man.ac.uk/~ezolin/dl/)

| Class | Definition | Complete Problem | Key Reference | DL Example | Logics in Book |
|-------|-----------|------------------|---------------|------------|----------------|
| **AC⁰** | Constant depth circuits | | | DL-Lite query answering | Propositional Logic (basic evaluation) |
| **L** | Log space | Boolean Formula Evaluation | | | Propositional Logic (formula evaluation) |
| **NL** | Nondeterministic log space | 2-SAT | Savitch (1970) | DL-Lite concept satisfiability | 2-SAT (Propositional Logic fragment) |
| **P** | Polynomial time | Horn-SAT, Circuit Value Problem | Cobham (1965) | EL, EL++ reasoning | Horn-SAT (Propositional Logic fragment) |
| **NP** | Nondeterministic polynomial time | SAT, 3-SAT | Cook (1971) | | SAT (Propositional Logic), Constraint Satisfaction (CSP) |
| **co-NP** | Complement of NP | Tautology, Unsatisfiability | | ALC concept satisfiability (acyclic TBox) | Tautology checking (Propositional Logic) |
| **PSPACE** | Polynomial space | QBF (TQBF) | Savitch (1970) | ALC concept satisfiability | Modal Logic, Temporal Logic (LTL model checking), Epistemic Logic |
| **EXPTIME** | Exponential time | Succinct Circuit Value Problem | Hartmanis and Stearns (1965) | ALC + GCIs, SHIQ, SHOIN (OWL DL) | SMT Solving (many theories), Temporal Logic (CTL model checking) |
| **NEXPTIME** | Nondeterministic exponential time | Succinct SAT | | SHOIQ | |
| **co-NEXPTIME** | Complement of NEXPTIME | Succinct Tautology | | | |
| **2-EXPTIME** | Double exponential time | Presburger Arithmetic | Fischer and Rabin (1974) | | SMT Solving (Presburger Arithmetic) |
| **N2EXPTIME** | Nondeterministic double exponential time | | | SROIQ (OWL 2 DL) | |

## Note on Undecidable Logics

Some logics covered in this book are **undecidable** (or **semi-decidable**) and thus do not appear in the complexity class table above:

- **First-Order Logic (FOL)**: Undecidable (though many decidable fragments exist, such as those used in SMT)
- **Higher-Order Logic (HOL)**: Undecidable (though type checking in HOL-based systems like Isabelle/HOL is decidable)
- **Dependent Type Theory**: Type checking is decidable, but theorem proving is semi-decidable
- **Hoare Logic**: Program verification is undecidable in general (though specific fragments and bounded verification are decidable)
- **Full Prolog**: Semi-decidable (though Datalog, a decidable subset, is EXPTIME-complete)

The table above focuses on **decidable problems** for which we can give precise complexity bounds.

## DL Complexity Summary

| Description Logic | Complexity | Reference |
|-------------------|------------|-----------|
| DL-Lite | AC⁰ / NL | Calvanese et al. (2007) |
| EL++ | P | Baader et al. (2005) |
| ALC | PSPACE / EXPTIME | Schmidt-Schauß and Smolka (1991) |
| SHIQ | EXPTIME | Tobies (2001) |
| SHOIQ | NEXPTIME | Tobies (2001) |
| SROIQ | N2EXPTIME | Kazakov (2008) |

---

## References

### Foundational Complexity Theory

- Hartmanis and Stearns (1965) [On the Computational Complexity of Algorithms](https://scholar.google.com/scholar?q=Hartmanis+Stearns+Computational+Complexity+Algorithms+1965), Journal of the ACM.
- Savitch (1970) [Relationships Between Nondeterministic and Deterministic Tape Complexities](https://scholar.google.com/scholar?q=Savitch+Relationships+Nondeterministic+Deterministic+Tape+1970), Journal of Computer and System Sciences.
- Cook (1971) [The Complexity of Theorem-Proving Procedures](https://scholar.google.com/scholar?q=Cook+Complexity+Theorem+Proving+Procedures+1971), STOC.
- Levin (1973) [Universal Sequential Search Problems](https://scholar.google.com/scholar?q=Levin+Universal+Sequential+Search+Problems+1973), Problems of Information Transmission.
- Fischer and Rabin (1974) [Super-Exponential Complexity of Presburger Arithmetic](https://scholar.google.com/scholar?q=Fischer+Rabin+Super+Exponential+Presburger+Arithmetic+1974), Proceedings of the AMS.
- Stockmeyer and Meyer (1973) [Word Problems Requiring Exponential Time](https://scholar.google.com/scholar?q=Stockmeyer+Meyer+Word+Problems+Exponential+Time+1973), STOC.
- Immerman (1988) [Nondeterministic Space is Closed Under Complementation](https://scholar.google.com/scholar?q=Immerman+Nondeterministic+Space+Closed+Complementation+1988), SIAM Journal on Computing.
- Szelepcsényi (1988) [The Method of Forced Enumeration for Nondeterministic Automata](https://scholar.google.com/scholar?q=Szelepcs%C3%A9nyi+Forced+Enumeration+Nondeterministic+Automata+1988), Acta Informatica.

### Description Logics

- Schmidt-Schauß and Smolka (1991) [Attributive Concept Descriptions with Complements](https://scholar.google.com/scholar?q=Schmidt-Schau%C3%9F+Smolka+Attributive+Concept+Descriptions+Complements+1991), Artificial Intelligence.
- Tobies (2001) [Complexity Results and Practical Algorithms for Logics in Knowledge Representation](https://scholar.google.com/scholar?q=Tobies+Complexity+Results+Practical+Algorithms+Logics+Knowledge+Representation+2001), Journal of Artificial Intelligence Research.
- Baader et al. (2005) [Pushing the EL Envelope](https://scholar.google.com/scholar?q=Baader+Pushing+EL+Envelope+2005), IJCAI.
- Calvanese et al. (2007) [Tractable Reasoning and Efficient Query Answering in Description Logics: The DL-Lite Family](https://scholar.google.com/scholar?q=Calvanese+Tractable+Reasoning+Efficient+Query+Answering+DL-Lite+2007), Journal of Automated Reasoning.
- Kazakov (2008) [RIQ and SROIQ Are Harder than SHOIQ](https://scholar.google.com/scholar?q=Kazakov+RIQ+SROIQ+Harder+SHOIQ+2008), KR.

### Textbooks & Surveys

- Arora and Barak (2009) [Computational Complexity: A Modern Approach](https://scholar.google.com/scholar?q=Arora+Barak+Computational+Complexity+Modern+Approach), Cambridge University Press.
- Papadimitriou (1994) [Computational Complexity](https://scholar.google.com/scholar?q=Papadimitriou+Computational+Complexity+1994), Addison-Wesley.
- Baader et al. (2003) [The Description Logic Handbook](https://scholar.google.com/scholar?q=Baader+Description+Logic+Handbook+2003), Cambridge University Press.

