# Complexity Classes Overview

| Class | Definition | Complete Problem | Key Reference | DL Example |
|-------|-----------|------------------|---------------|------------|
| **AC⁰** | Constant depth circuits | | | DL-Lite query answering |
| **L** | Log space | Boolean Formula Evaluation | | |
| **NL** | Nondeterministic log space | 2-SAT | Savitch (1970) | DL-Lite concept satisfiability |
| **P** | Polynomial time | Horn-SAT, Circuit Value Problem | Cobham (1965) | EL, EL++ reasoning |
| **NP** | Nondeterministic polynomial time | SAT, 3-SAT | Cook (1971) | |
| **co-NP** | Complement of NP | Tautology, Unsatisfiability | | ALC concept satisfiability (acyclic TBox) |
| **PSPACE** | Polynomial space | QBF (TQBF) | Savitch (1970) | ALC concept satisfiability |
| **EXPTIME** | Exponential time | Succinct Circuit Value Problem | Hartmanis & Stearns (1965) | ALC + GCIs, SHIQ, SHOIN (OWL DL) |
| **NEXPTIME** | Nondeterministic exponential time | Succinct SAT | | SHOIQ |
| **co-NEXPTIME** | Complement of NEXPTIME | Succinct Tautology | | |
| **2-EXPTIME** | Double exponential time | Presburger Arithmetic | Fischer & Rabin (1974) | |
| **N2EXPTIME** | Nondeterministic double exponential time | | | SROIQ (OWL 2 DL) |

## DL Complexity Summary

| Description Logic | Complexity | Reference |
|-------------------|------------|-----------|
| DL-Lite | AC⁰ / NL | Calvanese et al. (2007) |
| EL++ | P | Baader et al. (2005) |
| ALC | PSPACE / EXPTIME | Schmidt-Schauß & Smolka (1991) |
| SHIQ | EXPTIME | Tobies (2001) |
| SHOIQ | NEXPTIME | Tobies (2001) |
| SROIQ | N2EXPTIME | Kazakov (2008) |

---

## References

### Foundational Complexity Theory

- Cobham (1965): [The Intrinsic Computational Difficulty of Functions](https://scholar.google.com/scholar?q=Cobham+Intrinsic+Computational+Difficulty+Functions+1965)
- Edmonds (1965): [Paths, Trees, and Flowers](https://scholar.google.com/scholar?q=Edmonds+Paths+Trees+Flowers+1965)
- Hartmanis & Stearns (1965): [On the Computational Complexity of Algorithms](https://scholar.google.com/scholar?q=Hartmanis+Stearns+Computational+Complexity+Algorithms+1965)
- Savitch (1970): [Relationships Between Nondeterministic and Deterministic Tape Complexities](https://scholar.google.com/scholar?q=Savitch+Relationships+Nondeterministic+Deterministic+Tape+1970)
- Cook (1971): [The Complexity of Theorem-Proving Procedures](https://scholar.google.com/scholar?q=Cook+Complexity+Theorem+Proving+Procedures+1971)
- Levin (1973): [Universal Sequential Search Problems](https://scholar.google.com/scholar?q=Levin+Universal+Sequential+Search+Problems+1973)
- Fischer & Rabin (1974): [Super-Exponential Complexity of Presburger Arithmetic](https://scholar.google.com/scholar?q=Fischer+Rabin+Super+Exponential+Presburger+Arithmetic+1974)
- Stockmeyer & Meyer (1973): [Word Problems Requiring Exponential Time](https://scholar.google.com/scholar?q=Stockmeyer+Meyer+Word+Problems+Exponential+Time+1973)
- Immerman (1988): [Nondeterministic Space is Closed Under Complementation](https://scholar.google.com/scholar?q=Immerman+Nondeterministic+Space+Closed+Complementation+1988)
- Szelepcsényi (1988): [The Method of Forced Enumeration for Nondeterministic Automata](https://scholar.google.com/scholar?q=Szelepcs%C3%A9nyi+Forced+Enumeration+Nondeterministic+Automata+1988)

### Description Logics

- Schmidt-Schauß & Smolka (1991): [Attributive Concept Descriptions with Complements](https://scholar.google.com/scholar?q=Schmidt-Schau%C3%9F+Smolka+Attributive+Concept+Descriptions+Complements+1991)
- Tobies (2001): [Complexity Results and Practical Algorithms for Logics in Knowledge Representation](https://scholar.google.com/scholar?q=Tobies+Complexity+Results+Practical+Algorithms+Logics+Knowledge+Representation+2001)
- Baader et al. (2005): [Pushing the EL Envelope](https://scholar.google.com/scholar?q=Baader+Pushing+EL+Envelope+2005)
- Calvanese et al. (2007): [Tractable Reasoning and Efficient Query Answering in Description Logics: The DL-Lite Family](https://scholar.google.com/scholar?q=Calvanese+Tractable+Reasoning+Efficient+Query+Answering+DL-Lite+2007)
- Kazakov (2008): [RIQ and SROIQ Are Harder than SHOIQ](https://scholar.google.com/scholar?q=Kazakov+RIQ+SROIQ+Harder+SHOIQ+2008)

### Textbooks & Surveys

- Arora & Barak (2009): [Computational Complexity: A Modern Approach](https://scholar.google.com/scholar?q=Arora+Barak+Computational+Complexity+Modern+Approach)
- Papadimitriou (1994): [Computational Complexity](https://scholar.google.com/scholar?q=Papadimitriou+Computational+Complexity+1994)
- Baader et al. (2003): [The Description Logic Handbook](https://scholar.google.com/scholar?q=Baader+Description+Logic+Handbook+2003)

---

Want me to add more references for specific areas (e.g., circuit complexity, query complexity, or specific DL fragments)?