# Epistemic Logic with SMCDEL

*Author: John*

## Introduction

This chapter explores epistemic logic using SMCDEL (Symbolic Model Checker for Dynamic Epistemic Logic), investigating how knowledge and belief can be formally modeled and applied to social network analysis.

## Topics

- Epistemic logic foundations
- Knowledge and belief operators
- SMCDEL installation and usage
- Social network modeling
- Dynamic epistemic logic
	## Epistemic Logic in Hintikka's Knowledge and Belief
	### Possible Worlds Semantics
        - Epistemic logic introduces accessibility relations tied to an agent’s epistemic state.
        - For knowledge: the agent “knows φ” if φ holds in all worlds accessible from the actual world (all worlds the agent considers possible).
        - For belief: the condition is weaker; the agent “believes φ” if φ holds in all worlds compatible with the agent’s belief system, which need not exclude false ones.
    ### Properties of Knowledge
        - Knowledge is modeled as stronger than belief:
            - It is factive (Kφ → φ).
            - Often taken as closed under logical consequence (if Kφ and K(φ → ψ), then Kψ).
        - These features generate rich logical structures but also raise philosophical puzzles, such as the “logical omniscience problem”—the unrealistic assumption that if someone knows φ and φ implies ψ, they must also know ψ.
    ### Properties of Belief
        - Belief systems are internally consistent (ideally, an agent doesn’t believe both φ and ¬φ).
        - But they allow for error: an agent can believe something false.
        - Epistemic logic provides tools to model rational but fallible agents.
    ### Interplay of Knowledge and Belief
        - Hintikka analyzes questions like:
            - Does knowledge imply belief? 
                (Many systems assume Kφ → Bφ.)
            - Can beliefs upgrade to knowledge under stronger conditions?
            - How do we formally capture the gap between “true justified belief” and knowledge (anticipating later epistemological debates like the Gettier problem)?

## Resources

- [SMCDEL](https://w4eg.de/malvin/illc/smcdelweb/index.html)
- [Epistemic Logic Explorer](https://vezwork.github.io/modallogic/?model=;AS?formula=_)
- [Hintikka's Knowledge and Belief](https://archive.org/details/knowledgebeliefi00hint_0)

## Exercises

"Test changes to prove access"

*To be added*
