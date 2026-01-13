
# Epistemic Logic with SMCDEL

Author: *John Mulhern*

## Idea

Epistemic logic is the study of **knowledge** and **belief** using a formal logical language ([Hintikka, 1962](https://scholar.google.com/scholar?q=Hintikka+Knowledge+and+Belief)). Instead of only asking “is `p` true?”, we can ask:

- “does agent `a` know that `p` is true?” (`K_a p`)
- “does agent `a` believe that `p` is true?” (`B_a p`)
- “does agent `a` know that agent `b` knows that `p`?” (`K_a K_b p`)

This is useful in computer science because many systems are **multi-agent** or **distributed**. What an individual process, user, or node **knows** (or does **not** know) affects what it can safely and effectively do ([Halpern and Moses, 1990](https://scholar.google.com/scholar?q=Knowledge+and+Common+Knowledge+in+a+Distributed+Environment)).

Epistemic logic is motivated by a simple but profound observation: in many systems, what matters is not merely what is true but what agents think is true. Whether we examine human communication, negotiation between strategic players, or computation in networked software agents, the ability to reason about an entity’s informational state becomes central. Questions such as “what does the system know about its environment?” or “what can a user infer from a public disclosure?” characterize modern cybersecurity, distributed systems, and artificial intelligence. Thus epistemic logic provides a formal language to articulate and analyze these questions rigorously, giving us a way to represent knowledge differences, detect misinformation, model secrecy, and reason about what becomes knowable as communication unfolds ([van Ditmarsch, van der Hoek, and Kooi, 2007](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logic+van+Ditmarsch+van+der+Hoek+Kooi)).

Feel free to peek ahead for the {ref}`muddy children puzzle <muddy-children>`.

## In this chapter we will:

1. dive into the history of epistemic logic,
2. introduce the basics of (multi-agent) epistemic logic,
3. introduce *dynamic* epistemic logic (DEL) to handle information change,
4. show how to use **SMCDEL** (Symbolic Model Checker for Dynamic Epistemic Logic),
5. explain **social networks** through the lens of epistemic logic

## History

The story of epistemic logic begins not in computer science, but in philosophy—specifically, in a moment when logicians first wondered whether knowledge itself could be treated with the same mathematical precision as truth. In the early 1960s, Jaakko Hintikka proposed a bold idea that reshaped the field: if we can speak formally about what is true, we should also be able to speak formally about what an agent knows to be true. His seminal work introduced modal operators such as K_a φ, and with them a logic that captured the structure of knowledge through the lens of “possible worlds” [(Hintikka, 1962)](https://scholar.google.com/scholar?q=Hintikka+Knowledge+and+Belief). In one stroke, Hintikka gave us a language for expressing uncertainty, inference, ignorance, and introspection—with the rigor of classical logic.

Through the 1970s and 1980s, epistemic logic matured alongside another major development: the rise of Kripke semantics. Saul Kripke's relational semantics provided clarity and precision to modal logic, grounding Hintikka’s insights in a framework where knowledge corresponded to accessibility between worlds [(Kripke, 1963)](https://scholar.google.com/scholar?q=Kripke+semantical+considerations+modal+logic+1963). These frames became powerful tools, capable of describing anything from the beliefs of a single agent to the mutual awareness of large groups. Researchers like Halpern and Moses soon recognized another profound application: distributed systems. In their influential 1990 paper, they observed that many coordination problems hinge not merely on what processes know, but on what they know about the knowledge of others ([Halpern and Moses, 1990](https://scholar.google.com/scholar?q=Knowledge+and+Common+Knowledge+in+a+Distributed+Environment)). This insight forged the first deep connection between epistemic logic and computer science.

While epistemic logic had established itself as a rich static theory, its dynamic nature—how knowledge changes—remained elusive. That changed in the 1990s. Alexandru Baltag, Lawrence Moss, and Slawomir Solecki, building on earlier work by Plaza on public announcement logic [(Plaza, 1989)](https://scholar.google.com/scholar?q=Plaza+Logic+of+Public+Announcements), developed what we now call Dynamic Epistemic Logic (DEL). Their breakthrough was to treat communication events themselves as mathematical objects: not just “messages sent,” but structured transformations of epistemic models. A public announcement, a whispered secret, a shared observation—all could be described as actions that reshape the possibilities agents consider. The importance of this shift cannot be overstated: DEL made information flow first-class, allowing researchers to reason formally about communication, misinformation, secrecy, and coordinated decision-making ([Baltag, Moss, and Solecki, 1998](https://scholar.google.com/scholar?q=The+Logic+of+Public+Announcements+Common+Knowledge+and+Private+Suspicions); [Baltag, Moss, and Solecki, 2004](https://scholar.google.com/scholar?q=The+Logic+of+Epistemic+Actions)).

With the arrival of the 2000s came a new challenge: could these elegant theories be implemented? Could machines reason about knowledge the way logicians did on paper? The development of explicit-state model checkers such as MCK and tools like DEMO marked the first serious attempts to bring epistemic logic into computational practice [(Baldoni et al., 1998)](https://scholar.google.com/scholar?q=Model+Checking+Knowledge+and+Time). Soon after, the logic-and-AI renaissance led by Johan van Benthem, together with Hans van Ditmarsch, Jan van Eijck, and many others, provided the theoretical and algorithmic foundation needed to make epistemic model checking more efficient, more expressive, and more widely applicable [(van Ditmarsch, van der Hoek, and Kooi, 2007)](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logic+van+Ditmarsch+van+der+Hoek+Kooi). Their work laid the groundwork for symbolic representations of epistemic structures and for a deeper understanding of dynamic logics as computational artifacts.

In 2016, the field crossed a major milestone with the introduction of SMCDEL, the first fully symbolic model checker for Dynamic Epistemic Logic. Leveraging Binary Decision Diagrams (BDDs), SMCDEL scaled DEL reasoning to models containing thousands or millions of states—sizes previously unreachable for explicit methods. For the first time, researchers could explore nontrivial multi-agent communication scenarios interactively, observing how knowledge changed step by step, update by update. SMCDEL didn’t just implement DEL; it demonstrated its computational viability [(van Benthem, van Eijck, Gattinger, and Su, 2016)](https://scholar.google.com/scholar?q=Symbolic+Model+Checking+for+Dynamic+Epistemic+Logic).

The most recent chapter in this story emerges from an unexpected direction: artificial intelligence. As large language models and multi-agent AI systems proliferate, epistemic logic has found itself at the center of questions about belief modeling, theory of mind, explainability, and communication among autonomous systems. DEL-based reasoning tasks are now used to test the social inference capabilities of generative models ([Sileo et al., 2023](https://scholar.google.com/scholar?q=Targeting+Theory+of+Mind+Dynamic+Epistemic+Logic); [Wu et al., 2025](https://scholar.google.com/scholar?q=Inference-Time+Scaling+for+Theory+of+Mind+LLM)). Neurosymbolic architectures pair generative agents that produce hypotheses with epistemic modules that verify or correct them [(Fierro et al., 2024)](https://scholar.google.com/scholar?q=Bridging+Epistemology+and+Large+Language+Models). Meanwhile, robotics researchers use epistemic models to ensure that swarms, drones, and autonomous vehicles coordinate safely in environments saturated with partial information and unreliable communication ([Soldà et al., 2022](https://scholar.google.com/scholar?q=e-PICO+epistemic+reasoner+collaborative+robots); [Gielis et al., 2022](https://scholar.google.com/scholar?q=Critical+Review+of+Communications+in+Multi-Robot+Systems)).

From philosophical curiosity to formal semantics, from dynamic reasoning to symbolic computation, and now into the age of generative AI, the history of epistemic logic is a progression toward greater expressive power and deeper computational relevance. What began as an abstract theory of knowledge has grown into a foundational tool for understanding how information flows in interactive, intelligent, and increasingly autonomous systems.

## Basic Epistemic Logic

### Syntax

The syntax of epistemic logic expands propositional logic by equipping it with operators that express informational attitudes. Rather than merely stating that a fact holds, epistemic logic allows us to articulate perspectives on truth — what each agent takes to be the case, what they rule out, and how they reflect on their own knowledge state. This syntactic extension is minimalist by design: a small number of new operators yields an expressive language capable of capturing secrecy, inference, deception, and shared knowledge among distributed agents.

For example, we assume:

- a set of atomic propositions: `p, q, r, ...`
- a finite set of agents: `a, b, c, ...`

The language is built by:

- every atomic proposition `p` is a formula
- if `φ` and `ψ` are formulas, then

  - `¬φ`
  - `(φ ∧ ψ)`
  - `(φ ∨ ψ)`
  - `(φ → ψ)`

  are formulas

- if `φ` is a formula and `a` is an agent, then

  - `K_a φ` is a formula, read “agent `a` knows that `φ`”

Optionally we can also allow:

- `B_a φ` for “agent `a` believes that `φ`”

Examples:

- `K_a p`
- `K_a K_b p`
- `K_a (p → q)`
- `K_a p ∧ K_b p`
- `K_a p → B_a p` (knowledge implies belief)


### Semantics (Possible Worlds)

Epistemic logic uses **possible worlds semantics** [(Kripke semantics)](https://scholar.google.com/scholar?q=Kripke+semantical+considerations+modal+logic+1963).

A model is a triple:

- `M = (W, {R_a}_a, V)`

where:

1. `W` is a nonempty set of **worlds**
2. for each agent `a`, `R_a` is a binary relation on `W`
   - `(w, w') ∈ R_a` means: *at world `w`, agent `a` considers world `w'` possible*
3. `V` is a valuation assigning to every atomic proposition the set of worlds where it is true

We define truth at a world `w` inductively:

- `M, w ⊨ p` iff `w ∈ V(p)`
- `M, w ⊨ ¬φ` iff **not** (`M, w ⊨ φ`)
- `M, w ⊨ (φ ∧ ψ)` iff (`M, w ⊨ φ` **and** `M, w ⊨ ψ`)
- `M, w ⊨ (φ ∨ ψ)` iff (`M, w ⊨ φ` **or** `M, w ⊨ ψ`)
- `M, w ⊨ (φ → ψ)` iff (if `M, w ⊨ φ` then `M, w ⊨ ψ`)
- `M, w ⊨ K_a φ` iff for **all** `w'` such that `(w, w') ∈ R_a`, we have `M, w' ⊨ φ`

Key sentence:

> `K_a φ` is true at `w` iff `φ` is true in **all** worlds that agent `a` considers possible from `w`.

### Example (Not Knowing Even When It’s True)

Let there be 2 worlds: `w1`, `w2`.

- in `w1`, `p` is true
- in `w2`, `p` is false

Let agent `a` be **uncertain** between these 2 worlds:

- `R_a = {(w1,w1), (w1,w2), (w2,w1), (w2,w2)}`

Then:

- `M, w1 ⊨ p` (because `p` is true in `w1`)
- but `M, w1 ⊭ K_a p` (because from `w1`, agent `a` also considers `w2` possible, and in `w2` `p` is false)

So: `p` is actually true, but agent `a` does **not** know `p`.

### Properties of Knowledge (S5-style)
These S5 principles constitute a kind of “idealized epistemic agent.” Knowledge is factual, agents perfectly reflect on what they know, and lacking knowledge is itself a known state. While these assumptions prove analytically convenient — particularly in security or distributed systems where local state is perfectly introspectable — they are not universally appropriate. Human reasoners, machine learning systems, and bounded computational agents often violate introspection or even factivity. Thus S5 serves as a baseline theory upon which weaker or alternative epistemic logics can be constructed. In many CS applications, we model knowledge with S5-like properties. 

For each agent `a`, the relation `R_a` is:

- reflexive
- symmetric
- transitive

This validates the following principles:

1. **Factivity**: `K_a φ → φ`
2. **Positive introspection**: `K_a φ → K_a K_a φ`
3. **Negative introspection**: `¬K_a φ → K_a ¬K_a φ`
4. **Distribution**: `K_a (φ → ψ) → (K_a φ → K_a ψ)`

These together make knowledge quite strong.

### Belief

Belief (`B_a φ`) is often taken to be **weaker**:

- belief is **not** factive (we do **not** assume `B_a φ → φ`)
- we can still assume doxastic introspection (depending on the logic)
- often we assume: `K_a φ → B_a φ` (knowledge implies belief)

Belief is handy for modeling **mistakes** or **rumors** in social networks.

## Dynamic Epistemic Logic (DEL)

So far: *static* epistemic logic — one model, we ask what is known.

But many real situations have **information change**:

- a public announcement
- a private message
- an observation
- an agent discovering a fact

**Dynamic Epistemic Logic** adds **events** and **updates** to represent such changes.

Dynamic epistemic logic begins from a deep insight: knowledge changes. Our epistemic state is shaped not only by what the world is but also by what we learn, observe, forget, or misinterpret. DEL formalizes information events — announcements, observations, private communication — and studies how they transform possible-world structures. DEL allows reasoning about what becomes knowable after a rumor spreads, when a protocol message is broadcast, or how shared secrets propagate through a network.

**Public Announcement (Informal)**

Suppose we have a model `M` and we publicly announce `φ`.

- every agent hears the same announcement
- every agent trusts it (it becomes true, or was already true)
- so they **eliminate** all worlds in which `φ` was false
- result: a new epistemic model with fewer worlds

After this, many things that were **not** known become **known**, because there are fewer possibilities left.

This is exactly the kind of update SMCDEL is good at checking.

## The Landscape of Tools

Epistemic logic sits at the intersection of modal logic, distributed systems theory, and multi-agent reasoning, and over the past two decades it has given rise to a diverse ecosystem of tools. Each tool reflects a different philosophical or computational stance—whether emphasizing explicit-state exploration, symbolic verification, interactive proof, or planning under uncertainty. Understanding this landscape clarifies where SMCDEL fits and what makes it distinct.

Broadly, epistemic tools fall into four families: **model checkers**, **interactive theorem provers**, **epistemic planners**, and **AI-oriented reasoning systems**. Each family implements a different slice of the epistemic reasoning pipeline, and together they form a cohesive ecosystem.

### Model Checkers

Traditional epistemic model checkers follow the pattern of explicit exploration: they enumerate worlds, track accessibility relations, and evaluate formulas directly over that structure. Tools like [**MCK**](https://www.csse.canterbury.ac.nz/mck/) are representative of this approach. Given a Kripke model and an epistemic-temporal formula, MCK systematically checks whether the formula holds in the initial state. Conceptually, this evaluation can be sketched as:

```text
function ExplicitModelCheck(M, φ):
    for each world w in M.W:
        M.truth[w] := EvaluateFormula(M, w, φ)
    return M.truth
```

Although straightforward, explicit exploration becomes costly as models grow. Nevertheless, these tools provide clear insight into epistemic structures and are useful for protocol analysis, security examples, and small multi-agent scenarios.

Another branch of this family includes tools such as [**DEMO**](http://people.uleth.ca/~kooi/del/) and DEMO-S5, which focus on dynamic epistemic models and support visualization of DEL updates. They excel in educational and conceptual settings, where visualizing product updates and information flow is as important as the raw computation.

### Interactive Theorem Provers

A different approach embeds epistemic logic inside a higher-order proof environment such as [**Isabelle/HOL**](https://isabelle.in.tum.de/) or [**Coq**](https://coq.inria.fr/). Here, epistemic reasoning is not automated model checking but rather formal deduction about epistemic principles. These systems allow the user to define Kripke structures, prove lemmas about knowledge, establish impossibility results (such as the Coordinated Attack theorem), and verify security protocols.

A typical proof workflow might look like:

```
theory Epistemic_Example
begin

datatype world = w1 | w2

definition R_a where
  "R_a = {(w1, w1), (w1, w2), (w2, w1), (w2, w2)}"

lemma KnowsImpliesTruth:
  assumes "M, w ⊨ K_a φ"
  shows "M, w ⊨ φ"
  using assms unfolding semantics_of_K
  by auto

end
```

Interactive theorem provers give maximal rigor and flexibility, though at the cost of heavy manual involvement.

### Epistemic Planners

A more recent development comes from the AI planning community, where epistemic logic is used to model actions whose effects depend on agents’ knowledge or beliefs. Systems like [**EFP**](https://github.com/epistemic-planning/efp) (Epistemic Forward Planner) or [**MAFS**](https://scholar.google.com/scholar?q=MAFS+multi-agent+forward+search) (Multi-Agent Forward Search) treat DEL-style event models as action descriptions within a planning domain. Planners search for action sequences that achieve goals such as “agent A eventually knows that agent B knows p.”

A high-level sketch of how such planning might proceed is:

```
function EpistemicPlan(M_initial, Goal):
    frontier := {M_initial}
    visited  := ∅

    while frontier not empty:
        M := pop(frontier)
        if Satisfies(M, Goal):
            return ExtractPlan(M)

        for each event E in AvailableEvents:
            M' := ApplyEventModel(M, E)
            if M' not in visited:
                frontier.add(M')
                visited.add(M')
    return failure
```
These planners treat DEL updates much like classical STRIPS operators but with epistemic structure embedded inside them.

### AI-Oriented Epistemic Reasoning Systems

As artificial intelligence increasingly adopts multi-agent or social reasoning tasks, new tools integrate epistemic logic with learning-based systems. Some frameworks generate DEL scenarios to evaluate large language models’ Theory-of-Mind abilities. Others embed knowledge updates inside reinforcement-learning pipelines or agent-based simulators.

Although still experimental, these systems often pair a learned component for prediction or hypothesis generation with a symbolic epistemic module for consistency checking. A simplified architecture looks like:

```
loop:
    observation := Agent.observe()
    guess       := LLM.generate_hypothesis(observation)
    knowledge   := ApplyEventModel(knowledge, guess_as_event)
    action      := KnowledgeGuidedPolicy(knowledge)
    Agent.execute(action)
```

This neurosymbolic pattern—guess with a generative model, verify with symbolic epistemic logic—is increasingly influential.

### How SMCDEL Fits

SMCDEL occupies a distinct niche within this ecosystem. Unlike explicit-state tools, it is fully symbolic, representing worlds, relations, and updates as BDDs. Unlike theorem provers, it performs automated model checking without requiring manual proof steps. Unlike planners, it does not search action sequences but instead analyzes specific epistemic transitions. By combining the expressive machinery of DEL with the computational efficiency of BDDs, SMCDEL permits interactive experimentation with models that would be impractical for explicit tools.

## Using SMCDEL

SMCDEL (Symbolic Model Checker for Dynamic Epistemic Logic) is a tool that:

- lets you define agents, worlds, valuations, relations
- lets you define **event models** (for announcements, private messages, etc.)
- applies them with `update`
- and then lets you `check` whether a certain epistemic formula holds

You can use the **web version**, which all the code present in this chapter is based around:

- https://w4eg.de/malvin/illc/smcdelweb

or install it locally. 

**WARNING: IF ANY CODE FROM THIS DOCUMENT IS USED WHEN RUNNING LOCALLY, IT MAY NOT WORK AS THERE IS DIFFERENCES BETWEEN THE ONLINE VERSION AND THE LOCALLY RUN VERSION'S SYNTAX**

### Installation 

```bash
# Using Haskell Stack
stack install smcdel
```

After installation, you can run:
```bash
smcdel my_model.smcdel
```
where `my_model.smcdel` is a text file describing your epistemic model and the formulas you want to check.

### Model Example (use in online tool)
Goal: two agents, `a` and `b`, two worlds, `1` and `2`, and both agents are uncertain.

```
VARS 1, 2

LAW  Top

OBS  a: 1
     b: 1

WHERE? 1

WHERE? a knows whether 1

WHERE? a knows whether 2

WHERE? b knows whether 1

WHERE? b knows whether 2
```

What this does:

- The model contains two propositional variables (1, 2) and two agents (a, b), with all valuations allowed (LAW Top).

- Both agents observe only the value of variable 1, so they can always distinguish worlds by 1 but never by 2.

- As a result:

   - 1 is true exactly in the worlds where it appears in the valuation.

  - Agents always know whether 1 (they directly observe it).

  - Agents never know whether 2 (worlds indistinguishable to them disagree on 2).

Intuition: both answers should be false because each agent still considers the world where p is false possible.

### Adding a Public Announcement
Now we show how a Public Announcement can impact an epistemic model.

We start from the previous model and then "**add an event**" where we publicly announce 1.

```
VARS 1, 2

LAW  Top

OBS 
  a: 1
  b: 1

-- Before any announcement
WHERE? a knows whether 1
WHERE? b knows whether 1

WHERE? a knows whether 2
WHERE? b knows whether 2

-- After a public announcement that 2 is true
WHERE? [ ! 2 ] a knows whether 1
WHERE? [ ! 2 ] b knows whether 1

WHERE? [ ! 2 ] a knows whether 2
WHERE? [ ! 2 ] b knows whether 2

```

What happens:
- since we publicly announced `2`, all worlds where `2` was false are dropped
- in a model with a single world, `1` is trivially known by everyone
- so both `Ka 2` and `Kb 2` should now be `true`

This is the dynamic piece: **before** the update, they did not know; **after** the update, they do.

(muddy-children)=
## Muddy Children

The muddy children puzzle is sometimes considered the hello world of dyanmic epistemic logic. Fortunately, we can start exploring this interactively with [SMCDEL](https://w4eg.de/malvin/illc/smcdelweb/index.html). In fact, I recommend to start to work through the example pen-and-paper and interactively with SMCDEL at the same time.

For more background, I am referring to 

- Reasoning about knowledge. R Fagin, JY Halpern, Y Moses, M Vardi - 2004 [[pdf]](http://www.cse.buffalo.edu/~rapaport/676/F01/fagin.pdf)

Our starting point is the following quote from that book:

<!-- ![image](https://hackmd.io/_uploads/rJrvlGXTge.png)

![](images/2026-01-13-15-42-48.png) -->

![](images/2026-01-13-15-35-59.png)

---

Summary for 4 children 3 of whom are muddy:

- $4$ children
- $3$ children are muddy
- "At least one of you is muddy"
- "Do you know whether you are muddy?"
- All children say "No"
- "Do you know whether you are muddy?"
- All children say "No"
- "Do you know whether you are muddy?""
- All muddy children say "Yes"

How can we understand what is happening?

- Why should the announcement "At least one of you is muddy" have any effect? (All children already know that this is true.)
- Can announcing a true fact change the knowledge of the agents?
- Why should the questions "Do you know whether you are muddy?" have any effect? (This question does not seem to carry any information.)
- Why should repeating the question "Do you know whether you are muddy?" have accumulative effect? 

**Exercise/Activity**: Build a Kripke structure that models the situation before the first announcement. It will have 8 world and relations $R_1,R_2,R_3$ and atomic propositions $p_1,p_2,p_3$. Each world specifies a valuation of the variables $p_i$ such that $p_i=0$ if child $i$ is muddy in that world. Relation $R_i$ relates two worlds if child $i$ cannot distinguish them. Assume that in this example child 1 is not muddy and that children 2 and 3 are muddy. 
- Draw a picture of the Kripke model.
- What do the children know about the actual world before the game starts?
- Which world gets removed after the first announcement ("At least one of you is muddy")?
- Which worlds get removed after all children answer "No" following the first question ()"Do you know whether you are muddy")?
- Explain how the game proceeds using the dynamic updates of the model.


## Algorithms

Understanding the algorithms that drive SMCDEL reveals both the power and the limits of symbolic model checking for epistemic logic. At its core, the tool must determine which worlds satisfy a formula, and how those sets of worlds evolve when epistemic events occur. To do this efficiently, SMCDEL relies on *symbolic* representations rather than explicit enumeration.

The foundation of SMCDEL’s symbolic approach is the **Binary Decision Diagram (BDD)**. Instead of storing worlds, accessibility relations, valuations, and event preconditions as large explicit sets, SMCDEL encodes them as Boolean decision structures. These BDDs compress the underlying state space—often exponentially—by exploiting repeated logical substructure, in much the same way as symbolic hardware model checkers.

Formally, we can think of each formula, relation, or set of worlds as being represented by a BDD that encodes a Boolean characteristic function. For example, the set of worlds where a formula `φ` holds is represented by a BDD `B_φ`, which returns true exactly on those assignments corresponding to worlds satisfying `φ`.

### Model Evaluation for Knowledge

Using BDDs, SMCDEL evaluates epistemic formulas through operations on these symbolic sets. For a knowledge formula `K_a φ`, the semantics say that `K_a φ` holds at a world `w` if, in all worlds `w′` accessible from `w` via `R_a`, the formula `φ` is true. Algorithmically, this becomes a universal relational image computation.

At a high level, we can describe the evaluation process symbolically as:

```text
function ComputeKnowledgeBDD(agent a, B_phi, R_a, B_Worlds):
    # B_phi: BDD for the set of worlds where φ holds
    # R_a:   BDD encoding the accessibility relation for agent a
    # B_Worlds: BDD for all reachable worlds

    # Step 1: encode the complement of φ
    B_not_phi := NOT(B_phi)

    # Step 2: find (w, w') such that w R_a w' and w' violates φ
    #         i.e., bad successors with respect to φ
    B_bad_pairs := R_a AND LiftToPairs(B_not_phi)

    # Step 3: project away w' to obtain worlds w that have some bad successor
    B_bad_sources := Exists_wprime(B_bad_pairs)

    # Step 4: K_a φ holds exactly at worlds with no bad successors
    B_Ka_phi := B_Worlds AND NOT(B_bad_sources)

    return B_Ka_phi
```
Here, LiftToPairs conceptually aligns the BDD for ¬φ with the second component of the pair (w, w′), and Exists_wprime performs existential quantification over the successor world variables. The result B_Ka_phi is the BDD representing all worlds where K_a φ holds. In practice, SMCDEL caches such intermediate results and uses optimized BDD libraries to implement the Boolean and quantification operations efficiently.

### Dynamic Updates via Event Models

Dynamic Epistemic Logic introduces a second layer of computation: model updates. When a public announcement or private event occurs, SMCDEL constructs a new epistemic model that reflects the changed information state. Formally, this is described as the product of the current model M and an event model E, written M ⊗ E.

On the symbolic side, we work with BDDs representing:

- the current set of worlds,
- the current accessibility relations,
- the events and their preconditions,
- and the event indistinguishability relations for each agent.

The DEL product can be sketched as follows:
```
function ApplyEventModel(M, E):
    # M: current model with
    #    - B_Worlds: BDD for worlds
    #    - R_a: BDDs for each agent a's accessibility
    # E: event model with
    #    - B_Events: BDD for events
    #    - Pre: BDD for preconditions (over worlds × events)
    #    - R_a_evt: BDDs for event indistinguishability

    # Step 1: build candidate world–event pairs
    B_world_event_pairs := B_Worlds × B_Events

    # Step 2: enforce event preconditions (filter out impossible pairs)
    B_valid_pairs := B_world_event_pairs AND Pre

    # Step 3: project to obtain the new "worlds" of the product model
    B_new_worlds := Exists_events(B_valid_pairs)

    # Step 4: construct new accessibility relations for each agent
    for each agent a:
        # (w, e) is related to (w', e') if:
        #   - w R_a w'   in the old model
        #   - e R_a_evt e' in the event model
        B_Ra_worlds := LiftWorldRelation(R_a[a])
        B_Ra_events := LiftEventRelation(R_a_evt[a])
        B_Ra_product := (B_Ra_worlds AND B_Ra_events) AND
                        PairRestrictionTo(B_valid_pairs)

        # Optionally project to appropriate variable sets
        R_a_new[a] := B_Ra_product

    return NewModel(B_new_worlds, R_a_new)
```
Intuitively, this procedure constructs the Cartesian product of worlds and events, filters out combinations that do not satisfy the event’s precondition, and then recomputes each agent’s accessibility relation based on both the old world relation and the event indistinguishability relation. The result is a new symbolic model representing the updated epistemic state after the event.

In the special case of a public announcement of a formula φ, the event model has a single event whose precondition is φ, and all agents consider this event indistinguishable from itself. Symbolically, this collapses to simply eliminating worlds that do not satisfy φ, which can be expressed very compactly in BDD form.

### Complexity and Practical Performance

From the standpoint of computational complexity, DEL model checking is demanding. The general problem is PSPACE-complete, and systems involving deeply nested updates or many agents can reach EXPTIME complexity. In principle, this would make large-scale reasoning infeasible. In practice, however, symbolic methods allow SMCDEL to operate effectively on models containing thousands or even millions of worlds.

The key is that BDDs frequently represent huge sets very compactly, and the core algorithms—Boolean operations, relational products, quantification—operate on these compressed structures, often without ever “seeing” individual worlds. This is the same phenomenon that enabled symbolic hardware model checking to scale to industrial-sized designs.

### Optimizations in SMCDEL

To further improve performance, SMCDEL employs several implementation-level optimizations. Unreachable worlds are pruned early and often, reducing the size of the state space that subsequent operations must handle. The underlying BDD library performs dynamic variable reordering to keep the diagrams compact, which has a significant impact on memory and runtime. Intermediate results, such as BDDs for subformulas or partial relational images, are stored in caches and reused whenever the same structure appears again.

Additionally, event models are simplified before being applied: logically equivalent or redundant conditions are merged, and unnecessary structure is removed. Updates are often evaluated incrementally, building on existing symbolic objects instead of recomputing from scratch. A high-level sketch of this optimization pattern looks like this:
```
function CachedModelCheck(formula φ, model M, cache):
    if (M, φ) in cache:
        return cache[(M, φ)]

    if φ is atomic:
        result := EvaluateAtomic(φ, M)
    else if φ is K_a ψ:
        B_psi := CachedModelCheck(ψ, M, cache)
        result := ComputeKnowledgeBDD(a, B_psi, M.R_a, M.B_Worlds)
    else if φ is [E] ψ (a DEL update modality):
        M_updated := ApplyEventModel(M, EventModelOf(E))
        result := CachedModelCheck(ψ, M_updated, cache)
    else:
        result := CombineSubresults(φ, M, cache)

    cache[(M, φ)] := result
    return result
```

By combining symbolic representation, carefully designed relational operations, and aggressive caching, SMCDEL makes it possible to interactively explore complex multi-agent epistemic scenarios—often directly from the web interface—despite the underlying worst-case complexity of DEL model checking.

## Social Networks and DEL

We can think of a social network as:
- a set of agents (users, accounts, processes),
- a set of connections (who can hear whom, who follows whom, who is in the same group chat),
- a sequence of information events (DMs, posts, story updates, announcements).

From an epistemic perspective, such networks determine **who can receive information, who can distinguish which situations, and how knowledge propagates through communication** ([Ruan & Thielscher, 2011](https://scholar.google.com/scholar?q=A+Logic+for+Knowledge+Flow+in+Social+Networks); [Seligman, Liu, & Girard, 2013](https://scholar.google.com/scholar?q=Facebook+and+the+Epistemic+Logic+of+Friendship)).

Epistemic logic lets us ask:
- after this sequence of events, who knows the information?
- who only believes it?
- who knows that others know it?
- is it common knowledge to the group?

Dynamic Epistemic Logic (DEL) is particularly well-suited for this setting because it treats communication acts—such as public broadcasts and private messages—as model-transforming events, allowing precise reasoning about how information flow reshapes agents’ knowledge states (Baltag, Moss, & Solecki, 1998; [Renne, 2008](https://scholar.google.com/scholar?q=Public+and+Private+Communication+Are+Different+Renne)).

### Conceptual Mapping

| Social concept                                | Epistemic logic counterpart                                  |
|----------------------------------------------|---------------------------------------------------------------|
| user / account                               | agent (e.g. `A`, `B`, `C`)                                    |
| follow / friend                              | accessibility / visibility / communication link              |
| public post                                  | public announcement                                           |
| private message                              | private event (visible to a subset of agents)                 |
| rumor                                        | sequence of (possibly private) announcements                  |
| "everyone knows"                             | group knowledge (`E_G φ`)                                     |
| "everyone knows that everyone knows"         | common knowledge (`C_G φ`)                                    |

Treating **rumors or gossip as sequences of epistemic updates** has been studied explicitly in the DEL literature, where repeated private and public communications are shown to generate complex higher-order knowledge effects ([van Ditmarsch et al., 2017](https://scholar.google.com/scholar?q=Epistemic+Protocols+for+Dynamic+Gossip)).

So: **social-network reasoning is a natural application of dynamic epistemic logic**, especially when the structure of communication channels determines what agents can or cannot infer ([Baltag et al., 1998](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logics+of+Diffusion+and+Prediction)).

### Example: Rumor Spread in a Small Network

**Agents:** `A`, `B`, `C`.

- only `A` initially knows proposition `1`,
- `A` privately tells `1` to `B`,
- then `B` publicly says “I learned `1`”,
- we want to see what `C` can now conclude.

This scenario illustrates a key distinction in epistemic modeling: **private communication updates only the knowledge of involved agents, while public announcements can generate higher-order and even common knowledge**, depending on the assumed communication channel ([Renne, 2008](https://scholar.google.com/scholar?q=Public+and+Private+Communication+Are+Different+Renne)).

### Private vs. Public (Why It Matters)

- A public announcement reduces uncertainty for every agent.
- A private event reduces uncertainty only for the involved agents.
- Achieving common knowledge typically requires some form of public or mutually observable communication.

These distinctions are fundamental in DEL and underpin many formal results about secrecy, information leakage, and coordination in multi-agent systems ([Baltag et al., 1998](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logics+of+Diffusion+and+Prediction); Renne, 2008).

### Toward Common Knowledge

In a group chat with agents `A`, `B`, `C`, we might model:
- a message is posted publicly: `p`,
- everyone sees it,
- everyone knows that everyone sees it.

In epistemic logic we define:
- `E_G(φ)` = everyone in group `G` knows `φ`,
- `C_G(φ)` = `φ` is common knowledge in `G`.

Public announcements are a canonical mechanism for generating common knowledge, and their role in social and informational networks has been extensively studied in DEL ([Baltag et al., 1998](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logics+of+Diffusion+and+Prediction)).

More recent work extends this perspective by allowing **the social network itself to change**, modeling how new links, groups, or communication structures emerge and affect knowledge dynamics (Smets & Velázquez-Quesada, [2017](https://scholar.google.com/scholar?q=How+to+Make+Friends+Smets+Velazquez-Quesada), [2018](https://scholar.google.com/scholar?q=The+Creation+and+Change+of+Social+Networks+Smets)). These ideas have also been applied to **diffusion and prediction phenomena in social networks**, where epistemic states evolve alongside social influence ([Baltag, Christoff, Rendsvig, & Smets, 2019](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logics+of+Diffusion+and+Prediction)).

## Applications in Industry

Although epistemic logic began as a theoretical exploration of knowledge, it has quietly become a practical tool in some of the most demanding sectors of modern technology. Industry has discovered that many real systems—distributed networks, security protocols, autonomous robots, and even financial infrastructures—are governed as much by what agents *know* as by what they *do*. As a result, epistemic reasoning has found its way into the engineering pipelines of organizations that require absolute clarity about information flow, decision foundations, and the consequences of communication.

### [Cybersecurity and Information Flow](https://eprints.illc.uva.nl/id/eprint/1802/1/MoL-2021-12.text.pdf) 

One of the earliest industrial applications emerged in cybersecurity. Here, the central question is deceptively simple: *What can an attacker learn from the behavior of a system?* Epistemic logic provides language to express this precisely. Whether a program leaks information through its outputs, or a cryptographic protocol reveals more than intended, can be formulated in terms of what an adversary knows before and after observing the system.

Security analysts now routinely use epistemic-temporal logics to understand information release policies, derive conditions for noninterference, and evaluate side-channel vulnerabilities. In such contexts, DEL offers a way to model how knowledge accumulates over time—an invaluable perspective for industries managing confidential or sensitive data. Instead of asking merely “is this system secure?”, engineers ask “who could know what, and when?”, which is often a far more revealing question.

### [Distributed Cloud and Database Systems](https://arxiv.org/abs/2308.00579)

As modern cloud infrastructures grow in scale, distributed systems increasingly rely on reasoning about uncertainty. Large databases often replicate data across many nodes, and correct operation depends on each node having *sufficient* information to take safe actions. Consensus protocols, commit protocols, and failure detectors are all underpinned by subtle knowledge conditions: a node must know that others know, or know that they do not know, before proceeding.

Many companies—ranging from cloud providers to financial exchanges—use epistemic arguments to verify the correctness of their distributed algorithms. Epistemic logic clarifies the exact information requirements a process must meet before sending a message, committing a transaction, or assuming that a quorum has been achieved. Engineers apply logical frameworks to reason not just about the behavior of code, but about the mental state of the system’s components, treating them as information-processing agents.

### [Robotics and Autonomous Systems](https://ceur-ws.org/Vol-3204/paper_4.pdf)

In robotics, epistemic logic plays a direct role in safety. Autonomous drones, vehicles, robots, and factory agents operate in complex environments where incorrect assumptions can cause severe failures. When multiple robots coordinate, they must act based on their own observations, their beliefs about the observations of others, and their knowledge about shared or missing information.

DEL is especially well-suited for modeling such interactions. Consider fleets of drones that must determine when an area is safe, or robot arms that must avoid collision based on inferred knowledge of each other’s actions. Engineers use epistemic models to verify that these systems will take action *only when they know enough to do so*. The logic does not merely confirm that a protocol makes sense—it exposes the precise boundary between safe and unsafe knowledge states.

### [Generative AI and Cognitive Modeling](https://link.springer.com/article/10.1007/s43154-022-00090-9)

Perhaps the most recent and exciting application occurs in artificial intelligence, particularly with the rise of large language models and multi-agent AI systems. When generative models interact with humans or with each other, reasoning about beliefs, expectations, misunderstandings, and informational changes becomes central to their behavior.

Dynamic epistemic logic has become a testbed for evaluating an AI system’s ability to perform social reasoning. DEL-based scenarios are now used to challenge LLMs with Theory-of-Mind tasks: who knows what, when do they learn it, and how do announcements reshape their beliefs? Even more compelling is the emergence of **neurosymbolic architectures**, where generative models propose actions or hypotheses and epistemic modules verify whether these proposals are consistent with the knowledge state of an agent.

Much like robotics, AI systems benefit from epistemic guarantees. If an AI assistant must make recommendations based on partial user information, or if an autonomous negotiation system must infer the intentions of another agent, epistemic logic provides a disciplined way to model the process.

### Finance, Compliance, and Organizational Behavior

In industries defined by strict information regulations—such as finance, auditing, and legal compliance—epistemic logic solves a subtle but critical problem: tracing who knows what, when they knew it, and what they are allowed to infer. Concepts such as insider trading hinge on distinctions in knowledge states. Corporate governance involves modeling chains of disclosure, ensuring that required parties are informed while preventing leaks to unauthorized ones.

Increasingly, organizations model information flow using epistemic constraints. For example, a trading algorithm may be verified to operate legally only if certain knowledge conditions remain impossible. Boards may analyze decision timelines by reconstructing knowledge propagation during key events. In these settings, epistemic logic becomes not merely a tool for technical verification but also a framework for explaining events in terms that regulators and analysts can understand.

### [“Epistemic Logics for Cryptographic Protocols and Zero‐Knowledge Proofs”](https://eprints.illc.uva.nl/id/eprint/1802/1/MoL-2021-12.text.pdf) (Jaramillo, 2021) 

The author uses epistemic logic to model multi-agent interactions in cryptographic settings — specifically for modelling zero-knowledge proofs (where a verifier is convinced of a fact but learns nothing more).

### [*A process algebraic framework for multi-agent dynamic epistemic systems*](https://arxiv.org/abs/2407.17537) (2024) — system-level DEL with agents and transitions.


### Van Benthem, van Eijck, Gattinger, Su, [*Symbolic Model Checking for Dynamic Epistemic Logic*](https://staff.fnwi.uva.nl/d.j.n.vaneijck2/papers/16/pdfs/2016-05-23-del-bdd-lori-journal.pdf)

The classic symbolic SMCDEL reference.

### Why Industry Needs Epistemic Logic

Across these sectors, a common pattern emerges: modern systems do not operate solely on physical states or raw data. They operate on *information* and on the *beliefs derived from it*. Whether a system secures user data, coordinates autonomous robots, manages distributed transactions, or interacts with human beings, the essential question becomes:

**What does each component know, what can it infer, and how does new information change its behavior?**

Epistemic logic provides the machinery to answer these questions rigorously. DEL extends that machinery to the realm of change, modeling communication and observation as first-class citizens in the logic. Tools like SMCDEL make these insights computationally accessible, enabling engineers to test, verify, and explore the dynamics of knowledge in real systems.

The result is a growing recognition that epistemic logic is not merely an abstract curiosity but a practical necessity—one that helps bridge the gap between theoretical reasoning and industrial-grade system design.

## Typical Use Cases

While applications in industry highlight *where* epistemic logic matters, typical use cases focus on *what people actually do* with tools like SMCDEL in practice. In research labs, classrooms, and early-stage design work, SMCDEL serves less as a heavy-duty industrial verifier and more as a conceptual microscope: it lets us build small, precise models of information flow and then experiment with them until the underlying patterns become clear.

One of the most common use cases is **exploratory modeling of small communication scenarios**. A student or researcher starts with an informal story—perhaps a protocol sketch, a rumor in a social network, or a toy cryptographic exchange—and turns it into a DEL model. By encoding the agents, worlds, and events, they can ask questions such as “after this announcement, who knows what?” or “is there any agent who mistakenly believes `p`?”. SMCDEL becomes a sandbox in which to test intuitions: you propose a scenario, run an update, and let the model either confirm or refute your expectations about knowledge and belief ([Plaza (1989)](https://scholar.google.com/scholar?q=Plaza+Public+Announcement+Logic+1989), [Baltag, Moss, & Solecki (1998/2004)](https://scholar.google.com/scholar?q=Baltag+Moss+Solecki+Dynamic+Epistemic+Logic), [van Ditmarsch, van der Hoek, & Kooi (2007)](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logic+Ditmarsch+Hoek+Kooi)).


A closely related pattern is **debugging epistemic behavior in protocols and algorithms**. When designing a multi-agent protocol, it is easy to assume that some piece of information “obviously” becomes known after a certain step. SMCDEL provides a way to challenge those assumptions. By encoding the protocol as a sequence of events, one can check whether key epistemic conditions actually hold: does the coordinator ever know that all participants received the message? Does an agent know that its secret has not leaked? When the model shows that a desired knowledge property fails, it often reveals exactly which step in the protocol is epistemically inadequate ([Halpern & Moses (1990)](https://scholar.google.com/scholar?q=Halpern+Moses+1990+Knowledge+Common+Knowledge), [MCK](https://www.csse.canterbury.ac.nz/mck/), [Balliu et al. (2012)](https://arxiv.org/abs/1208.6106)).

In teaching and learning, SMCDEL is often used for **visualizing classic epistemic puzzles**. Problems such as muddy children, Russian cards, or coordinated attack become much more transparent when they are not only described but also executed. Students can watch how successive announcements or observations prune the space of possible worlds and turn ignorance into knowledge. The tool allows them to experiment: change an assumption, add an event, remove a piece of information, and see immediately how the structure of knowledge shifts ([DEMO](http://people.uleth.ca/~kooi/del/),[SMCDEL](https://scholar.google.com/scholar?q=Symbolic+Model+Checking+Dynamic+Epistemic+Logic), [van Ditmarsch (2000)](https://scholar.google.com/scholar?q=Ditmarsch+muddy+children+1990+modal+logic)).

Another frequent use case is **rapid prototyping of “what-if” scenarios** for more complex systems. Before investing in a full-fledged verification effort or a detailed simulator, a designer can build a small epistemic model that captures the essence of a situation: a few agents, a handful of propositions, and a simplified sequence of communication events. Questions like “could an observer ever deduce this secret?” or “can these agents ever achieve common knowledge of success?” can often be answered at this coarse level. If the toy model already exhibits a problematic epistemic pattern—say, an unavoidable leak or a failure of agreement—that insight can guide subsequent design choices ([Baltag, Moss, & Solecki (1998/2004)](https://scholar.google.com/scholar?q=Baltag+Moss+Solecki+Dynamic+Epistemic+Logic), [van Ditmarsch, van der Hoek, & Kooi (2007)](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logic+Ditmarsch+Hoek+Kooi), [Muise et al., Epistemic Planning](https://scholar.google.com/scholar?q=epistemic+planning+Muise)
).

Finally, with the emergence of epistemic evaluations for AI systems, SMCDEL is increasingly used as a **test harness for reasoning tasks**. Researchers designing Theory-of-Mind benchmarks can specify DEL models that encode nested beliefs and staged updates, and then translate those into textual scenarios for large language models or other agents. The “ground truth” about who knows what, and when, is computed by SMCDEL; model outputs can then be compared against this logical baseline. In this role, SMCDEL is less about verifying a deployed system and more about generating and validating sophisticated epistemic test cases ([Sileo et al. (2023)](https://scholar.google.com/scholar?q=Sileo+Dynamic+Epistemic+Logic+Theory+of+Mind), [Wu et al. (2025)](https://scholar.google.com/scholar?q=Wu+Inference+Time+Scaling+Theory+of+Mind+2025), [Fierro et al. (2024)](https://scholar.google.com/scholar?q=Fierro+Bridging+Epistemology+Large+Language+Models)
).

In all of these typical use cases, the models are intentionally small and stylized. The goal is not to mirror the full complexity of a real system, but to isolate the epistemic core of a phenomenon—communication, secrecy, agreement, misinformation—and to understand it well enough that larger-scale designs and analyses can be built on solid conceptual ground.


## Epistemic Logic and AI

### Targeting Theory of Mind in Large Language Models with Dynamic Epistemic Logic – [Sileo et al. (2023)](https://scholar.google.com/scholar?q=Sileo+Dynamic+Epistemic+Logic+Theory+of+Mind)
  
Uses dynamic epistemic logic (DEL) to generate controlled Theory-of-Mind tasks and test whether LLMs can reason about who knows what, when, and under which information updates. They explicitly use DEL models to construct scenarios where knowledge and belief are manipulated stepwise, then probe LLM behavior against these formal structures.

### Inference-Time Scaling for Theory-of-Mind Tasks – [Wu et al. (2025)](https://scholar.google.com/scholar?q=Wu+Inference+Time+Scaling+Theory+of+Mind+2025)

Builds on the same idea: ToM is framed in explicitly epistemic-logical terms, and dynamic epistemic logic is used to structure multi-agent belief/knowledge states. LLMs are then evaluated (and improved) on these tasks, showing that epistemic logic can act as a test harness for higher-order social reasoning in generative models.

### Bridging Epistemology and Large Language Models – [Fierro et al. (2024)](https://scholar.google.com/scholar?q=Fierro+Bridging+Epistemology+Large+Language+Models)

Analyzes different philosophical definitions of knowledge and connects them to large language models, giving semi-formal epistemic-logic style axioms (e.g., S4/T-like systems) in an appendix. They explicitly discuss how modal operators (like those in epistemic logic) can formalize competing notions of “the model knows that p.”

### An AI Safety Problem – Klassen & al., AAMAS 2023
Analyzes safety failures in multi-agent AI systems as arising from misaligned epistemic states rather than faulty policies, showing how agents can act rationally yet unsafely due to incorrect or incomplete knowledge about the world or other agents. The paper argues that explicit epistemic reasoning is necessary for AI safety, framing knowledge alignment as a core design requirement for multi-agent systems.

## Case Study: The “Rescue Drone Coordination” Problem

### Scenario Overview
Imagine a fleet of **autonomous rescue drones** responding to a natural disaster.  
Each drone (`A`, `B`, `C`) monitors a separate zone but must coordinate to deliver medical supplies safely.  
However, communication links are intermittent and not every message is received by every drone.

Key proposition:  
- `p` = “Zone X has been cleared of hazards.”

Initially, only `A` detects that `p` is true.  
Drone `A` sends a **private message** to `B`, but the network drops `A`’s broadcast to `C`.  
Then `B` issues a **public announcement** (“Zone X is safe!”) on the shared channel.

### Modeling in SMCDEL
We can represent:
```text
-- Rescue Drone Coordination (approximate private-then-public) in SMCDEL

VARS 1,2,3

LAW  Top

-- a = detected safety
-- b = was privately informed (also sees 1)
-- c = cannot see 1 initially so its base is 2
OBS  a: 1
     b: 1,3
     c: 2

TRUE?
  {1,3}
  a knows that 1
  & b knows that 1
  & ~ (c knows that 1)

WHERE?
  < ! (1) >
  (a knows that 1)
  & (b knows that 1)
  & (c knows that 1)

VALID?
  [ ! (1) ]
  (a knows that 1 & b knows that 1 & c knows that 1)

```

This case study tests knowledge propagation in a safety-critical network.
You can expand upon this experiment by adding false public announcements (miscommunication), modeling message delays or dropped links, or by checking whether “everyone knows that everyone knows p” (common knowledge) ever arises.

### Why It Matters

Such models help engineers verify communication protocols in distributed robotics or IoT systems:
- Ensuring drones act only when they know an area is safe.
- Preventing actions based on mistaken or outdated beliefs.
- Analyzing how local updates become global knowledge—vital in swarm coordination.

## References
- Hintikka (1962). [Knowledge and Belief](https://scholar.google.com/scholar?q=Hintikka+Knowledge+and+Belief), Cornell University Press

- Kripke (1963). [Semantical Considerations on Modal Logic](https://scholar.google.com/scholar?q=Kripke+Semantical+Considerations+on+Modal+Logic+1963), Acta Philosophica Fennica

- Halpern and Moses (1990). [Knowledge and Common Knowledge in a Distributed Environment](https://scholar.google.com/scholar?q=Knowledge+and+Common+Knowledge+in+a+Distributed+Environment), Journal of the ACM

- Plaza (1989). [Logic of Public Announcements](https://scholar.google.com/scholar?q=Plaza+Logic+of+Public+Announcements), Proceedings of TARK

- Baltag, Moss, and Solecki (1998). [The Logic of Public Announcements, Common Knowledge, and Private Suspicions](https://scholar.google.com/scholar?q=The+Logic+of+Public+Announcements+Common+Knowledge+and+Private+Suspicions), Proceedings of TARK

- Baltag, Moss, and Solecki (2004). [The Logic of Epistemic Actions](https://scholar.google.com/scholar?q=The+Logic+of+Epistemic+Actions), Synthese

- van Ditmarsch, van der Hoek, and Kooi (2007). [Dynamic Epistemic Logic](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logic+van+Ditmarsch+van+der+Hoek+Kooi), Springer

- van Benthem, van Eijck, Gattinger, and Su (2016). [Symbolic Model Checking for Dynamic Epistemic Logic](https://scholar.google.com/scholar?q=Symbolic+Model+Checking+for+Dynamic+Epistemic+Logic), Journal of Logic, Language and Information

- Baldoni et al. (1998). [Model Checking Knowledge and Time](https://scholar.google.com/scholar?q=Model+Checking+Knowledge+and+Time), Proceedings of KR '98 (Knowledge Representation Conference)

- Balliu, Dam, and Le Guernic (2012). [Epistemic Temporal Logic for Information Flow Security](https://scholar.google.com/scholar?q=Epistemic+Temporal+Logic+for+Information+Flow+Security), Proceedings of CSF (IEEE Computer Security Foundations Symposium)

- Jaramillo (2021). [Epistemic Logics for Cryptographic Protocols and Zero-Knowledge Proofs](https://scholar.google.com/scholar?q=Epistemic+Logics+for+Cryptographic+Protocols+and+Zero-Knowledge+Proofs), Master's Thesis, University of Amsterdam

- Soldà et al. (2022). [e-PICO: An Epistemic Reasoner for Collaborative Robots](https://scholar.google.com/scholar?q=e-PICO+epistemic+reasoner+collaborative+robots), Proceedings of KR (Principles of Knowledge Representation and Reasoning)

- Bramblett et al. (2023). [Epistemic Planning for Heterogeneous Robotic Systems](https://scholar.google.com/scholar?q=Epistemic+Planning+for+Heterogeneous+Robotic+Systems), arXiv

- Gielis et al. (2022). [A Critical Review of Communications in Multi-Robot Systems](https://scholar.google.com/scholar?q=Critical+Review+of+Communications+in+Multi-Robot+Systems), Autonomous Intelligent Systems

- Sileo et al. (2023). [Targeting Theory of Mind in Language Models with Dynamic Epistemic Logic](https://scholar.google.com/scholar?q=Targeting+Theory+of+Mind+Dynamic+Epistemic+Logic), arXiv

- Fierro et al. (2024). [Bridging Epistemology and Large Language Models](https://scholar.google.com/scholar?q=Bridging+Epistemology+and+Large+Language+Models), Proceedings of EMNLP 2024

- Wu et al. (2025). [Inference-Time Scaling for Theory of Mind Tasks](https://scholar.google.com/scholar?q=Inference-Time+Scaling+for+Theory+of+Mind+LLM), arXiv

- Klassen et al. (2023). [An AI Safety Problem: Misaligned Epistemic States in Multi-Agent Systems](https://scholar.google.com/scholar?q=Misaligned+Epistemic+States+Multi-Agent+Systems), Proceedings of AAMAS

- Ruan and Thielscher (2011). [A Logic for Knowledge Flow in Social Networks](https://scholar.google.com/scholar?q=A+Logic+for+Knowledge+Flow+in+Social+Networks), Proceedings of the Twenty-Second International Joint Conference on Artificial Intelligence (IJCAI)

- Seligman, Liu, and Girard (2013). [Facebook and the Epistemic Logic of Friendship](https://scholar.google.com/scholar?q=Facebook+and+the+Epistemic+Logic+of+Friendship), Proceedings of TARK

- Renne (2008). [Public and Private Communication Are Different](https://scholar.google.com/scholar?q=Public+and+Private+Communication+Are+Different+Renne), Synthese

- van Ditmarsch, van Eijck, Pardo, Ramezanian, and Schwarzentruber (2017). [Epistemic Protocols for Dynamic Gossip](https://scholar.google.com/scholar?q=Epistemic+Protocols+for+Dynamic+Gossip), Journal of Applied Logic

- Smets and Velázquez-Quesada (2017). [How to Make Friends: A Logical Approach to Social Group Creation](https://scholar.google.com/scholar?q=How+to+Make+Friends+Smets+Velazquez-Quesada), Logic, Rationality and Interaction (LORI 2017)

- Smets and Velázquez-Quesada (2018). [The Creation and Change of Social Networks: A Logical Study Based on Group Size](https://scholar.google.com/scholar?q=The+Creation+and+Change+of+Social+Networks+Smets), Dynamic Logic and Applications (DALI)

- Baltag, Christoff, Rendsvig, and Smets (2019). [Dynamic Epistemic Logics of Diffusion and Prediction in Social Networks](https://scholar.google.com/scholar?q=Dynamic+Epistemic+Logics+of+Diffusion+and+Prediction), Studia Logica
