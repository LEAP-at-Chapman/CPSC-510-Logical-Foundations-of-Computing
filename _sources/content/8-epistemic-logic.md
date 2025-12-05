# Epistemic Logic with SMCDEL

Author: *John Mulhern*


## Idea

Epistemic logic is the study of **knowledge** and **belief** using a formal logical language. Instead of only asking “is `p` true?”, we can ask:

- “does agent `a` know that `p` is true?” (`K_a p`)
- “does agent `a` believe that `p` is true?” (`B_a p`)
- “does agent `a` know that agent `b` knows that `p`?” (`K_a K_b p`)

This is useful in computer science because many systems are **multi-agent** or **distributed**. What an individual process, user, or node **knows** (or does **not** know) affects what it can safely and effectively do.

Epistemic logic is motivated by a simple but profound observation: in many systems, what matters is not merely what is true but what agents think is true. Whether we examine human communication, negotiation between strategic players, or computation in networked software agents, the ability to reason about an entity’s informational state becomes central. Questions such as “what does the system know about its environment?” or “what can a user infer from a public disclosure?” characterize modern cybersecurity, distributed systems, and artificial intelligence. Thus epistemic logic provides a formal language to articulate and analyze these questions rigorously, giving us a way to represent knowledge differences, detect misinformation, model secrecy, and reason about what becomes knowable as communication unfolds.

## In this chapter we will:

1. introduce the basics of (multi-agent) epistemic logic,
2. introduce *dynamic* epistemic logic (DEL) to handle information change,
3. show how to use **SMCDEL** (Symbolic Model Checker for Dynamic Epistemic Logic),
4. explain **social networks** through the lense of epistemic logic

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

Epistemic logic uses **possible worlds semantics** (Kripke semantics).

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

### Public Announcement (Informal)

Suppose we have a model `M` and we publicly announce `φ`.

- every agent hears the same announcement
- every agent trusts it (it becomes true, or was already true)
- so they **eliminate** all worlds in which `φ` was false
- result: a new epistemic model with fewer worlds

After this, many things that were **not** known become **known**, because there are fewer possibilities left.

This is exactly the kind of update SMCDEL is good at checking.

## Using SMCDEL

SMCDEL (Symbolic Model Checker for Dynamic Epistemic Logic) is a tool that:

- lets you define agents, worlds, valuations, relations
- lets you define **event models** (for announcements, private messages, etc.)
- applies them with `update`
- and then lets you `check` whether a certain epistemic formula holds

You can use the **web version**:

- https://w4eg.de/malvin/illc/smcdelweb

or install it locally.

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

### Model Example
Goal: two agents, `a` and `b`, one proposition `p`, two worlds, and both agents are uncertain.

**File:** `simple_model.smcdel`

```
# Agents and propositions
agents a b;
props p;

# Worlds
worlds w1 w2;

# Valuation: p is true in w1, false in w2
val p = {w1};

# Epistemic relations: both agents can't distinguish w1 and w2
rel a = {(w1,w1),(w1,w2),(w2,w1),(w2,w2)};
rel b = {(w1,w1),(w1,w2),(w2,w1),(w2,w2)};

# Check what they know in w1
check w1: Ka p;
check w1: Kb p;
```

What this does:

- declares agents, props, worlds
- says p is only true in w1
- says both agents see the two worlds as indistinguishable
- asks: “in world w1, does agent a know p?”, “does agent b know p?”

Intuition: both answers should be false because each agent still considers the world where p is false possible.

### Adding a Public Announcement
Now we show how a Public Announcement can impact an epistemic model.

We start from the previous model and then **add an event** where we publicly announce p.

**File:** `announcement.smcdel`
```
include "simple_model.smcdel";

# Define a public announcement event
event announce_p {
    pre  = p;    # only applicable in worlds where p is true
    post = {};   # no change to valuations
}

# Apply the event
update announce_p;

# Now check again
check w1: Ka p;
check w1: Kb p;
```

What happens:
- since we publicly announced `p`, all worlds where `p` was false are dropped
- only `w1` remains
- in a model with a single world, `p` is trivially known by everyone
- so both `Ka p` and `Kb p` should now be `true`

This is the dynamic piece: **before** the update, they did not know; **after** the update, they do.

## Social Networks and Epistemic Logic
We can think of a social network as:
- a set of agents (users, accounts, processes)
- a set of connections (who can hear whom, who follows whom, who is in the same group chat)
- a sequence of information events (DMs, posts, story updates, announcements)

Epistemic logic lets us ask:
- after this sequence of events, who knows the information?
- who only believes it?
- who knows that others know it?
- is it common knowledge to the group?

### Conceptual Mapping

| Social concept                              | Epistemic logic counterpart                                  |
|---------------------------------------------|---------------------------------------------------------------|
| user / account                              | agent (e.g. `A`, `B`, `C`)                                    |
| follow / friend                             | accessibility / visibility / communication link              |
| public post                                 | public announcement                                           |
| private message                             | private event (visible to a subset of agents)                 |
| rumor                                       | sequence of (possibly private) announcements                  |
| "everyone knows"                            | group knowledge (`E_G φ`)                                     |
| "everyone knows that everyone knows"        | common knowledge (`C_G φ`)                                    |

So: **social-network reasoning is a natural application of DEL.**

---

### Example: Rumor Spread in a Small Network

**Agents:** `A`, `B`, `C`.

- only `A` initially knows proposition `p`
- `A` privately tells `B`
- then `B` publicly says “I learned `p`”
- we want to see what `C` can now conclude

**File:** `social_network.smcdel`

```text
agents A B C;
props p;

# two worlds: p is true / p is false
worlds w1 w2;
val p = {w1};

# everyone initially uncertain
rel A = {(w1,w1),(w1,w2),(w2,w1),(w2,w2)};
rel B = {(w1,w1),(w1,w2),(w2,w1),(w2,w2)};
rel C = {(w1,w1),(w1,w2),(w2,w1),(w2,w2)};

# 1) A privately tells B
event A_to_B {
    pre = p;
    rel = {
        (A,A),
        (B,B),
        (C,C)
    };
}

# 2) B publicly announces "I learned p"
event B_public {
    pre = p;
    rel = {
        (A,A),
        (B,B),
        (C,C)
    };
}

# apply events in sequence
update A_to_B;
update B_public;

# now ask:
check w1: KA p;      # does A know p?
check w1: KB p;      # does B know p?
check w1: KC p;      # does C know p now?
check w1: KC KB p;   # does C know that B knows p?
check w1: KB KA p;   # does B know that A knows p?
```

What’s going on:
- After `A_to_B`, only `B` gains the info.
- After `B_public`, everyone sees that `p` must be true (since `B` said so publicly and the precondition was `p`).
- So now `C` learns `p`, and also learns that `B` knows `p`.

This shows that the second step (public announcement) is what makes the information spread to the whole network.

### Private vs. Public (Why it matters)
- A public announcement reduces uncertainty for every agent. It is “broadcast.”
- A private event reduces uncertainty only for the involved agents.
- If we want something to become common knowledge, it almost always needs to be public (or something equivalent to a public event — e.g. everyone hears it, and everyone hears that everyone heard it, etc.).

This distinction is exactly what we need to study:
- partial disclosure
- data leaks
- misinformation
- who can deduce what after an observable action

### Toward Common Knowledge

In a group chat with agents `A`, `B`, `C`, we might model:
- a message is posted publicly: `p`
- everyone sees it
- everyone knows that everyone sees it (because that’s how the channel works)

In epistemic logic we often define:
- `E_G(φ)` = everyone in group `G` knows `φ`
- `E_G^2(φ)` = everyone in `G` knows that everyone in `G` knows `φ`
- ...
- `C_G(φ)` = for all `n`, `E_G^n(φ)`

Public announcements are a classic way to get close to this kind of knowledge.

## Applications in Industry
### [“Epistemic Temporal Logic for Information Flow Security”](https://eprints.illc.uva.nl/id/eprint/1802/1/MoL-2021-12.text.pdf) 

Balliu et al. apply an epistemic-temporal logic to programs to reason about what an attacker knows or doesn’t know after observing program outputs — i.e., how knowledge evolves over time as information is released. This directly maps to the “who knows what” view of epistemic logic and is a strong CS/industrial-adjacent example (secure coding, confidentiality, release of secret data).

### [“Epistemic Logics for Cryptographic Protocols and Zero‐Knowledge Proofs”](https://eprints.illc.uva.nl/id/eprint/1802/1/MoL-2021-12.text.pdf) (Jaramillo, 2021) 

The author uses epistemic logic to model multi-agent interactions in cryptographic settings — specifically for modelling zero-knowledge proofs (where a verifier is convinced of a fact but learns nothing more).

### [*A process algebraic framework for multi-agent dynamic epistemic systems*](https://arxiv.org/abs/2407.17537) (2024) — system-level DEL with agents and transitions.


### Van Benthem, van Eijck, Gattinger, Su, [*Symbolic Model Checking for Dynamic Epistemic Logic*](https://staff.fnwi.uva.nl/d.j.n.vaneijck2/papers/16/pdfs/2016-05-23-del-bdd-lori-journal.pdf)

The classic symbolic SMCDEL reference.

## Epistemic Logic and Generative AI

### Targeting Theory of Mind in Large Language Models with Dynamic Epistemic Logic – Sileo et al., 2023
  
Uses dynamic epistemic logic (DEL) to generate controlled Theory-of-Mind tasks and test whether LLMs can reason about who knows what, when, and under which information updates. They explicitly use DEL models to construct scenarios where knowledge and belief are manipulated stepwise, then probe LLM behavior against these formal structures.

### Inference-Time Scaling for Theory-of-Mind Tasks – Wu et al., 2025

Builds on the same idea: ToM is framed in explicitly epistemic-logical terms, and dynamic epistemic logic is used to structure multi-agent belief/knowledge states. LLMs are then evaluated (and improved) on these tasks, showing that epistemic logic can act as a test harness for higher-order social reasoning in generative models.

### Bridging Epistemology and Large Language Models – Fierro et al., EMNLP 2024

Analyzes different philosophical definitions of knowledge and connects them to large language models, giving semi-formal epistemic-logic style axioms (e.g., S4/T-like systems) in an appendix. They explicitly discuss how modal operators (like those in epistemic logic) can formalize competing notions of “the model knows that p.”

### An AI Safety Problem – Klassen & al., AAMAS 2023

### Epistemic Artificial Intelligence is Essential for Machine Learning

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

## Referenes & Further Reading
- Jaakko Hintikka, Knowledge and Belief (1962)
- Hans van Ditmarsch, Wiebe van der Hoek, Barteld Kooi, Dynamic Epistemic Logic
- Y. Halpern and Y. Moses, “Knowledge and Common Knowledge in a Distributed Environment,” Journal of the ACM, 37(3), 1990
- SMCDEL web interface: https://w4eg.de/malvin/illc/smcdelweb