# Hoare Logic in Dafny

## Idea

Hoare Logic extends propositional logic (or first-order logic) by allowing programs to appear in the syntax of the logic. Specifically, an atomic proposition has the form

$$
\{P\} S \{Q\}
$$

where $S$ is a sequence of statements in some programming language, $P$ is the precondition one assumes to hold before executing $S$ and $Q$ is the postcondition that is guaranteed to hold whenever execution of $S$ terminates.

Observe how this picks up on ideas of modal, temporal and epistemic logic. In fact, in propositional dynamic logic, a logic closely related to Hoare logic, one writes instead

$$
P\to [S]Q
$$

where $[S]$ plays the role of a modal box operator, similarly to the public announcment operator in dynamic epistemic logic.

This allows programmers to specify and verify what their code does, catching bugs at compile-time rather than runtime. 

Dafny makes this practical by integrating specifications (pre and postconditions) directly in the programming language and using automated theorem proving (Z3) to check the Hoare triples.

## Basic Theory - The Rules of Hoare Logic

Hoare Logic is a logic for compositional reasoning about safety properties of programs. For each construct in the programming language there is a corresponding reasoning rule. For example, for a simple language with sequential composition, assignment, while loop, conditional, we may have:

**Sequential Composition**:

$$
\frac{\{P\}\ \mathtt S\ \{Q\} \quad\quad \{Q\}\ \mathtt T\ \{R\}}
{\{P\}\ \mathtt S ; \mathtt T\ \{R\}}
$$

**Assignment**:

$$ 
\{P [\mathtt{exp}\,/\,\mathtt x]  \}
\ \ \ \mathtt x:=\mathtt{exp} \ \ \ 
\{P \}
$$

**Iteration**:

$$\frac{\{I \wedge \mathtt B \}\ \mathtt S\ \{I\}}{\{I \}\ \mathtt{while}\ B\ \mathtt{do}\ S\ \mathtt{done} \{\neg B \wedge I\}}$$

**Conditional**:

$$
\frac{\{B \wedge P\}\ \mathtt S\ \{Q\} \quad\quad \{\neg B \wedge P \}\ \mathtt T\ \{Q\} }
{\{P\}\ \mathtt{if}\ B\ \mathtt{then}\ \mathtt S\ \mathtt{else}\ \mathtt T\ \mathtt{endif}\ \{Q\}
}$$

**Weakening**:

$${\frac{P'\Rightarrow P \quad\{P \}\ \mathtt S\ \{Q\} \quad Q\Rightarrow Q'}{\{P' \}\ \mathtt S \  \{Q'\}}}$$

**Remark:**
-  Weakening connects the proof system of logic (for proving propositions of the form $P\Rightarrow Q$) with the proof system for the constructs of the programming language. 
-  Assignment reasons from the postcondition towards the precondition. The rule computes the weakest precondition that guarantess the post-condition (assuming that the program S terminates). Reasoning forward on states and backwards on predicates is typical for [Stone duality](https://en.wikipedia.org/wiki/Stone_duality).
-  While is interesting because it formalizes reasoning with invariants.

## Tool (Installation, First Example, First Exercise)

Recall the Hoare triple
```
{P}
  S
{Q}
```
from the Idea section. For example, if `S` computes the absolute value we may have
```
{x == -5}
  if x < 0 {y := -x;} else {y := x;}
{y == 5}
```
We can turn this into Dafny ([try it online](https://tio.run/##VY5NDoIwFIT3PcWkK0ggYeMGrIkH8AZuMDxiE6zaHwMRzl5fhYXu5vtmFtO1vZlivJG/3jscLy4ba2jjc1jywRqHbFqFAKtn0JYcvA3ETMaFhBMOCtWfUAoj5nlN5Sje3Oqe3R4VEoCrOlUNwwIaHP36VYtFiO3aqdUmy7@TV2v5iguDT8v0udzlaf@wfBRyM1CQxTYsIM9GNmKJ8QM))
```dafny
method Abs(x: int) returns (y: int)
  requires true                 // precondition
  ensures y >= 0                // postcondition
  ensures y == x || y == -x     // postcondition
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}
```
Note that the two postconditions
```
  ensures y >= 0                
  ensures y == x || y == -x     
```
together ensure that `Abs` satsifies its mathematical specification. Moreover, Dafny verifies that the postcondition is true. For much more on this example, as well as a wide ranging introduction, see [Getting Started with Dafny: A Guide](https://github.com/dafny-lang/dafny/blob/master/docs/OnlineTutorial/guide.md).

### First Exercise

What happens for the following implementation of integer division?
```dafny
method Divide(x: int, y: int) returns (q: int)
  requires true 
  ensures x == q * y + (x % y)
{ q := x / y; }
```
How do you interpret the answer when you [try it out](https://tio.run/##Jck9CgIxFEXhflZxGiGjwvQj6dyIkCemmEj@JEFm7fGptznwXXe7hz7GJuXxdFz9yzsxbcWHcqb/OpOk1BQyJv5hQilWnyRTUhV0ahJy/VLDWiJHOidM40Cfp7fKavVb6Bf2MT4)?
Can you change the program so that the Dafny program verifier finishes with 0 errors?

## Introductory Examples

Get started at [https://dafny.org/](https://dafny.org) and install the Dafny extension in Vscode. Make sure to have the .NET runtime (available on Macos via `brew install dotnet`).

Save the following as [Divide.dfy](../src/dafny/Divide.dfy)
```dafny
method Divide(x: int, y: int) returns (q: int, r: int)
  requires y > 0     // divisor must be positive
  requires x >= 0    // to keep it simple
  ensures x == q * y + r
  ensures 0 <= r < y
{
  q := 0;
  r := x;
  while r >= y
    invariant 0 <= r
    invariant x == q * y + r
  {
    r := r - y;
    q := q + 1;
  }
}

method Main() {
  var quotient, remainder := Divide(12,8);
  print "Divide(12,8) = ", quotient, ", remainder = ", remainder, "\n";
}
```
**Exercise/Activity:**
- Do you see green checkmarks in the IDE (indicating that this code has been verfied)?
- Run the code from the commandline with `dafny run Divide.dfy` (may require setting a path variable or separate installation via eg `brew install dafny`).
- What happens if you delete the line `requires x >= 0` (save as `Divide2.dfy`) expressing the precondition that the dividend cannot be negative and run the program with `Divide(-12,8)`?
- Run the modified code with `dafny run Divide2.dfy` and with `dafny run --no-verify Divide2.dfy`. How do you interpret the results?
- How do you change `Divide2.dfy` so that it can accomodate negative dividends? (Note that integer division must return a non-negative remainder.)

## Basic Theory

...

## The Landscape of Tools

## Algorithms

## Benchmark and Competitions

## Applications in Industry

## Case Studies

## History

## Current Development, Research Challenges, Conferences and Workshops

## References

Introductions:
- [Getting Started with Dafny: A Guide](https://github.com/dafny-lang/dafny/blob/master/docs/OnlineTutorial/guide.md)

Applications:
- [@Scholar: AWS Dafny](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=aws+dafny&btnG=)
- [@Scholar: Dafny Smart Contracts](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%22dafny%22+%22smart+contracts%22&btnG=)
- [@Scholar: Dafny IronFleet](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%22dafny%22+%22IronFleet%22&btnG=)
- [@ Scholar: Separation logic Facebook](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%22O%27Hearn%22+%22separation+logic%22+%22facebook%22&btnG=)
## Suggestions for future work on the book