# Hoare Logic with Dafny

*Author: Alex*

## Idea

### Idea

Hoare Logic is a formal system for proving program correctness using logical assertions. It represents programs as Hoare triples:

{P}\ C\ {Q}

where (P) is the precondition, (C) the command, and (Q) the postcondition. For example:

{x = 2}\ x := x + 3\ {x = 5}

means that if (x = 2) before execution, then (x = 5) afterward.

Hoare logic forms the basis of modern verification tools like Dafny, which extend it with loop invariants, assertions, and automated theorem proving. Unlike testing, which checks correctness for specific cases, Hoare logic proves correctness for all possible executions.


## Topics

- Hoare logic foundations
- Dafny installation and setup
- Specification languages
- Program verification techniques
- Industrial applications

## Resources

- [Dafny](https://github.com/dafny-lang/dafny)
- [Dafny Tutorial](https://dafny.org/dafny/OnlineTutorial/guide)
- [Dafny Video Tutorial](https://www.youtube.com/watch?v=oLS_y842fMc)

## Exercises

*To be added*
