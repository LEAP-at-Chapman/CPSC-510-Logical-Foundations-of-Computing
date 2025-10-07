# Temporal Logic with Spin

## Idea

Temporal logic is a system of logic used to reason about time. A statement in temporal logic may have a truth value that changes over the course of time. It includes new qualifiers that relate to time, such as: *always*, *eventually*, *never*, *until*, *whenever* etc.

For example: I will *eventually* be hungry

This mode of logic can be very useful in concurrent systems where two threads must be made to *never* access the same reasource at the same time. 

## Basic Theory

Temporal logic is used to reason about things in terms of time. For example, a statement like "It is raining" may vary in truth throughout time. Sometimes it will be raining and sometimes it will not be raining. Temporal logic allows truth values to vary throughout time. There are many different types of temporal logic, some allow you to view the system as a single path through time, while some may involve multiple timelines. 

It includes all basic logical operators: and, or, not and implies.

It also includes several additional modal operators:
* Until (U):
    A U B means that A must be true until B becomes true, after which A no longer needs to be true.
* Release (R):
    A R B means that B is true up to and including the first position in which A is true.
* Next (N or a Circle):
    N A means that A must be true in the next state.
* Future (F or a Diamond):
    F A means that A must be true somewhere ahead of the current position in time.
* Globally (G or Box):
    G A means that A must be true for the rest of the timeline or path.
* For All (A or an upsidedown A):
    A B means that B must be true on all paths starting from the current position.
* There Exists (E or a backwards E):
    E A means that there exists at least one path starting from the current position where A is true.

## Tool

The tool we will be using to explore temporal logic is called SPIN. It is primarily used to verify multithreaded software.

# Installation
Link: https://spinroot.com/spin/Man/README.html


# Example
# Excercise

## References
* https://en.wikipedia.org/wiki/Temporal_logic#Temporal_operators
* https://en.wikipedia.org/wiki/SPIN_model_checker
* https://spinroot.com/spin/whatispin.html

