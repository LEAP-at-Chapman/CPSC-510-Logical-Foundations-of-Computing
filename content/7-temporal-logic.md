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

The tool we will be using to explore temporal logic is called SPIN. It is primarily used to verify multithreaded software. SPIN uses a coding language called promela.

### Installation
Link: https://spinroot.com/spin/Man/README.html

Some examples taken from: https://spinroot.com/courses/summer/

I find it easiest to use Ubuntu or Debian to install it, as it can be done with a simple `sudo apt-get install spin`.

### First Example

init {	// file: ex_1a.pml
		byte i	// initialized to 0 by default
		do	// loop forever
		:: i++	// nondisterministic choice, only one option
		od
	}

run with `$ spin -u514 -p -l ex_1a.pml`

This should print 514 steps of increasing numbers.

### First Excercise
A farmer wants to move a cabbage, a goat, and a wolf across a river in his boat. He can only fit one thing in his boat while going across. If the farmer isn't watching, the goat will eat the cabbage, and the wolf will eat the goat. Can you think of a way to model this problem and find it's solution in SPIN?

Note: SPIN allows you to both define the solution in the code and in the fourmula you run from the command line.

## Intro Examples

## The Landscape of Tools

## Algorithms

## Benchmarks

## Applications in Industry

One of the main applications of SPIN in the industry is model checking for concurecy. 

## Case Studies

## History

## Current Development, Research Challenges, Conferences and Workshops

## References
* https://en.wikipedia.org/wiki/Temporal_logic#Temporal_operators
* https://en.wikipedia.org/wiki/SPIN_model_checker
* https://spinroot.com/spin/whatispin.html
* https://spinroot.com/courses/summer/

## Suggestions for Future Work on this Book
