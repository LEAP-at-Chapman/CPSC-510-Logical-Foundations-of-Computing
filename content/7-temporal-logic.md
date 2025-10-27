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
* For All (A or an upsidedown A, also sometimes called box `[]`):
    A B means that B must be true on all paths starting from the current position.
* There Exists (E or a backwards E, also sometimes called diamond `<>`):
    E A means that there exists at least one path starting from the current position where A is true.

## Tool

The tool we will be using to explore temporal logic is called SPIN. It is primarily used to verify multithreaded software. SPIN uses a coding language called promela.

### Installation
Link: https://spinroot.com/spin/Man/README.html

Some examples taken from: https://spinroot.com/courses/summer/

I find it easiest to use Ubuntu or Debian to install it, as it can be done with a simple `sudo apt-get install spin`.

### First Example
To test if SPIN works on your machine try run this code:

Note: you will need a C compiler to run SPIN.

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

To check a model with fourmulas, you must first define them in the file with `#define`. These defined fourmulas should begin with a lowercase letter.

Afterwards you may run your model with fourmulas by typing the following and replacing FOURMULA with the fourmula you wish to use (ie <>cond2):

```bash
spin -a -f 'FORMULA' wgc.pml
gcc -o pan pan.c
./pan -a
spin -t wgc.pml
```

If SPIN can verify the code, it will generate a trail file. Make sure to delete any existing trail files in the folder before you run your program, as this may lead to confusion.

## Intro Examples

## The Landscape of Tools

## Algorithms

## Benchmarks

I looked into benchmarks for SPIN and other model checkers, however at the time of writing, there does not appear to have been many benchmarks of such tools available online.

I found a research paper that declared its intent to create a benchmark of model checkers like SPIN, located at https://spinroot.com/spin/symposia/ws07/Pelanek.pdf. However, at the time of writing, the link contained in the paper (https://anna.fi.muni.cz/models) leads to a 404 error.

## Applications in Industry

One of the main applications of SPIN in the industry is model checking for concurecy or mutual exculsion problems. For example, it is often the case where two processes are running in parallel and must read and write from the same reasource. These processes cannot be allowed to access the reasource at the same time to avoid memory problems. However both processes must access the reasource *eventually*. This problem and problems like it can be modeled and checked in SPIN.

## Case Studies

### Finding the Fault in the Needham-Schroedor Protocol

The Needham-Schroedor Public Key Protocol was an oft-used encryption protocol for communicating across the internet. It ustilized public key encryption to exchange a secrect between both parties. This secrect then allowed them to continue conversing securely. After 17 years, a flaw was found in the protocol that would allow an attacker to listen in on communications that were supposed to be secure. The attack was discovered using model checking.

The Needham-Schroedor Protocol works as follows:

1. Alice send Bob a message with her address and a unique random number.

2. Bob sends Alice a message with the same random number along with another unique random number.

3. Alice sends back Bob's random number.

4. The handshake is complete, communication may begin.

These messages are encoded with Public Key Encryption, which is secure but expensive, hence why it isn't used for the whole conversation. 

The following is a link to a SPIN program that can be used to find the flaw in the protocol. This program was written by Professor Kurtz.

https://github.com/LEAP-at-Chapman/Intro-to-Model-Checking-with-Spin/blob/main/src/Needham-Schroeder/ns.pml

A fix was proposed by the person who found this fault. To avoid the attack, the second message should also include Bob's address. Can you explain how this avoids the attack? Try editing the SPIN program to include this fix, does it prevent the attack?

## History

## Current Development, Research Challenges, Conferences and Workshops

## References
* https://en.wikipedia.org/wiki/Temporal_logic#Temporal_operators
* https://en.wikipedia.org/wiki/SPIN_model_checker
* https://spinroot.com/spin/whatispin.html
* https://spinroot.com/courses/summer/
* https://spinroot.com/spin/symposia/ws07/Pelanek.pdf


## Suggestions for Future Work on this Book
