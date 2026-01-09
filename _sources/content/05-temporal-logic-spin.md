# Temporal Logic with Spin
Author: *Jack de Bruyn*

## Idea

Temporal logic is a logic used to reason about time. A statement in temporal logic may have a truth value that changes over the course of time. It includes new connectives that relate to time, such as: *always*, *eventually*, *never*, *until*, *whenever* etc.

For example: I will *eventually* be hungry

This mode of logic can be very useful in concurrent systems where two threads must be made to *never* access the same resource at the same time. 

## Basic Theory

Temporal logic is used to reason about things in terms of time. For example, a statement like "It is raining" may vary in truth throughout time. Sometimes it will be raining and sometimes it will not be raining. Temporal logic allows truth values to vary throughout time. There are many different types of temporal logic, some allow you to view the system as a single path through time, while some may involve multiple timelines. 

It includes all basic logical operators: and, or, not and implies.

It also includes several additional modal operators:
* Until (U):
    A U B means that A must be true until B becomes true, after which A no longer needs to be true.
* Release (R):
    A R B means that B is true up to and including the first position in which A is true.
* Next (⭘):
    ⭘ A means that A must be true in the next state.
* Future (◊):
    ◊ A means that A must be true somewhere ahead of the current position in time.
* Globally (☐):
    ☐ A means that A must be true for the rest of the timeline or path.
* For All (☐):
    ☐ A means that A must be true on all paths starting from the current position.
* There Exists (◊):
    ◊ A means that there exists at least one path starting from the current position where A is true.

## Tool

The tool we will be using to explore temporal logic is called SPIN. It is primarily used to verify multithreaded software. SPIN uses a coding language called Promela.

### Installation
[Link to Install](https://spinroot.com/spin/Man/README.html)

Some examples taken from [here](https://spinroot.com/courses/summer/).

I find it easiest to use Ubuntu or Debian to install it, as it can be done with a simple `sudo apt-get install spin`.

### First Example
To test if SPIN works on your machine try run this code:

Note: you will need a C compiler to run SPIN.
```promela
init {	// file: ex_1a.pml
		byte i	// initialized to 0 by default
		do	// loop forever
		:: i++	// nondisterministic choice, only one option
		od
	}
```
run with `$ spin -u514 -p -l ex_1a.pml`

This should print 514 steps of increasing numbers.

### First Exercise

The following is a basic handshake protocol between two processes, written in Promela. Process A sends signal a1 to initiate, then process B sends signal b1 when it receives signal a1, and when A receives b1 it sends signal a1 again, restarting the process. The program also includes some basic error handling.

Load this program into SPIN and try answering the questions below.

```promela
mtype = { a0, a1, b0, b1, err } // file ex_2.pml

chan a2b = [0] of { mtype }	// a rendezvous channel for messages from A to B
chan b2a = [0] of { mtype }	// a second channel for the reverse direction

active proctype A()
{
  S1:	a2b!a1
  S2:	if
  	:: b2a?b1  -> goto S1
  	:: b2a?b0  -> goto S3
  	:: b2a?err -> goto S5
  	fi
  S3:	a2b!a1  -> goto S2
  S4:	b2a?err -> goto S5
  S5:	a2b!a0  -> goto S4
 }
  
active proctype B()
{
  	goto S2
  S1:	b2a!b1
  S2:	if
  	:: a2b?a0  -> goto S3
  	:: a2b?a1  -> goto S1
  	:: a2b?err -> goto S5
 	fi
  S3:	b2a!b0 -> goto S2
  S4:	a2b?_  -> goto S1
  S5:	a2b!b0 -> goto S4
}
```

1. Use SPIN to verify if there are any unreachable states. Explain the result.

2. How would you modify the model to make all states reachable? 

## The Farmer and the River
(Source: [[1]](https://github.com/LEAP-at-Chapman/Intro-to-Model-Checking-with-Spin/), [[2]](https://github.com/LEAP-at-Chapman/Intro-to-Model-Checking-with-Spin/blob/main/notes/Wolf-Goat-Cabbage.md))

A farmer wants to move a cabbage, a goat, and a wolf across a river in his boat. He can only fit one thing in his boat while going across. If the farmer isn't watching, the goat will eat the cabbage, and the wolf will eat the goat. Can you think of a way to model this problem and find it's solution in SPIN?

Note: SPIN allows you to both define the solution in the code and in the formula you run from the command line.

To check a model with formulas, you must first define them in the file with `#define`. These defined formulas should begin with a lowercase letter.

Afterwards you may run your model with formulas by typing the following and replacing FORMULA with the formula you wish to use (ie <>cond2):

```bash
spin -a -f 'FORMULA' wgc.pml
gcc -o pan pan.c
./pan -a
spin -t wgc.pml
```

If SPIN can verify the code, it will generate a trail file. Make sure to delete any existing trail files in the folder before you run your program, as this may lead to confusion.


## The Landscape of Tools

Information below is mainly taken from [here](https://mluckcuck.github.io/model-checking-cheatsheet) as well as the websites and wikipedia pages for each model checker.

Other Model Checkers:
1. [NuSMV](https://nusmv.fbk.eu/)

A version of a model checker called SMV, but using temporal logic. Specifically uses Linear Temporal Logic or Computation Tree Logic. Programs are written in binary decision diagrams, which are data structures that can be used to represent booleans.

2. [PRISM](https://www.prismmodelchecker.org/)

PRISM is a probabilistic model checker using its own language, also called PRISM. It is useful for models that contain probabilities or other randomness.

3. [FDR](https://cocotec.io/fdr/)

A model checker specifically designed for CSP, which itself is a language for describing concurrent systems designed by Tony Hoare. Short for Failure Divergence Refinement.

4. [ProB](https://prob.hhu.de/)

A model checker for B-Method and Event-B. B is designed to support turning formal specifications into code.

5. [Java Pathfinder](https://github.com/javapathfinder)

Model checker specifically designed for Java. It creates its own Java Virtual Machine that runs all possible combinations of paths through a given program.

6. [UPPAAL](https://uppaal.org/)

A model checker designed to model systems made of timed automata. Uses a simplified form of Timed TCTL.

## Algorithms

In general, model checking with Linear Temporal Logic is not NP complete due to requiring the checking of infinitely many paths ([Bauland et al., 2008](https://arxiv.org/abs/0805.0498)). However, certain fragments of the logic that limit some of the universal quantifiers are NP complete. When SPIN verifies a system, several steps are taken.

1. The user must describe the system in Promela (Process Meta Language), which is SPIN's programming language.

2. The statements within this program (which are expressed as Linear-Temporal Logic), are converted into [Büchi Automata](https://en.wikipedia.org/wiki/B%C3%BCchi_automaton). These Automata are state machines that accept or rejects infinite inputs. 

3. SPIN generates C source code for a model checker specifically designed to verify the defined system, instead of running the verification itself.

## Benchmarks

I looked into benchmarks for SPIN and other model checkers, however at the time of writing, there does not appear to have been many benchmarks of such tools available online.

I found a research paper that declared its intent to create a benchmark of model checkers like SPIN, located [here](https://spinroot.com/spin/symposia/ws07/Pelanek.pdf). However, at the time of writing, the [link](https://anna.fi.muni.cz/models) contained in the paper leads to a 404 error.

## Applications in Industry

One of the main applications of SPIN in the industry is model checking for concurrency or mutual exclusion problems. For example, it is often the case where two processes are running in parallel and must read and write from the same resource. These processes cannot be allowed to access the resource at the same time to avoid memory problems. However both processes must access the resource *eventually*. This problem and problems like it can be modeled and checked in SPIN.

SPIN has also been used for a number of other, more specific applications in the industry. For instance, back in the early 2000s some researchers used SPIN  to verify the flight software of spacecraft ([Gluck and Holtzman, 2008](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Using+SPIN+model+checking+for+flight+software+verification&btnG=)). Given the risks of spaceflight, double and triple checking everything is the norm, which is especially important for something as vital as the central flight system of a craft. 

Additionally the automotive industry had run into some trouble ensuring the reliability of their vehicle systems due to increasing complexity ([Zhang et al., 2018](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Verifying+OSEK%2FVDX+automotive+applications%3A+A+Spin-based+model+checking+approach&btnG=)). SMT-based checking isn't very efficient as it can't handle loops or interruptions very well ([Zhang et al., 2018](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Verifying+OSEK%2FVDX+automotive+applications%3A+A+Spin-based+model+checking+approach&btnG=)). As such, SPIN was proposed as an alternative and was found to be quite efficient at verifying such systems ([Zhang et al., 2018](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Verifying+OSEK%2FVDX+automotive+applications%3A+A+Spin-based+model+checking+approach&btnG=)).

Model checkers like SPIN can also be used to help find design flaws in web applications, or to simplify their designs ([Alzahrani and Mohammed Yahya, 2015](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Model+checking+web+applications+heriot+watt+university&btnG=)). The researchers in this paper tested SPINs ability to verify web applications and compared it against another model checker (Upaal) to ensure it was correct ([Alzahrani and Mohammed Yahya, 2015](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Model+checking+web+applications+heriot+watt+university&btnG=)).

## Needham-Schroeder Protocol

(Source: [[1]](https://github.com/LEAP-at-Chapman/Intro-to-Model-Checking-with-Spin/), [[2]](https://github.com/LEAP-at-Chapman/Intro-to-Model-Checking-with-Spin/blob/main/notes/Needham-Schroeder.md))

In this case study, we will look at the Needham-Schroeder Protocol. The Needham-Schroeder Public Key Protocol was an oft-used encryption protocol for communicating across the internet. It utilized public key encryption to exchange a secret between both parties. This secret then allowed them to continue conversing securely. After 17 years, a flaw was found in the protocol that would allow an attacker to listen in on communications that were supposed to be secure. The attack was discovered using model checking.

The Needham-Schroeder Protocol works as follows:

1. Alice send Bob a message with her address and a unique random number.

2. Bob sends Alice a message with the same random number along with another unique random number.

3. Alice sends back Bob's random number.

4. The handshake is complete, communication may begin.

These messages are encoded with Public Key Encryption, which is secure but expensive, hence why it isn't used for the whole conversation. 

A program that can be used to find this flaw is located [here](https://github.com/LEAP-at-Chapman/Intro-to-Model-Checking-with-Spin/blob/main/src/Needham-Schroeder/ns.pml). 

A fix was proposed by the person who found this fault. To avoid the attack, the second message should also include Bob's address. Can you explain how this avoids the attack? Try editing the SPIN program to include this fix, does it prevent the attack?

## History

Most information gathered from [Temporal Logic](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=temporal+logic+N+Rescher%2C+A+Urquhart&btnG=) by N Rescher and A Urquhart, as well as some additional information taken from the [wiki](https://en.wikipedia.org/wiki/Temporal_logic#Temporal_operators) on Temporal Logic and [SPIN's history tab](https://spinroot.com/spin/Doc/roots.html).

- 1947: Jerzy Łoś first formalizes a logic with temporal functions in the book, *The Foundations of a Methodological Analysis of Mill's Methods*. The aim of this book was to formalize Mill's methods of induction, but in the process Łoś created the first working instance of temporal logic.

- 1953: Arthur Prior begins research on Temporal Logic. He was apparently interested in questions of free will. While his work shared overlap with Łoś', he would not officially reference Łoś until two years later.

- 1957: Prior publishes a book on temporal logic called *Time and Modality*. For a time this was the widely accepted beginning of temporal logic. Prior formalized the more modern version of temporal logic, using modal operators.

- 1958: Prior gets a letter from Saul Kripke, pointing out to him the possibilities of branching time. This caused Prior to reevaluate his assumption that time must be linear, and he went on to develop two theories of branching time.

- 1967: Prior publishes *Past, Present and Future*, a collection of his most revised theories on temporal logic, before dying two years later.

- 1980: The first precursor to SPIN is developed, called Pan. Pan shared many properties with SPIN, but it only had access to safety conditions.

- 1983: The successor to Pan is developed, called Trace. This model checker swapped process algebras for automata as its verification method.

- 1989: The first version of SPIN is developed. It was originally intended to simply be a small example model checker for a course on protocol verification. Over the following years it would be improved and expanded upon until it began the version we use today.

## Current Developments

1. [International Symposium on Temporal Representation and Reasoning (TIME)](https://time-symposium.org/t/):

TIME is not exclusively dedicated to temporal logic, but does include a number of papers on the subject. It officially began in 1994, and claims to be "the only yearly multidisciplinary international event dedicated to the topic of time in computer science" (TIME, 2022). Also includes overlap with spatial reasoning topics.

2. [International Conference on Formal Modeling and Analysis of Timed Systems](https://www.formats-conference.org/)

Also called FORMATS. This conference focuses on bringing together all discussions of timing in computer science, from embedded systems to verification. The conference holders believe that each of these disciplines share some basic problems related to timing that would benefit from a shared discussion.

The following is one of the papers from this conference that I found interesting:

[Stochastic Temporal Logic Abstractions: Challenges and Opportunities](https://link.springer.com/chapter/10.1007/978-3-030-00151-3_1) (Deshmukh, Kyriakis, and Bogdan, 2018)

This paper suggests using temporal logic to model the uncertainty of an environment. The paper delves into the potential applications of such an approach, but also discusses some of the challenges associated with it.

## References

- Rescher and Urquhart (1971). [Temporal Logic](https://scholar.google.com/scholar?q=Temporal+Logic+Rescher+Urquhart), Springer-Verlag/Wien

- Bauland et al. (2008). [The Tractability of Model-Checking for LTL: The Good, the Bad, and the Ugly Fragments](https://scholar.google.com/scholar?q=The+Tractability+of+Model-Checking+for+LTL+The+Good+the+Bad+and+the+Ugly+Fragments), arXiv

- Gluck and Holtzman (2008). [Using SPIN model checking for flight software verification](https://scholar.google.com/scholar?q=Using+SPIN+model+checking+for+flight+software+verification), IEEE

- Alzahrani and Mohammed Yahya (2015). [Model checking web applications](https://scholar.google.com/scholar?q=Model+checking+web+applications+heriot+watt+university), Heriot Watt University

- Deshmukh, Kyriakis, and Bogdan (2018). [Stochastic Temporal Logic Abstractions: Challenges and Opportunities](https://scholar.google.com/scholar?q=Stochastic+Temporal+Logic+Abstractions+Challenges+and+Opportunities), Springer

- Zhang, Li, Cheng, and Xue (2018). [Verifying OSEK/VDX automotive applications: A Spin-based model checking approach](https://scholar.google.com/scholar?q=Verifying+OSEK+VDX+automotive+applications+A+Spin-based+model+checking+approach), Wiley

- TIME (2022). [International Symposium on Temporal Representation and Reasoning (TIME)](https://time-symposium.org/t/), TIME

## Further Resources
* [Introduction to Model Checking with Spin](https://github.com/LEAP-at-Chapman/Intro-to-Model-Checking-with-Spin/), LEAP-at-Chapman.
* [Wikipedia Article on Temporal Logic](https://en.wikipedia.org/wiki/Temporal_logic#Temporal_operators). Contains a good overview of the logic with links to more in-depth reading.
* [Wikipedia Article on SPIN](https://en.wikipedia.org/wiki/SPIN_model_checker).
* [SPIN's Website](https://spinroot.com/spin/whatispin.html).
* [Some examples for getting to know SPIN](https://spinroot.com/courses/summer/).
* [A paper discussing the benchmarking of various model checkers](https://spinroot.com/spin/symposia/ws07/Pelanek.pdf). Sadly appears somewhat incomplete at time of writing.
* [An overview of various model checkers](https://mluckcuck.github.io/model-checking-cheatsheet).
* [A link to the TIME symposium](https://time-symposium.org/t/)
* [A quick guide to SPIN's history](https://spinroot.com/spin/Doc/roots.html)

## Future Work 

For future work on this chapter, I would suggest expanding the algorithm section. As it stands currently it only gives a brief overview of SPIN's algorithm, which could likely warrant further inspection.

Additionally, it would be good to check in on the benchmarks of the various temporal logic model checkers. As mentioned in the paper there does not seem to be any available at the time of writing. I would be interested in seeing if this changes in the future.

Lastly an additional case study that could be interesting to look into is the idea of automated code verification for generative AI. A lot of talk has been made over whether gen AI could be used to create code automatically. One of the issues with this approach is that it's difficult to tell whether the code generated actually works. As such it would be interesting to integrate SPIN into this process; using some combination of genAI and SPIN to automatically generate and verify code segments.
