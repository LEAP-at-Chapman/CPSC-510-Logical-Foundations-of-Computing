# Hoare Logic with Dafny

*Author: Alex*

## Idea

Hoare Logic introduced the idea that we can reason about programs the same way we reason about mathematical proofs by introducing program verification. Instead of observing program behavior through test cases, we showcase what a program should do in logical form, and then prove that it does so. At its core lies the Hoare triple:

[{P}; C; {Q}]

This notation captures the relationship between a precondition (P), a command (C), and a postcondition (Q). This notation reads as:

<p align="center"> If the execution of program P begins in a state where the precondition C holds, then upon termination, the postcondition Q will hold. </p>

Each component plays a specific role:
- **P** (Precondition) - describes the assumptions or required state before execution.
- **C** (Command) - represents a piece of the program
- **Q** (Postcondition) - expresses what is guaranteed to be true after execution if the program halts.

This logic provides partial correctness, meaning the result will be correct if the program terminates. To achieve​​ total correctness, we must demonstrate that the program terminates. 

## Basic Theory

*To be added*

## Dafny Installation and Setup

### Windows Installation

#### 1. Requirements
- [.NET 8.0 SDK](https://dotnet.microsoft.com/download/dotnet/8.0)
- **Z3 Theorem Prover v4.12.1**
- Windows Server 2019 or 2022 (tested)

---

#### 2. Install Dafny
```bash
# 1. Install .NET 8.0
# 2. Download Dafny ZIP from:
#    https://github.com/dafny-lang/dafny/releases/latest
# 3. Right-click → Properties → Unblock → OK
# 4. Extract to a folder, then run:
Dafny.exe
```

#### 3. VS Code Integration (Recommended)
- Install Visual Studio Code.
- Open VS Code → press Ctrl+P → run:
```bash
ext install dafny-lang.ide-vscode
```
- Open a .dfy file to activate Dafny.

#### 4. Compile Dafny Programs

| Target     | Requirements     | Example                             |
| ---------- | ---------------- | ----------------------------------- |
| **C#**     | .NET 8.0 SDK     | `dafny build -t:cs MyProgram.dfy`   |
| **Java**   | Java ≥ 8, Gradle | `dafny build -t:java MyProgram.dfy` |
| **Python** | Python ≥ 3.7     | `dafny build -t:py MyProgram.dfy`   |

Run directly:
```bash
dafny run MyProgram.dfy
```

#### 5. Developer Build
```bash
# Install dependencies
pip install pre-commit && pre-commit install

# Clone Dafny
git clone https://github.com/dafny-lang/dafny --recurse-submodules

# Build
dotnet build dafny/Source/Dafny.sln

# Add Z3
# Place z3.exe in dafny/Binaries/z3/bin/
```

Run Tests:
```bash
cd dafny/Source/IntegrationTests
dotnet test -v:n
```

### Mac Installation

#### 1. Requirements
Install .NET 8.0 SDK:
```bash
brew install dotnet-sdk
```

#### 2. Install Dafny
```bash
brew install dafny
```

#### 3. VS Code Integration (Recommended)
- Install Visual Studio Code.
- Open VS Code → press Ctrl+P → run:
```bash
ext install dafny-lang.ide-vscode
```
- Open a .dfy file to activate Dafny.

#### 4. Compile Dafny Programs

| Target         | Requirements     | Example                             |
| -------------- | ---------------- | ----------------------------------- |
| **C#**         | .NET 8.0 SDK     | `dafny build -t:cs MyProgram.dfy`   |
| **Java**       | Java ≥ 8, Gradle | `dafny build -t:java MyProgram.dfy` |
| **Python**     | Python ≥ 3.7     | `dafny build -t:py MyProgram.dfy`   |
| **Go**         | Go ≥ 1.18        | `dafny build -t:go MyProgram.dfy`   |
| **JavaScript** | Node ≥ 16        | `dafny build -t:js MyProgram.dfy`   |

Run:
```bash
dafny run MyProgram.dfy
```

#### 5. Developer Build
```bash
brew install python3 pre-commit wget
git clone https://github.com/dafny-lang/dafny.git --recurse-submodules
cd dafny
make exe
pre-commit install

# Install Z3 4.12.1
make z3-mac
# or manually:
cd Binaries
wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-08-02/z3-4.12.1-x64-macos-11-bin.zip
unzip z3-4.12.1-x64-macos-11-bin.zip
mv z3-4.12.1 z3
```

Run Dafny:
```bash
./Scripts/dafny
./Scripts/quicktest.sh
```

Run Tests
```bash
cd Source/IntegrationTests
dotnet test -v:n
```

### Linux Installation

#### 1. Requirements

.NET 8.0 SDK
```bash
sudo apt install dotnet-sdk-8.0
```

Python 3 + pip

```bash
sudo apt install python3 python3-pip
```

#### 2. Install Dafny
```bash
wget https://github.com/dafny-lang/dafny/releases/latest/download/dafny.zip
unzip dafny.zip
./dafny/dafny
```

#### 3. Compile Dafny Programs
| Target     | Requirements     | Example                             |
| ---------- | ---------------- | ----------------------------------- |
| **C#**     | .NET 8.0 SDK     | `dafny build -t:cs MyProgram.dfy`   |
| **Java**   | Java ≥ 8, Gradle | `dafny build -t:java MyProgram.dfy` |
| **Python** | Python ≥ 3.7     | `dafny build -t:py MyProgram.dfy`   |
| **Go**     | Go ≥ 1.18        | `dafny build -t:go MyProgram.dfy`   |

Run: 
```bash
dafny run MyProgram.dfy
```

#### 4. Developer Build
```bash
sudo apt install dotnet-sdk-8.0 python3 python3-pip
git clone https://github.com/dafny-lang/dafny.git --recurse-submodules
cd dafny
make exe
pip3 install pre-commit && pre-commit install

# Install Z3 4.12.1
make z3-ubuntu
# or manually:
cd Binaries
wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-08-02/z3-4.12.1-x64-ubuntu-20.04-bin.zip
unzip z3-4.12.1-x64-ubuntu-20.04-bin.zip
mv z3-4.12.1 z3
```

Run Dafny:
```bash
./Scripts/dafny
./Scripts/quicktest.sh
```

Run Tests:
```bash
cd Source/IntegrationTests
dotnet test -v:n
```

## Program Verification Techniques

*To be added*

## Exercises

*To be added*

## The Landscape of Tools

*To be added*

## Benchmark and Competitions

*To be added*

## Applications in Industry

Using preconditions, postconditions, and invariants, as Hoare Logic showcases, this reasoning is now embedded in modern tools and workflows. These principles have now influenced every layer of software reliability. Here are a few examples of how Hoare Logic has been implemented in industry:

- **Safety-Critical Systems:**
In safety-critical systems, such as those in the aerospace and medical device industries, implement Hoare Logic through rigorous reasoning using preconditions, postconditions, and invariants. The implementation of the Hoare Triple ensures software correctness, particularly in cases where failure can be catastrophic. NASA's use of highly complex software makes testing impossible, especially when failures need to have probabilities on the order of 10⁻⁹ per hour. This highly rare, even if subtle, edge-case condition must be proven safe rather than minimally tested. Formal verification supports the validation of flight-control algorithms, redundancy management logic, timing-critical tasks, and fault-tolerant coordination across distributed systems.

- **Static Analysis and Software Quality:**
Modern tools such as Facebook Infer and Microsoft Code Contracts apply Hoare Logic-based reasoning to automatically detect bugs, memory leaks, and logic errors before runtime.


## Case Studies

*To be added*

## History

In 1949, Alan Turing presented his paper, “Checking a Large Routine”, which was one of the first attempts to describe how programmers could verify the correctness of their code. Throughout his paper, Turing proposed the idea of using assertion statements to explain what should be true at specific points in the program, thereby verifying its correctness. Additionally, Turing introduced the concept of a termination function as a method to ensure that the presented program eventually halts. Using a factorial program, Turing showed that logical reasoning could be applied to computer programs.

Throughout the 1960s, Robert Floyd built on Turing’s ideas by introducing the inductive assertion method, a systematic approach to proving the correctness of flowchart-based programs. Floyd proposed identifying key points in a program with logical statements called invariants, similar to the idea of assertion statements, which are both meant to show specific points during the program that must remain true throughout execution. Although the idea continued to build on Turing’s progress, this was limited to flowcharts rather than structured programming languages.

In the year 1969, C.A.R. Hoare continued to build on these ideas by introducing the Hoare triple: {P} S {Q}. This notation states that if the execution of program P begins in a state where the precondition C holds, then upon termination, the postcondition Q will hold. Although this development seemed simple, it proved to be powerful, as it created rules for statements, loops, and sequences. This notation enabled program proofs to be both structured and easier to understand due to their improved readability. The Hoare triple enabled program verification for all types of code, not just flowcharts, transforming program reasoning into a formal, language-based discipline. 

By the early 1970s, Hoare had expanded his logic to handle recursive procedures and local variables, which enabled reasoning about more complex programs. Working alongside Joseph Foley, he applied these ideas to verify the Quicksort algorithm, which was one of the first detailed proofs of correctness for a real-world program. Around the same time, Hoare began promoting the idea of programming and proving should be done simultaneously. This growing philosophy later influenced Edsger Dijkstra’s work on structured programming and program derivation, transforming Hoare Logic into a guide for creating verified software instead of verifying it after the fact.

The development of Hoare Logic established a foundation in computer science by shifting the perspective from viewing programs as sequences of commands to viewing them as logical systems that can be mathematically analyzed. Building upon Turing’s conceptual groundwork, refining Floyd’s formalization, and realizing Hoare’s framework, this lineage transformed programming into a science of correctness. To this day, Hoare Logic remains a foundational method of verification, and it also serves as a symbol of the connection between logic, mathematics, and computation.


## Current Development, Research Challenges, Conferences and Workshops

*To be added*

## Suggestions for future work on the book

*To be added*

## Resources

- [Dafny](https://github.com/dafny-lang/dafny)
- [Dafny Tutorial](https://dafny.org/dafny/OnlineTutorial/guide)
- [Dafny Video Tutorial](https://www.youtube.com/watch?v=oLS_y842fMc)

## References

- [Northeastern University – CS2800: Logic and Computation (Spring 2023) Lecture 32: Hoare Logic](https://course.ccs.neu.edu/cs2800sp23/l32.html)

- [University of Rochester – CSC 255/455: Programming Languages (Spring 2024) Lecture 25: Introduction to Hoare Logic](https://www.cs.rochester.edu/~spai4/courses/csc-255-455/spring-2024/static/25-intro-hoare-logic.pdf)

- [University of Pennsylvania – Software Foundations, Volume 2: Programming Language Foundations Chapter: Hoare Logic](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html)

- [Carnegie Mellon University – 15-654 Software Engineering (Spring 2006) Lecture Notes: Hoare Logic by Jonathan Aldrich](https://www.cs.cmu.edu/~aldrich/courses/654-sp06/notes/3-hoare-notes.pdf)

- [Alexander Kurz – Hoare Logic Example (HackMD) Worked example: Loop invariants and correctness proofs](https://hackmd.io/@alexhkurz/Hy135C2tH)

- [University of Cambridge – M.J.C. Gordon: Hoare Logic Lecture Notes All Lectures (Formal Semantics, wlp, VCG, and Separation Logic)](https://www.cl.cam.ac.uk/archive/mjcg/HoareLogic/Lectures/AllLectures.pdf)

- [Intro. to the Hoare Triple (Discrete Math Tutorial) - Validity, Calculating Precondition, Explained.](https://www.youtube.com/watch?v=-Bs2Uy3zGsw)

- [Fifty years of Hoare’s logic](https://ir.cwi.nl/pub/29146/29146.pdf)

- [Formal Methods and Their Role in Digital Systems Validation for Airborne Systems](https://ntrs.nasa.gov/api/citations/19960008816/downloads/19960008816.pdf)
