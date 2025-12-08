# Hoare Logic with Dafny

*Author: Alex*

## Idea

Hoare Logic is a mathematically based logic that focuses on proving that programs behave correctly, rather than relying on testing to determine their functionality. By treating programming as a formal reasoning process, where you specify what must be true before running a piece of code and what will be true after it finishes, the code can be verified and processed to ensure that, once correctly proven, the code satisfies this relationship.

The core tool is the Hoare Triple, which consists of the following format: { Precondition } Code { Postcondition }. Through this reasoning process, the Hoare Triple can view the program fragmented into logical terms. Using a set of inference rules, developers can prove the correctness of sequences, conditionals, and loops. 

Hoare Logic promotes correctness by construction, aiming to ensure that programs are built with proofs and formal logic every step of the program creation process, thereby eliminating bugs from any program development. By building on the idea of viewing program verification as a formal reasoning process, code verification and testing are simplified, with Hoare Logic serving as the foundation of modern formal verification.

## Basic Theory

Hoare Logic introduced the idea that we can reason about programs the same way we reason about mathematical proofs by introducing program verification. Instead of observing program behavior through test cases, we showcase what a program should do in logical form, and then prove that it does so. At its core lies the Hoare triple:

[{P}; C; {Q}]

This notation captures the relationship between a precondition (P), a command (C), and a postcondition (Q). This notation reads as:

<p align="center"> If the execution of program P begins in a state where the precondition C holds, then upon termination, the postcondition Q will hold. </p>

Each component plays a specific role:
- **P** (Precondition) - describes the assumptions or required state before execution.
- **C** (Command) - represents a piece of the program
- **Q** (Postcondition) - expresses what is guaranteed to be true after execution if the program halts.

This logic provides partial correctness, meaning the result will be correct if the program terminates. To achieve​​ total correctness, we must demonstrate that the program terminates. 


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

Dafny was built using the principles of Hoare Logic as a form of program verification. Through this, Dafyny integrated the Hoare Triple directly into the system language to verify what must be true before (pre-condition) and what must be true after program execution (post-condition). This integration of built-in formal reasoning enabled constructs such as ```requires``` and ```ensures``` to be part of the natural language. Additionally, Dafny development was also able to account for loops and recursions by utilizing invariants and termination conditions. 

Although a majority of the verification work in Dafny is handled by an SMT solver, this automated process alleviates the stress of manually constructing corrected proofs. This automated process, however, still requires human input to provide well-selected specifications and invariants, which can be deemed challenging, especially for more complex properties. 

Despite the challenges that selecting specifications and invariants may bring, Dafny has successfully demonstrated the practicality of implementing Hoare Logic. Through system-wide efforts to enforce program validations and correctness, users can develop programs without worrying about extensive testing. As a result of this constant verification, users can trust their programs, knowing that each portion of them has been thoroughly validated. Founded on the principle of ensuring that mathematical proofs function as intended, Hoare Logic provides a robust and reliable method for developing programs. 


## Exercises

### Ex. 1) Absolute Value in Dafny with Specifications

Write a Dafny method called ```Abs``` that:

1. Takes an integer input ```x```.

2. Returns an integer result ```r``` that is the absolute value of ```x```.

3. Includes postconditions (ensures clauses) that guarantee:

    - The result is always non-negative.

    - The result has the same magnitude as ```x```.

    - The result is either ```x``` or ```-x```.

**Step 1:**

To begin this exercise, we can simplify it by tackling one portion of the code at a time. Initially, we can start by taking into account the header that we need to use in order to get the absolute value of an integer input ```x```.

```
method Abs(x: int) returns (r: int)
```
This header method is named ```Abs```, which takes an integer ```x``` and returns an integer ```r```.

**Step 2:**

Now that the method and input parameters have been specified, we can add the ensures clauses, which are what we need to ensure are correct when verifying our program. 

```
  ensures r >= 0
  ensures r * r == x * x
  ensures r == x || r == -x
```

Through these clauses, we see that they are checking that: ```r``` is never negative, ```r``` keeps the same magnitude as ```x```, and ```r``` is either ```x``` (if positive) or ```–x ```(if negative). Dafny checks these automatically.

**Step 3:**

Lastly, the code that needs to be verified must be added to our program along with the respective parameters. 

```
if x >= 0 {
  r := x;
} else {
  r := -x;
}
```

This code checks if ```x``` is zero or positive and returns it as is. If ```x``` is negative, it flips the sign accordingly.

Once we have the entire code assembled together, we have the following program:

```
method Abs(x: int) returns (r: int)
  ensures r >= 0
  ensures r * r == x * x
  ensures r == x || r == -x
{
  if x >= 0 {
    r := x;
  } else {
    r := -x;
  }
}
```

This will result in the answer ```Abs(-5) = 5```.

### Ex. 2) Summing an Array in Dafny Using a Loop Invariant

Write a Dafny method called ```ArraySum``` that:

- Takes an array input ```a```.

- Returns an integer result ```total``` representing the sum of all elements.

- Uses a loop invariant to ensure correctness as the array is processed.

**Step 1:**

First, we define the method header and required input:

```
method ArraySum(a: array<int>) returns (total: int)
  requires a != null
```

This line introduces a method named ```ArraySum```, which takes an array ```a``` and returns an integer ```total```.
The requires clause ensures that the array must not be null before the method runs.

**Step 2:**

Next, we add the loop structure and initialize our variables:

```
{
  var i := 0;
  total := 0;
```

Through this loop structure, ```i``` starts at ```0``` and will move through the array as the total begins at 0 and will accumulate the sum.

**Step 3:**

We now include the loop and its invariant:

```
  while i < a.Length
    invariant 0 <= i <= a.Length
  {
    total := total + a[i];
    i := i + 1;
  }
}
```
This loop works by repeating while ```i``` is within the array bounds and adding each element to the total. As it loops, it increases ```i``` by ```1``` each iteration. The invariant ensures that ```i``` always stays between ```0``` and ```a.Length```. 

**Step 4:**

To verify that the method is working correctly, we can input this main method:
```
method Main()
{
  var a := new int[5];
  a[0] := 2;
  a[1] := 4;
  a[2] := -1;
  a[3] := 3;
  a[4] := 1;

  var result := ArraySum(a);
  print "Sum of array = ", result, "\n";
}
```

Once we have the entire code assembled together, we have the following program:

```
method ArraySum(a: array<int>) returns (total: int)
  requires a != null
{
  var i := 0;
  total := 0;

  while i < a.Length
    invariant 0 <= i <= a.Length
  {
    total := total + a[i];
    i := i + 1;
  }
}

method Main()
{
  var a := new int[5];
  a[0] := 2;
  a[1] := 4;
  a[2] := -1;
  a[3] := 3;
  a[4] := 1;

  var result := ArraySum(a);
  print "Sum of array = ", result, "\n";
}
```

Where it will result in:

```
Sum of array = 9
```

## The Landscape of Tools

*To be added*

## Benchmark and Competitions

The development of Hoare Logic continues to grow, as the number of conferences and workshops around program verification tools continues to increase. Events such as ETAPS, TACAS, FM, and the Dagstuhl seminars provide a platform for individuals to test new ideas and assess how tools perform on real-world problems. The VerifyThis competition has become especially influential. Participants are given problems, create specifications, and work with their verification tools within an allotted time limit. These events often lead to the development of contract notation, improved annotation design, stronger automation, and more helpful tool feedback. These developments shape the evolution of verification tools.

Additionally, these events highlight the challenges that researchers continue to face. Writing effective specifications and invariants still requires skill and insight. Even with recent advances, tools can produce confusing diagnostics or behave in ways that make it hard to understand what went wrong. When these issues arise, conferences and competitions provide researchers with a platform to discuss them directly. Comparing approaches, discussing which ideas are effective, and identifying areas where tools are still limited, enables an exchange that guides future improvements in program verification tools.

The VerifyThis competition has also contributed directly to the development of modern verification tools. Through this competition, many participants have been able to develop improvements as these events push them to refine their tools, adopt new specification features, and strengthen automation strategies. Surviving past competitions show that these newly implemented improvements often stem from insights gained during competitions such as VerifyThis. These teams observe how others formalize requirements, structure invariants, and interact with their tools under pressure. This collaborative environment fosters a feedback loop that supports steady progress in deductive verification research, ensuring that Hoare Logic continues to evolve as both a theoretical framework and a practical verification method.

## Applications in Industry

Using preconditions, postconditions, and invariants, as Hoare Logic showcases, this reasoning is now embedded in modern tools and workflows. These principles have now influenced every layer of software reliability. Here are a few examples of how Hoare Logic has been implemented in industry:

- **Safety-Critical Systems:**
In safety-critical systems, such as those in the aerospace and medical device industries, implement Hoare Logic through rigorous reasoning using preconditions, postconditions, and invariants. The implementation of the Hoare Triple ensures software correctness, particularly in cases where failure can be catastrophic. NASA's use of highly complex software makes testing impossible, especially when failures need to have probabilities on the order of 10⁻⁹ per hour. This highly rare, even if subtle, edge-case condition must be proven safe rather than minimally tested. Formal verification supports the validation of flight-control algorithms, redundancy management logic, timing-critical tasks, and fault-tolerant coordination across distributed systems.

- **Static Analysis:**
In static analysis, the Hoare Triple is used to reason all program states, ensuring correctness when testing alone can be insufficient. This reasoning is adjusted and adapted to work across various computational models. For synchronous languages, they are rewritten into a synchronous tuple assignment form, enabling grouped updates and macro-step boundaries to be verified through specialized axioms. Meanwhile, in quantum programs, redefined semantics, quantum predicates, and measurement-aware rules are used to handle superposition and probabilistic branching. In each case, static analysis becomes an automated form of Hoare-style reasoning adapted to the computational model, ensuring that correctness is proven.


## Case Studies

*To be added*

## History

In 1949, Alan Turing presented his paper, “Checking a Large Routine”, which was one of the first attempts to describe how programmers could verify the correctness of their code. Throughout his paper, Turing proposed the idea of using assertion statements to explain what should be true at specific points in the program, thereby verifying its correctness. Additionally, Turing introduced the concept of a termination function as a method to ensure that the presented program eventually halts. Using a factorial program, Turing showed that logical reasoning could be applied to computer programs.

Throughout the 1960s, Robert Floyd built on Turing’s ideas by introducing the inductive assertion method, a systematic approach to proving the correctness of flowchart-based programs. Floyd proposed identifying key points in a program with logical statements called invariants, similar to the idea of assertion statements, which are both meant to show specific points during the program that must remain true throughout execution. Although the idea continued to build on Turing’s progress, this was limited to flowcharts rather than structured programming languages.

In the year 1969, C.A.R. Hoare continued to build on these ideas by introducing the Hoare triple: {P} S {Q}. This notation states that if the execution of program P begins in a state where the precondition C holds, then upon termination, the postcondition Q will hold. Although this development seemed simple, it proved to be powerful, as it created rules for statements, loops, and sequences. This notation enabled program proofs to be both structured and easier to understand due to their improved readability. The Hoare triple enabled program verification for all types of code, not just flowcharts, transforming program reasoning into a formal, language-based discipline. 

By the early 1970s, Hoare had expanded his logic to handle recursive procedures and local variables, which enabled reasoning about more complex programs. Working alongside Joseph Foley, he applied these ideas to verify the Quicksort algorithm, which was one of the first detailed proofs of correctness for a real-world program. Around the same time, Hoare began promoting the idea of programming and proving should be done simultaneously. This growing philosophy later influenced Edsger Dijkstra’s work on structured programming and program derivation, transforming Hoare Logic into a guide for creating verified software instead of verifying it after the fact.

The development of Hoare Logic established a foundation in computer science by shifting the perspective from viewing programs as sequences of commands to viewing them as logical systems that can be mathematically analyzed. Building upon Turing’s conceptual groundwork, refining Floyd’s formalization, and realizing Hoare’s framework, this lineage transformed programming into a science of correctness. To this day, Hoare Logic remains a foundational method of verification, and it also serves as a symbol of the connection between logic, mathematics, and computation.

## Suggestions for future work on the book

*To be added*

## Hoare Logic in F*

*To be added*

## Resources

- [Dafny](https://github.com/dafny-lang/dafny)
- [Dafny Tutorial](https://dafny.org/dafny/OnlineTutorial/guide)
- [Dafny Video Tutorial](https://www.youtube.com/watch?v=oLS_y842fMc)

## References

- [University of Pennsylvania – Software Foundations, Volume 2: Programming Language Foundations Chapter: Hoare Logic](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html)

- [Carnegie Mellon University – 15-654 Software Engineering (Spring 2006) Lecture Notes: Hoare Logic by Jonathan Aldrich](https://www.cs.cmu.edu/~aldrich/courses/654-sp06/notes/3-hoare-notes.pdf)

- [Alexander Kurz – Hoare Logic Example (HackMD) Worked example: Loop invariants and correctness proofs](https://hackmd.io/@alexhkurz/Hy135C2tH)

- [University of Cambridge – M.J.C. Gordon: Hoare Logic Lecture Notes All Lectures (Formal Semantics, wlp, VCG, and Separation Logic)](https://www.cl.cam.ac.uk/archive/mjcg/HoareLogic/Lectures/AllLectures.pdf)
5
- Krzysztof and Ernst-Rudiger (2019) [Fifty Years of Hoare’s Logic](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Fifty+years+of+Hoare%E2%80%99s+logic+KR+Apt%2C+ER+Olderog&btnG=), Springer

- Josh Rushby (1995) [Formal Methods and Their Role in Digital Systems Validation for Airborne Systems](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Formal+Methods+and+Their+Role+in+Digital+Systems+Validation+for+Airborne+Systems&btnG=), NASA Contractor Report 4673 

- https://www.cs.cmu.edu/~lblum/flac/Presentations/cappiello_project_report.pdf
