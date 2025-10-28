# Hoare Logic

"The most  important property of a program is whether it accomplishes the intentions of its user. If the intentions can be described rigorously by making assertions about the values of variables at the end of the execution of the program, then the techniques described in this paper may be used to prove the correcteness of the program." 

Hoare. [An axiomatic basis for computer programming](http://extras.springer.com/2002/978-3-642-63970-8/DVD3/rom/pdf/Hoare_hist.pdf). Communications of the ACM. 12 (10): 576–580, 1969.

## Introduction

In Programming Languages there is an important circle of ideas including [Hoare logic](https://en.wikipedia.org/wiki/Hoare_logic) and Dijkstra's [predicate transformer semantics](https://en.wikipedia.org/wiki/Predicate_transformer_semantics), Kozen's [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra) and Pratt's [Dynamic logic](https://en.wikipedia.org/wiki/Dynamic_logic_(modal_logic)), O'Hearn and Reynolds's [Separation logic](https://en.wikipedia.org/wiki/Separation_logic) and many more methods, techniques, tools, etc.

This line of research grew out of the methodology of **structured programming**, which is something that every programmer learns today right from the start, but was a novel concept around 1970. I postpone a discussion of this to the conclusions.

Here, we will just give some of the basic ideas and illustrate them with an important technique of proving the correctness of while programs. 

Therefore, an alternative title would be

$$
\textbf{Correctness of While Programs}
$$

The technique is based on a refinement of the method of invariants. Thus, another possible title is

$$
\textbf{Invariants for Program Correctness}
$$

These ideas have various ramifications in programming and software engineering.

- Preconditions, Postconditions, and Invariants are useful at all levels of programming and software development: Every function, procedure, method, component, [API](https://en.wikipedia.org/wiki/Application_programming_interface), etc has

  - preconditions that are required from the user to guarantee correct performance
  - postconsitions that are guarantees to the user
  - invariants that are guaranteed to hold after execution if they held before execution

- [Design by contract](https://en.wikipedia.org/wiki/Design_by_contract) is a software engineering method build on these ideas.

- Check out the [list of programming languages](https://en.wikipedia.org/wiki/Design_by_contract#Language_support) supporting these ideas.
   
- Assume/guarantee or rely/guarantee is an important technique in the development of concurrent programs

**Table of Contents**:

- [Summary of the Rules of Hoare Logic](./9-hoare-logic.md)
- Introductory Example
- Preconditions and Postconditions
- Program Variables vs Mathematical Variables
- The Rules in Detail

## Example

Consider the following program, see also [HL-example-1.dfy](../src/dafny/HL-example-1.dfy).
```
while (x != 0) do z:=z+y;  x:= x-1 done
```
Here are some questions we may ask.
- Does this program  terminate? 
- What does the program calculate?
- Does this program calculate `x*y` in the variable `z`?

It will  depend on the value of `x` and `z` before executing the program. 

This program will terminate and yield `z = x*y`  at the end if `x` is non-negative and  `z==0` at the start.

**Activity:** Find an invariant for the while loop.

Answer. [^invariantwhile2][^invariantwhile]

[^invariantwhile]: Let us make a table of an execution. We assume here that the program variables are initialised as follows: `x` is 100, `y` is 2 and `z` is 0. `t` counts how often the body of the loop was executed. (We will later see how to generalize to aribtrary input `x,y,z`.)

	|`t`|`x`|`y`|`z`|
	|:---:|:---:|:---:|:---:|
	|0|100|2|0|
	|1|99|2|2|
	|2|98|2|4|
	|...|...|...|...|
	|99|1|2|198|
	|100|0|2|200|
	
	How can we be sure that we found the correct numbers to fill in after the dots? The answer is that these numbers satisfy invariants, namely
	
		t + x = 100
		z = t * y
	
	With a bit of algebra we can now find an invariant that only consists of program variables
	
		z = (100 - x) * y
		
	This is an invariant. We will see below how to make this independent of particular values such as `100`.

[^invariantwhile2]:
	Let us think about it.
	
	Each time the program goes through the loop, `x` will be decremented. How often does it happen? This again depends on `x`.
	
	***The aim is to find a reasoning principle that frees us from tracking how often we go through a loop.***
	
	Here it is actually easy to see that we go `x` times through the loop (if `x` is not negative). But in more complicated examples there may not be a formula that allows us to caclulate the number of times we go through a loop from the available data. 
	
	(This follows from the halting problem.)
	
	So we would like to decouple the question "how often do we go through the loop?" (termination) from the question of correctness ... which is then called ***partial correctness***, or more precisely, correctness under the assumption of termination.
	
	Does this sound impossible?
	
	Remember our lecture about [invariants](https://hackmd.io/@alexhkurz/BkMoUhXvD)?
	
	Can you spot an invariant? A property that remains unchanged while going throuth the loop?

    Hint: Invent a notation that allows to distinguish the value of a program variable before and after the execution of some code. (There are different ways of doing this.)

    Can you conclude from the invariant what the result of the computation is? 

    After answering the questions yourself, you can check with my solutions below.


## Preconditions ... Postconditions ...

As the example shows part of the difficulty lies in having a reliable notation that allows us to track change through a program and making statements (such as `z == x*y` ) about its properties.

The first important idea is that we want express that certain assumptions are satisfied before executing the program (preconditions)  and properties that we then know after the execution of the program (postconditions)

If $\mathtt S$ is a program ("S" as in "Sequence of Statements") then we write

$$
\{P\}\; \mathtt S\;\{Q\}
$$

A predicate that holds before the execution of the program is  called  a ***precondition***  and a predicate that holds after  a ***postcondition***. If the precondition is met before execution,  the program  establishes the postcondition if it terminates. 


For example, we can write

$$
\color{blue}{\{\mathtt x\ge 0 \wedge \mathtt z=0 \}} \; 
\mathtt{while \ (x \not = 0 ) \  do \ z:=z+y;  x:= x-1  \ done}  \;
$$

to express what we said above, namely that the we want to execute the program above only in case $\mathtt x\ge 0$ and $\mathtt z=0$.

**Notation:** We use mathematical notation in pre and postconditions. For example, we write "=" in $\{\mathtt x\ge 0 \wedge \mathtt z=0 \}$ to mean equality, not assignment. Program variables are typeset in typewriter font as in $\mathtt{x,y,z}$.


What should be the post condition?

**Exercise:** A first idea for a postcondition is  

$$
{\{\mathtt x\ge 0 \wedge \mathtt z=0 \}} \; 
\mathtt{while \ (x \not = 0 ) \  do \ z:=z+y;  x:= x-1  \ done}  \;\color{blue}{\{\mathtt{z=x*y}\}}.
$$

What do you think about this? Does it look right? Consider how $\mathtt x$ changes through the computation.

Answer.[^looksright]

## Program Variables vs Mathematical Variables

Our difficulty in finding the correct postcondition can be remedied using the following trick. 

While we allow program variables to change during the execution of a program $\mathtt S$ in

$$
\{P\}\; \mathtt S\;\{Q\}
$$

we also allow, not in programs, but in the properties $P$ and $Q$, mathematical variables. This is not surprising, once we had the idea, since we are already using mathematical notation such as $>,=,\wedge$ etc. And, as in mathematics, there is no assigment-operation that would allow us to change the value of a mathematical variable. So when we write

$$
\{\ldots n\ldots \}\; \mathtt S\;\{\ldots n\ldots\}
$$

the mathematical variable $n$ stands for the same value before the execution and after the execution of $\mathtt S$.

**Question:** Recalling that $\mathtt y$ is a program variable and that $n$ is a mathematical variable: What does  

$$
\{\mathtt y = n\}\; \mathtt S\;\{\mathtt y = n\}
$$

express about $\mathtt S$? Why does it not express that $\mathtt y$ cannot change during the execution of $S$?

**Exercise:** Do the following pre and postconditions

$$
\color{blue}{\{\mathtt z=0 \ \wedge\  \mathtt x =n \}} \; 
\mathtt{while \ (x \not = 0 ) \  do \ z:=z+y;  x:= x-1  \ done}  \;\color{blue}{\{\mathtt{z=\mathit{n}*y}\}}
$$

capture our informal discusions above?

**Exercise:** How do you have to change the post and precondition if you  want to drop the precondition $\color{blue}{\{\mathtt z=0\}}$ and make a statement that holds for arbitrary initial values of $\mathtt z$?

See the footnote for a solution.[^invariantznot0]

## The Rules in Detail

Hoare logic (also known as Floyd-Hoare logic) is a formal system developed by the British computer scientist C. A. R. Hoare, and subsequently refined by Hoare and other researchers. The purpose of the system is to provide a set of logical rules in order to reason about the correctness of computer programs with the rigour of mathematical logic and, therefore, the possibility of delegating such reasoning to a compiler or other verification software tools.

We will describe Hoare Logic for a minimal programming language containg only assignments, conditionals and while-loops. In addition to the rules for the simple language in  Hoare's original paper, rules for other language constructs have been developed since then by Hoare and many other researchers. There are rules for concurrency, procedures, jumps, and pointers and much more. For example, [Separation logic](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=%22O%27Hearn%22+%22separation+logic%22+%22facebook%22&btnG=) is used by Facebook in verification tools.

### While-loop

Let us go back to our leading example        

        while (x != 0 ) do z:=z+y;  x:= x-1 done
 

So let us try to formalise this using pre and postcondition, or, as on says, ***Hoare triples***.

**Exercise:** Prove the Hoare triple

$$
\color{blue}{\{\mathtt z = (n-\mathtt x)\cdot\mathtt y\}} \; 
\mathtt{while \ (x \not = 0 ) \  do \ z:=z+y;  x:= x-1  \ done}  \;\color{blue}{\{\mathtt z = (n-\mathtt x)\cdot\mathtt y\}}.
$$

**Question:** Why is  $\color{blue}{\{\mathtt z = (n-\mathtt x)\cdot\mathtt y\}}$ called a loop invariant?

**Activity:** Recall that the intended meaning of the while loop is to compute $\mathtt z = n\cdot\mathtt y$ which we write in form of a Hoare triple as

$$
\color{blue}{\{\mathtt z = 0 \ \wedge \ \mathtt x=n\}} \; 
\mathtt{while \ (x \not = 0 ) \  do \ z:=z+y;  x:= x-1  \ done}  \;\color{blue}{\{\mathtt z = n\cdot\mathtt y\}}.
$$

What reasoning steps are needed to obtain this Hoare triple from the one of the previous exercise?

To carefully explain the answer to this question takes a little effort. So let us first give a short answer:

            Show that the precondition implies the invariant and
                that the invariant implies the postcondition

First, to show that the precondition implies the invariant, is to show that

$$
\mathtt z = 0 \ \wedge \ \mathtt x=n \ \Longrightarrow \ \mathtt z = (n-\mathtt x)\cdot\mathtt y
$$

This is easy: Just replace in the conclusion $\mathtt z$ by 0 and $\mathtt x$ by $n$ and you find $0=0$, which is indeed true. [^equals]

Second, to show that the invariant implies the postcondition, is to show that 

$$
\mathtt z = (n-\mathtt x)\cdot\mathtt y \ \Longrightarrow \ \mathtt z = n\cdot\mathtt y
$$

and if you go back to the program you see that this is possible since we know that 

$$
\mathtt x=0
$$

is a postcondition that must always be true after termination of the while-loop.

**Exercise:** Explain why. [^xis0]

So summarise in symbolic notation what we have done so far, we started out with a rule stating that $I$ is an invariant

$$
\frac{\color{blue}{\{I \}}\ \mathtt S\ \color{blue}{\{I\}}}{\color{blue}{\{I \}}\ \mathtt{while}\ B\ \mathtt{do}\ S\ \mathtt{done} \color{blue}{\{ I\}}}
$$

and then modified it to take into account that after termination of the loop we also know "not $B$", that is, 

$$
\frac{\{I \}\ \mathtt S\ \{I\}}{\{I \}\ \mathtt{while}\ B\ \mathtt{do}\ S\ \mathtt{done} \{ \color{blue}{\neg B \,\wedge\,}I\}}
$$

And then we used this rule by showing that the precondition implies $I$ and that $\neg B\wedge I$ implies the postcondition.

This last step, which is important to bring into the picture the pre and postconditions that are actually needed for our (partial) correctness assertion, can also be formalised as a rule as follows.

$$
\color{red}{\frac{P'\Rightarrow P \quad\{P \}\ \mathtt S\ \{Q\} \quad Q\Rightarrow Q'}{\{P' \}\ \mathtt S \  \{Q'\}}}
$$

This rule is our first official rule of Hoare logic. We will see more later and they are all highlighted in red for reference.

**Question:** Why does this reasoning not require the precondition $\color{blue}{\{x\ge 0\}}$? For what exactly is this precondition needed? 

This question has an important answer, so do look up the footnote after thinking about it yourself. [^xge0]


Before we formulate the official rule for how to reason with a loop invariant, we need one more adjustment. 

**Question:** Given the loop 

$$
\mathtt{while \  (x<10) \  do \ x:= x+1  \ done}
$$

what could we use as loop invariant?

It is easy to write down some irrelevant invariants, but which invariant would help us to prove the postcondition $\color{blue}{\{x=10\}}$?

A little thought shows that while an $I$ such that

$$
\color{blue}{\{I\}} \; 
\mathtt S  \;\color{blue}{\{I\}}
$$

is obviously an invariant for `while B do S done`  , this is more than we need. After all, the invariant only needs to hold if we enter the loop, so it is enough for a ***loop invariant*** $I$ to satisfy

$$
\color{blue}{\{I \ \wedge \ \mathtt B\}} \; 
\mathtt{\mathtt S}  \;\color{blue}{\{I\}}. 
$$

To illustrate this idea think about the following.

**Exercise:** Consider again

$$
\mathtt{while \  (x<10) \  do \ x:= x+1  \ done}
$$

and find a loop invariant. Can you conclude from that invariant the postcondition $\color{blue}{\{x = 10\}}$?

For a solution see the footnote.[^invariantx10]

We are now ready to state the Hoare rule for a while loop.

The ***while rule*** is as follows. 

$$
\color{red}{\frac{\{I \wedge \mathtt B \}\ \mathtt S\ \{I\}}{\{I \}\ \mathtt{while}\ B\ \mathtt{do}\ S\ \mathtt{done} \{\neg B \wedge I\}}}
$$
     
Here $I$ is the ***loop invariant***. 

### Making Hoare Logic Compositional

From a practical programming point of view we already learned some important lessons from studying Hoare logic. 

For example, we have seen 

- how to separate termination from partial correctness and 
- how to prove partial correctness of loops using invariants.

But there is more to Hoare logic. 

We have seen two examples of symbolic rules (see the red rules above) that formalise the way we reasoned about our example programs.

Two big ideas of programming languages are now the following.

- If we can formalise enough rules needed to reason about programs, then we can build software tools that do reason for us automatically.

- There is hope to find all rules as long as we proceed in a compositional way, that is, "by induction" on the rules that define the programming language.

In our case, we have a programming language that has assignments, sequential composition, conditionals, and while-loops.

So far we have only seen the rule for while-loops.

In what follows, we will look at rules for the other programming constructions.

### Sequential Composition

The rule of composition applies to sequentially-executed programs
$\mathtt S$ and $\mathtt T$, where $\mathtt S$ executes prior to $\mathtt T$ and is written 

$$
\mathtt S;\mathtt T
$$

For example, consider the following two instances of the assignment axiom:

$$ 
\{ x + 1 = 43\} \ y:=x + 1\ \{y =43 \}
$$

and

$$ 
\{ y = 43\} \ z:=y\ \{z =43 \}. 
$$

By putting these together, we get:

$$ 
\{ x + 1 = 43\} \ y:=x + 1; z:= y\ \{z =43 \}
$$

The **rule for composition** of programs is as follows.

$$
\color{red}{
\frac{\{P\}\ \mathtt S\ \{Q\} \quad\quad \{Q\}\ \mathtt T\ \{R\}}
{\{P\}\ \mathtt S ; \mathtt T\ \{R\}}
}
$$

### Assignment

The assignment instruction is written as  

$$
\mathtt x:=E
$$ 

and it assigns the value $E$ to the variable $\mathtt x$. For example, we consider a   program consisting of only one instruction 

$$
\mathtt x:= \mathtt y-1
$$

which assigns $\mathtt y-1$ to the variable $\mathtt x$. 

Now, suppose we know that $y$ has value $10$ before the execution of this instruction. Then, we know that after its execution the value of $x$ will be $9$. This is expressed in Hoare Logic as follows. 

$$
\color{blue}{\{\mathtt y = 10 \}} 
\ \ \ \mathtt x:= \mathtt y-1  \ \ \ 
\color{blue}{\{\mathtt x=9  \}}
$$

The predicate $\mathtt y=10$  is the precondition and the predicate $\mathtt x=9$ is the postcondition.

Our predicates could involve more variables. For instance,

$$
\color{blue}{\{\mathtt x>0 \wedge \mathtt x\leq 3 \wedge \mathtt y = 10 \}}
 \ \ \ \mathtt x:= \mathtt y-1  \ \  
\color{blue}{\{\mathtt x=9 \wedge \mathtt y=10 \}} $$

The ***assignment axiom*** in Hoare Logic  states that after the assignment any predicate holds for the variable that was previously true for the right-hand side of the assignment:

$$ 
\color{red}{\{P [\mathtt{exp}\,/\,\mathtt x]  \}
\ \ \ \mathtt x:=\mathtt{exp} \ \ \ 
\{P \}} 
$$

In other words, the post-condition  $P$ holds after the execution of the  assignment $\mathtt x:=E$ provided that  $P [\mathtt{exp}\,/\,\mathtt x]$ holds prior to it.


Suppose now that the program is  the statement 

$$
y:=x + 1
$$ 

and we want that $\mathtt y = 43$ after its execution. What are the possible values for $\mathtt x$ at the beginning of the execution of our program?

Using the  assignment axiom we get that

$$ 
\color{blue}{\{\mathtt x+1 = 43\}}
\ \ \ \mathtt y:=\mathtt x + 1\ \ \ 
\color{blue}{\{ \mathtt y = 43 \}}
$$

The precondition $\mathtt x+1 = 43$  can be simplified to $\mathtt x = 42$. Hence,

$$ 
\color{blue}{\{\mathtt x = 42 \}}
\ \ \ \mathtt y:=\mathtt x + 1 \ \ \ 
\color{blue}{\{ \mathtt y = 43 \}}
$$

Suppose now that our program is the statement 

$$
\mathtt x := \mathtt x + 1
$$

and we want that $\mathtt x \leq N$ after its execution. Using the assignment axiom we get 

$$
\color{blue}{\{\mathtt x + 1 \leq N \}}
\ \ \ \mathtt x := \mathtt x + 1\ \ \ 
\color{blue}{\{\mathtt x \leq N\}} 
$$

Hence, 

$$
\color{blue}{\{\mathtt x <  N \}}
\ \ \ \mathtt x := \mathtt x + 1\ \ \ 
\color{blue}{\{\mathtt x \leq N\}} 
$$

**Remark:** The assignment axiom proposed by Hoare does not apply when more than one name can refer to the same stored value. For example,

$$
\color{blue}{\{ y = 3\}} 
\ \ \ x := 2 \ \ \ 
\color{blue}{\{y = 3 \}}
$$

The above statement is not  true if $x$  and $y$ refer to the same variable, because no precondition can cause y to be 3 after x is set to 2.


### Exercise

Use the red rules above to show

$$
\color{blue}{\{true\}}\ \mathtt{while \  (x<10) \  do \ x:= x+1  \ done}\color{blue}{\{\mathtt x=10\}}
$$

and

$$
\color{blue}{\{\mathtt z = m \ \wedge \ \mathtt x=n\}} \; 
\mathtt{while \ (x \not = 0 ) \  do \ z:=z+y;  x:= x-1  \ done}  \;\color{blue}{\{\mathtt z = m + n\cdot\mathtt y\}}.
$$

**Remark:** In the second example you need to strengthen the invariant so that it expresses that $y$ does not change in the loop.

### If-then-else


Consider the following program.

$$
\mathtt{if}\ (y>0) \ \mathtt{then}\  x: = y \ \mathtt{else}\ x:= -y 
 \ \mathtt{endif}
$$
 
We want to show that the above program  calculates the absolute value of $y$,
denoted by $| y |$, i.e.

$$
\{true\} \mathtt{if}\ (y>0) \ \mathtt{then}\  x: = y \ \mathtt{else}\ x:= -y 
 \ \mathtt{endif} \{x = |y|\} 
$$
 
If $y>0$ then it is clear that $x=y$. If not, then $y \leq 0$
and then $x = - y = |y |$.

Consider the following program.

$$
\mathtt{if}\ (x \geq y) \ \mathtt{then}\  z:= x  \ \mathtt{else}\ z
:= y 
 \ \mathtt{endif}
$$

We want to show that the above program calculates the maximum of the
two values $x$ and $y$, i.e.
 
$$
\{true\} \mathtt{if}\ (x \geq y) \ \mathtt{then}\  z:= x  \ \mathtt{else}\ z
:= y 
 \ \mathtt{endif} \{ z = max(x,y) \}
$$

If $x \geq y$ then $x$ is the maximum and then $z = x = max(x,y)$. If not, then $x < y$ and $z = y = max(x,y)$.  


The  **conditional rule** is as follows.

$$
\color{red}{
\frac{\{B \wedge P\}\ \mathtt S\ \{Q\} \quad\quad \{\neg B \wedge P \}\ \mathtt T\ \{Q\} }
{\{P\}\ \mathtt{if}\ B\ \mathtt{then}\ \mathtt S\ \mathtt{else}\ \mathtt T\ \mathtt{endif}\ \{Q\}}
}
$$

This concludes our explanations of Hoare logic. 

## Homework

Apply the method of analysis from these notes to  
```
while (x!=0) do z:=z*y;  x:= x-1 done
```
What is the invariant? Indicate the reasoning steps in which you  apply the rules of Hoare logic.

This exercise is very similar to what we have done above (essentially, we use now `*` instead of `+`). If you want to do something more challenging, you can instead also do the next exercise.

## Further Exercises

Apply the method of analysis to  
```
 while (i<=n) do t:=t+i; i:=i+1 done
```
[Hint: [Triangular numbers](https://en.wikipedia.org/wiki/Triangular_number).]
	
See also [Exercises: Program Verification, Hoare Logic, Loop Invariants](https://hackmd.io/@alexhkurz/rkhVZNzjH).

## Summary and Outlook

I will first summarise some of the lessons that we learned from studying Hoare logic, lessons that are relevant to programmers and software engineers far beyond the particularities of this specific approach to program correctness.

Then I will briefely look at the history of ideas around "structured programming" which gave rise to Hoare logic and other approaches to program verification.

### Hoare Logic

... the following summary is currently just a collection of random notes ... 

- The following habits can improve the practice of programming
  
  - What are the pre and postconditions of the code I write?
  - Should I test them explicitely? Raise an exception if they are violated? Describe them explicitely in comments? Make users of my code aware of them?
  - Using software tools that support pre and postcondition in my code.
  - Thinking of loop-invariants before implementing my loops.
  - Working backwards from postconditions to preconditions: Given that I want to guarantee a postcondition, what are the preconditions and what is the code needed for this? [^fromposttopre]

- These programming techniques have formal counterparts, some of which are
  
  - Hoare triples
  - loop invariants
  - rules of Hoare logic

- Hoare logic is compositional
  We have seen that each programming construct corresponds to a rule in Hoare logic for a simple programming language consisting only of assignments, conditionals, sequential composition and while-loops. In principle there is no reason why this approach could not be extended to cover any construct available in any programming language. Not surprisingly, the literature on this topic is vast. For us here, the upshot is that the rules of Hoare logic are compositional in the definition of the syntax of the language.

- Hoare logic is a formal system 
    While this lecture emphasised how to use invariants to reason about the correctness of while loops, we also hinted at how this reasoning can be formalised.

- Hoare logic can be implemented by software tools that support program design and development
This is a consequence of the previous item. Formal systems can be implemented and then turned into tools.

- Hoare logic as many ramifications for various special purpose situations such as concurrency, memory management, etc

### Structured Programming

(this section is being written as an after-thought and was not part of the semester)

Early programming close to the machine relies on jumps as a basic mechanism to control flow. Accordingly, early higher level languages such as Fortran had a corresponding $\texttt{goto}$ statement. Goto's lend themselves to the writing of "unstructured" code that is difficult to read and debug, but was considered a necessary ingredient. 

In 1966, the article [Flow diagrams, turing machines and languages with only two formation rules](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Flow+diagrams%2C+turing+machines+and+languages+with+only+two+formation+rules&btnG=) by Boehm and  showed that jumps (gotos) are not needed and any program can be written with just three controle structures: sequential composition, conditional and iteration. This was an important result at the time as it suggested that the complex control structures (typically based on gotos, later fiving rise to so-called spaghetti code) that plagued programming at the time were not necessary.

## Historical References

- Reynolds: [The Craft of Programming](https://kilthub.cmu.edu/ndownloader/files/12102656). 1981.

This is one of the first textbooks teaching verification of programs. I find it still interesting today ...

- ...

## Further Reading

### Formal Verification

We have seen that the rules of Hoare logic can be formalised in symbolic notation. It should therefore should be possible to implement software engineering tools that automate reasoning about programs.

To get a taste of how verification is done in real world programming applications, have a look at the blogs by David Crocker about *Verifying loops in C and C++*, [part 1](https://critical.eschertech.com/2010/03/22/verifying-loops-in-c/) and [part 2](https://critical.eschertech.com/2010/03/29/verifying-loops-part-2/) and [part 3](https://critical.eschertech.com/2010/03/31/verifying-loops-proving-termination/). There is also a very short [introduction to software verification](https://critical.eschertech.com/about/).

[^invariant]: What about $\mathtt z = (n-\mathtt x)\cdot\mathtt y$ where $n$ is the value of $\mathtt x$ before entering the loop?

    The first trick here is to use two different variables: program variables $\mathtt{x,y,z}$ that can change during program execution and mathematical variables $n$ that cannot.

    The second trick is that we can conclude the value of $\mathtt z$ after the loop finishes by taking the conjunction of the loop-invariant $\mathtt z = (n-\mathtt x)*\mathtt y$ with the negation $\mathtt x=0$ of the condition `(x != 0)` that controls the entry into the loop. After all, we can only finish the loop if we are not allowed entry. 
    
    But now see what happens. This conjunction implies $\mathtt z= n\cdot \mathtt y$, which is what we wanted, namely the value of $\mathtt z$ after $n$ eecutions of the loop (remember that $n$ is the value of $\mathtt x$ before the loop was entered).


[^looksright]: The problem with $\color{blue}{\{\mathtt{z=x*y}\}}$ is that it only gives us what we want if we take for $\mathtt x$ the value of $\mathtt x$ *before* the computation and for $\mathtt z$ the value of $\mathtt z$ *after* the computation. On the other hand, if we take for both variables their values after the computation, as we should (why?), the condition $\color{blue}{\{\mathtt{z=x*y}\}}$ is false (for almost all initial values of the variables).

[^equals]: The rule of logic that allows us to replace equals by equals is often called the "congruence rule" of equational reasoning. 


[^xis0]: The condition $\mathtt B$ that forces to execute the loop is in our example `x!=0`, that is, $\neg(x=0)$. Therefore $\neg\mathtt B$ is $\neg\neg(x=0)$, which is $x=0$.

[^xge0]: Our first observation was that the precondition $\{x\ge 0\}$ is needed for correctness. Why is it not needed in the proof of the Hoare triple? The reason is that Hoare triples only concern what is called **partial correctness**, that is, correctness under the assumption of termination. Indeed, $\{x\ge 0\}$ is only needed in our example to argue for termination. 

[^invariantznot0]: $$\color{blue}{\{\mathtt x=n \ \wedge\  \mathtt z=m \ \wedge\  \mathtt y =k \}} \; 
\mathtt{while \ (x \not = 0 ) \  do \ z:=z+y;  x:= x-1  \ done}  \;\color{blue}{\{\mathtt{z=n+m*k}\}}. $$

[^invariantx10]: $\color{blue}{x\le 10}$ is a loop invariant.

[^fromposttopre]: Note that this goes in the opposite direction of our usual thinking about code, which is operational and proceeds from an initial state and works forward from there.

