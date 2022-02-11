---
title: Echo algorithm with reification of transition predicates
author: Burkhardt Renz
date: February 2022
---

## The echo algorithm with reification of transition predicates

The visualisation of the echo algorithm in `echo.md` does not show which
transition predicates is responsible for  a state transition. 
Using the _event reification idiom_ 
(see [An idiom to depict events](https://haslab.github.io/formal-software-design/modeling-tips/index.html#an-idiom-to-depict-events)) it is possible to improve the
visualisation.

To observe the effects of the new entities that represent transition
predicates in the _instance window_ of the Alloy Analyzer, you should
load _theme_ `echo_reif.thm`.

The following part of the specification is the same as in `echo.als`:

```alloy
open util/graph[Node]

let unchanged[r] { (r)' = (r) } 

enum Color {Red, Green}

abstract sig Node {
    neighbors: set Node,
    var parent: lone Node,
    var inbox: set Node,
    var color: Color
}	

one sig INode extends Node{}
sig PNode extends Node{}

fact {
    noSelfLoops[neighbors]
    undirected[neighbors]
    rootedAt[neighbors, INode]
}

pred init {
    no parent
    no inbox
    color = Node->Red
}

pred stutter {
    unchanged[parent]
    unchanged[inbox]
    unchanged[color]
}

pred broadcast[n, fp: Node] {
    all q: n.neighbors - fp | q.inbox' = q.inbox + n
    all u: Node - n.neighbors + fp | u.inbox' = u.inbox	
}

pred initiate {
    init
    broadcast[INode, INode]
    unchanged[parent]
    unchanged[color]
}

pred forward [n: Node, msg: Node] {
    (not n = INode) and no n.parent and msg in n.inbox
    parent' = parent + n->msg
    broadcast[n, msg]
    unchanged[color]
}

pred echo [n: Node] {
    (n = INode or one n.parent) and n.inbox = n.neighbors and n.color = Red
    unchanged[parent]
    inbox' = inbox ++ n.parent->(n.parent.inbox + n)
    color' = color ++ (n->Green)
}
```

The first step is the definition of an enumeration of atoms that
represent the transition predicates in the visualisation.

```alloy
enum TransPred { Initiate, Forward, Echo, Stutter }
```

In the second step we make sure that these singletons are coupled with
the state transitions using functions in Alloy. At first
glance the definition of the functions look self-referential: In the
definition of `initiate` e.g. `initiate` itself occurs.  However in one
case it is the _function_ and in the other case the _predicate_. In
Alloy functions and predicates can be overloaded.

```alloy
fun initiate: TransPred {
    { tp: Initiate | initiate }
}
fun forward: TransPred -> Node -> Node {
    { tp: Forward, n, msg: Node | forward[n, msg] }
}
fun echo: TransPred -> Node {
    { tp: Echo, n: Node | echo[n] }
}
fun stutter: TransPred { 
    { tp: Stutter | stutter}
}
fun transPreds: set TransPred {
    initiate + forward.Node.Node + echo.Node +  stutter
}
```

Since `transPreds` is the set of the names of the transition predicates,
we can use these names in the definition of the transition system:

```alloy
fact trans {
    init
    always some transPreds
}
```

Finally we define a function that gives us the green nodes of the graphs.
We can use this function to show the color in the visualisation.

```alloy
fun finished: set Node {
    { n: Node | n.color = Green }
}	
```

The predicates and assertions for the verification remain unchanged.

```alloy
pred fairness {
    all n, msg: Node {
        (eventually always init) 
            implies (always eventually initiate)
        (eventually always (not n = INode and no n.parent and msg in n.inbox))
            implies (always eventually forward[n, msg])
        (eventually always ((n = INode or one n.parent) and n.inbox = n.neighbors and n.color = Red))
            implies (always eventually echo[n])
    }
}

run examples {}
						
run withProgress {fairness} for exactly 4 Node

assert EchoComesBack {
    fairness implies eventually INode.color = Green
}
check EchoComesBack

assert SpanningTree {
    (eventually INode.color = Green) 
    implies (eventually (tree[~parent] and rootedAt[~parent, INode]))
}
check SpanningTree
```

To get a nice visualisation you have to customize the _theme_. An
example how to do this is found in `echo_reif.thm`.

