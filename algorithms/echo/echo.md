---
title: Echo algorithm
author: Burkhardt Renz
date: February 2022
---
## The echo algorithm

The echo algorithm constructs a
spanning tree in a connected undirected graph. We consider the nodes of
the graph as agents. An agent has a unique _id_. It can send
_messages_ to its neighbors. The nodes cooperate by the following
_protocol_ to construct the tree,
see e.g. Chap. 4.3 in: Wan Fokkik _Distributed algorithms: an intuitive approach_, 
MIT Press, 2018.

- One of the nodes is chosen at random to begin the protocol.
  This the _initiator_. The other nodes are called
  _participants_. The initiator will end up being the root of the
  spanning tree. It initiates the protocol by sending its own
  _id_ to each neighbor.
- Each participant checks its inbox and, if not empty, takes
  some message from it. If the participant has not yet marked a
  parent node, the id in this message becomes its parent and it
  sends its own id to each neighbor except its parent.
- When a participant has received messages from each neighbor,
  it sends its id to its parent.
- Finally, when the initiator has received an echo from each
  neighbor, the relation _parent_ of pairs of nodes constructed in the
  course of the message exchange forms a spanning tree of the graph with the
  initiator as the root.

Specifications of properties of graphs can be found in module
`util/graph`:

```alloy
open util/graph[Node]
```

Transitions predicates comprise
1. the condition the current state must meet for the transition to occur, the _guard_,
2. the changes i.e. for an item `x` its value `x'` in the next state, and
3. the _frame condition_, i.e. what remains unchanged.

The following macro helps to specify frame conditions. It's provided by the
[macro mechanism of Alloy](http://alloytools.org/quickguide/macro.html).

```alloy
let unchanged[r] { (r)' = (r) } 
```

To control the state of each node, we provide colors. In the initial
state all nodes are `Red`. A node that has send its echo back to its parent
changes his color to `Green`. The following enumeration defines our two colors:

```alloy
enum Color {Red, Green}
```

The graph has nodes and edges to adjacent `neighbors`. This is the static structure 
remaining fixed for the run of the algorithm. Nodes send messages to the `inbox`
of their neighbors. The content of the messages are ids of the sending node for which we use
the `Node` itself. The spanning tree is formed by building the relation `parent`.

In this variant of the specification we partition the set of nodes into the singleton
`INode`, the initiator and the `PNode`s, the participants.

```alloy
abstract sig Node {
  neighbors: set Node,
  var parent: lone Node,
  var inbox: set Node,
  var color: Color
}	

one sig INode extends Node{}
sig PNode extends Node{}
```

The following fact specifies that our graph is undirected, connected and has no self loops.

```alloy
fact {
  noSelfLoops[neighbors]
  undirected[neighbors]
  rootedAt[neighbors, INode]
}
```

The predicate `init` specifies the initial state of the algorithm, i.e. the relation
`parent` is empty, no messages has been sent yet, and all nodes are `Red`.

```alloy
pred init {
  no parent
  no inbox
  color = Node->Red
}
```

We provide a _stutter step_ that leaves everything unchanged:

```alloy
pred stutter {
  unchanged[parent]
  unchanged[inbox]
  unchanged[color]
}
```

The predicate `broadcast` specifies that node `n` sends itself to each
of its neighbors except its future parent `fp`.

```alloy
pred broadcast[n, fp: Node] {
  all q: n.neighbors - fp | q.inbox' = q.inbox + n
  all u: Node - n.neighbors + fp | u.inbox' = u.inbox	
}
```

The first step of the algorithm: the initiator braodcasts itself to each of its
neighbors:

```alloy
pred initiate {
  init
  broadcast[INode, INode]
  unchanged[parent]
  unchanged[color]
}
```

If a participant receives its first message it marks the sender as its
parent and sends itself to each of its neighbors.
If a node got messages from each of its neighbors, i.e. its `inbox` equals
the set of its `neighbors`, it echos back to its parent.

```alloy
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

The specification of the transition system: beginnend in the initial state always 
some of the transition predicates have to be fulfilled i.e. a step is performed.

```alloy
fact trans {
  init
  always { 
    initiate or
    some n, msg: Node | forward[n, msg] or
    some n: Node | echo[n] or
    stutter 
  }
}
```

The predicate fairness guarantees that if the guard of a transition predicate becomes true
then eventually the transition happens; 
see [Verifying the expected properties of the protocol](https://haslab.github.io/formal-software-design/protocol-design/index.html#verifying-the-expected-properties-of-the-protocol)
by Julien Brunel, David Chemouil, Alcino Cunha, Nuno Macedo.

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
```

The first run `examples` gives graphs with up to three nodes and execution paths with
a lot of stutter steps, but other transitions as well. 

The second run `withProgress` uses the fairness condition and the Alloy Analyzer gives the
shortest execution path for graphs with 4 nodes first. Button `New Config` in the instance 
window shows a new static configuration, i.e. some other graph, and button `New Trace` shows 
another execution path.

```alloy
run examples {}

run withProgress {fairness} for exactly 4 Node
```

Having specified the echo algorithm we are interested in two questions:
1. Does the echo really come back to the initiator?
2. If so, do we have found a spanning tree of the graph?

To verify assumptions in Alloy we formulate the property to be checked as an assertion.
The command `check` starts the verification and will output whether the analyzer did
find a counterexample.

```alloy
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

Note: the verification is done per default for graphs up to 3 nodes and up to
10 steps of the execution paths.

The number of nodes can be increased, e.g.
`check EchoComesBack for 4 Node`, and the number of steps too, e.g.
`check EchoComesBack for 5 Node, 16 steps`. In both cases the Alloy Analyzer
performs _bounded model checking_. 

It is also possible to check with _unbounded model checking_, 
taking into consideration an arbitrary number of transitions, e.g.
`check EchoComesBack for 1.. steps`. For this check the `Solver` in the menu
`Options` must be set to `Electrod/nuSMV` or `Electrod/nuXmv`.
