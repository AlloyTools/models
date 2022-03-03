---
title: Echo algorithm - variant
author: Burkhardt Renz
date: February 2022
---
## The echo algorithm - variant

So far we specified graphs with a dedicated node that initiates
the echo algorithm. In this variant of the specificiation we let the
Alloy model finder choose the initiating node.

```alloy
open util/graph[Node]

let unchanged[r] { (r)' = (r) } 

enum Color {Red, Green}

sig Node {
    neighbors: set Node,
    var parent: lone Node,
    var inbox: set Node,
    var color: Color
}	
```

Since we do not have a dedicated initiator, we have to ensure the
connectivity of the graph by the predicate `stronglyConnected` from
`util/graph`.

```alloy
fact {
    noSelfLoops[neighbors]
    undirected[neighbors]
    stronglyConnected[neighbors]
}
```

The definition of the transition predicates has a small modification:
The initiating node marks itself as its parent.

```alloy
pred stutter {
    unchanged[parent]
    unchanged[inbox]
    unchanged[color]
}

pred broadcast[n, fp: Node] {
    all q: n.neighbors - fp | q.inbox' = q.inbox + n
    all u: Node - n.neighbors + fp | u.inbox' = u.inbox	
}

pred initiate[n: Node] {
    parent = n -> n
    no inbox
    color = Node -> Red
    unchanged[parent]
    #Node = 1 implies {
        color' = n -> Green 
        unchanged[inbox]
    } else {
        broadcast[n, n]
        unchanged[color]
    }
}

pred forward [n: Node, msg: Node] {
    no n.parent and msg in n.inbox
    parent' = parent + n->msg
    broadcast[n, msg]
    unchanged[color]
}

pred echo [n: Node] {
    one n.parent and n.inbox = n.neighbors and n.color = Red
    unchanged[parent]
    inbox' = inbox ++ n.parent->(n.parent.inbox + n)
    color' = color ++ (n->Green)
}
```

In the definition of the transition system, we perfrom as first step
`initiate` for some node choosen by the model finder. Thus the other
possible steps are only possible in the next step `after` the first
one:

```alloy
fact trans {
    some n: Node | initiate[n]
    after always { 
        some n, msg: Node | forward[n, msg] or
        some n: Node | echo[n] or
        stutter 
    }
}

pred fairness {
    all n, msg: Node {
        (eventually always (no n.parent and msg in n.inbox))
            implies (always eventually forward[n, msg])
        (eventually always (one n.parent and n.inbox = n.neighbors and n.color = Red))
            implies (always eventually echo[n])
    }
}
								
run examples {}

run makeProgress {fairness} 

assert echoComesBack {
    fairness implies (eventually all n:Node | n.color = Green)
}
check echoComesBack
```

Since we defined a self loop at  the initiating node, we must modify
the check whether we got a spanning tree as result of the algorithm:
```alloy
assert SpanningTree {
    #{ n: Node | n = n.parent} = 1
    always (color = Node->Green implies tree[~(parent-iden)])
}

check SpanningTree
```
