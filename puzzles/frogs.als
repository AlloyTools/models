/*

A model of the jumping frogs puzzle. 

David Faitelson

davidf@afeka.ac.il

January 2026

You can see the puzzle at this website:

https://data.bangtech.com/algorithm/switch_frogs_to_the_opposite_side.htm#google_vignette

The model solves the puzzle either by providing a counter example to the 
assertion that it is impossible to reach the desired final state, or by asking
for an example that reaches the desirable state.

Tip: to improve the visualization, color the green stones with green, and the brown
stones with red.

*/

abstract sig Stone {
	adj : lone Stone // which stone is adjacent to which stone
}

one sig S1,S2,S3,S4,S5,S6,S7 extends Stone {}

var sig Green in Stone {} // stones occupied by green frogs

var sig Brown in Stone {} // stones occoupied by brown frogs

fact {

	// From left to right, S1 is the leftmost stone, S7 is the rightmost.

	adj = S1 -> S2 + S2 -> S3 + S3 -> S4 + S4 -> S5 + S5 -> S6 + S6 -> S7
}

// Initialy the green frogs are on the 3 leftmost stones, the brown frogs
// are on the three rightmost stones and the middle stone is empty.

pred init {

	Green = S1 + S2 + S3
	Brown = S5 + S6 + S7
}

// move a frog from one stone to antoher. This is used by all the 
// following moves.

pred move[stones : set Stone , from : Stone, to : Stone]
{
		to !in Green + Brown
		stones' = stones - from + to
}

// A green frog may move one place to the right if the position is empty

pred moveRight
{
	some g : Green | 
		move[Green, g, g.adj]
	Brown' = Brown
}

// A green frog may jumpt two places to the right if adjacent position 
// has a frog (of any kind) and the position that follows is empty

pred jumpRight
{
	some g : Green | {
		g.adj in Green + Brown
		move[Green, g, g.adj.adj]
	}
	Brown' = Brown
}


// The behavior of brown frogs is symmetric

pred moveLeft
{
	some g : Brown | 
		move[Brown, g, adj.g]
	Green' = Green
}

pred jumpLeft
{
	some g : Brown | {
		adj.g in Green + Brown
		move[Brown, g, adj.adj.g]
	}
	Green' = Green
}

// It is essential to add a skip move, otherwise we cannot require that 
// every state satisfies some operation.

pred Skip {
	Green' = Green
	Brown' = Brown
}

// The first state satisfies the initial configuration. Any state pair
// satisfies one of the legal moves or skip.

fact {
	init
	always (moveRight or moveLeft or jumpRight or jumpLeft or Skip)
}

// Find the traces that solves the puzzle by asserting that we can never get
// to it. The solver will produce a counter example.

check {
	always ! {
		Green = S5 + S6 + S7
		Brown = S1 + S2 + S3
	}
} for 16 steps

// Alternatively, find the traces that solves the puzzle by asking for a trace 
// that eventually gets to the desired state.

run {
	eventually {
		Green = S5 + S6 + S7
		Brown = S1 + S2 + S3
	}
} for 16 steps
