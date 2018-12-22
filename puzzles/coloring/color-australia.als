/**
 * Example constraint solving with Alloy
 * Solves the coloring problem for coloring Australia's states with
 * different colors. This problem was defined in miniZinc but I
 * think it looks better in Alloy
 */


sig Color {}
enum State { wa, nt, q, sa, nsw, v, t }

let adjacent = 
		wa -> nt 
	+ 	wa -> sa 
	+ 	nt->sa 
	+ 	nt->q 
	+ 	sa->q 
	+ 	sa->nsw 
	+ 	sa-> v 
	+ 	q->nsw 
	+ 	nsw->v

pred colors[ coloring :  State  -> one Color ] {
	all s : State, a : adjacent[s] | coloring[s] != coloring[a]
}

run colors for 1 but exactly 3 Color
