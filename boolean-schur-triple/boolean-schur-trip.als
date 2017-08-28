//
// Boolean Schur Triple Problem: 
//   does there exists a red/blue coloring of the numbers 1 to n, 
//   such that there is no monochromatic solution of 
//
//         a + b = c with a < b < c ≤ n.
//

enum Color { Red, Blue }

pred monochromatic( s : seq Color, a, b, c : Int ) {	
		a.plus[b] = c
	  a < b and b < c and c < # s
		# (s[a] + s[b] + s[c]) = 1 // all same color
}

pred schur( s : seq Color ) {

  // cardinality is +1 from schur since
  // schur starts at 1 and Alloy starts at 0.
  // se we remove the 0
  
	# s = 10 	
  
	no a,b,c : s.inds - 0| monochromatic[s,a,b,c]
}

run schur for 20 but 6 int
