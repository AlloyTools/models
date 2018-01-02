        open util/ordering[Time]

	sig Time {}


	let range[s,e] 			= (s + s.nexts) - e.nexts // inclusive bounds i.e. [s,e]
	let overlap[s1,e1,s2,e2] 	= some (range[s1,e1] & range[s2,e2])

	check {


		// [t0,t0] ∩ [t0,tn]
		overlap[ first, first, first, last ] 

		// [t0,t1] ∩ [t1,tn]
		overlap[ first, first.next, first.next, last ]

		// [t0,t1] ∩ [t0,tn]
		overlap[ first, first.next, first, last ]

		// [t0,t1] ∩ [t0,t1]
		overlap[ first, first.next, first, first.next ]	

		// not ( [t1,t0] ∩ [t0,t1] )
		not overlap[ first.next, first, first, last ]

		// not ( [t0,t1] ∩ [t2,tn] )
		not overlap[ first, first.next, first.next.next, last ]	

		// reflexive
		all t1, t2, t3,  t4 : Time | overlap[t1,t2,t3,t4] <=> overlap[t3,t4,t1,t2]
	} for 10
