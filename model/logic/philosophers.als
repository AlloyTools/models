
open util/ordering[Table]

sig Table {
	setting 	: P -> Fork
}


sig Fork {}

sig P {
	next			: P,
	left, right 	: Fork
} {
	right = next.@left
}

let update[table',settings'] = no table' or table'.setting=settings'

let take[ philosopher, fork, table, table'] {
	no table.setting.fork
	table'.update[ table.setting + philosopher -> fork ]
}

let eat[ philosopher, table,  table' ] {
	let forks = table.setting[philosopher] {
		# forks = 2
		table'.update[ table.setting - philosopher->forks ]
	}
}

let wait[p,table,tableOrNone'] = {
	one tableOrNone'
	tableOrNone'.setting = table.setting
}

pred step[ philosopher : P, table : Table, table' : lone Table ] {
		philosopher.take[ philosopher.left, 	table, table' ]
	or 	philosopher.take[ philosopher.right, 	table, table' ]
	or	philosopher.eat[ 						table, table' ]
	or  philosopher.wait[						table, table' ]

}

fact trace {
	ring[P]
	bijective[left] and bijective[right]

	no first.setting

	all table : Table - last | 
		some p : P | p.step[ table, table.next ]
}

assert Liveliness {
	no table : Table | no philosopher : P | philosopher.step[table,none]
}


run { #P = 4 } for 4

check Liveliness for 15 but exactly 4 P, 4 Fork, 4 int

// macros

let ring[group] 		= all member : group | member.^next = group
let bijective[relation] = ( all d,r : univ | d.relation = r <=> relation.r = d )
let domain[ relation ] 	= relation.univ
let range[  relation ] 	= univ.relation

