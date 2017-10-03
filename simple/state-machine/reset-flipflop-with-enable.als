
open util/ordering[Trace]

enum Event { C, X }
enum State { On, Off }

fun transitions : State -> Event -> State {
			On  -> C -> Off 
		+ On  -> X -> On
		+ Off -> C -> On
		+ Off -> X -> Off 
}

sig Trace {
	state : State,
	event : lone Event
}

fact {
	first.state = On
	no last.event	

	all t' : Trace - first, t : t'.prev {
		some e : Event | 
					t.event = e 
			and t'.state = transitions[t.state][t.event]		
	}
}

pred show( ) { 
	some t : Trace | all s : t.^next | s.state = Off 

}

run show  for 10
