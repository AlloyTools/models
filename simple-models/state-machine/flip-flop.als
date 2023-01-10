//
// A simple model of a flipflop state machine that 
// flips on every clock event.
//
// This is probably the simplest possible time based example
// for Alloy but shows how to make a trace. 
//

open util/ordering[Trace]

enum Event { C }
enum State { On, Off }

fun transitions : State -> Event -> State {
    On  -> C -> Off 
  + Off -> C -> On
}

sig Trace {
  state : State,
  event : lone Event
}

fact {
  first.state = On
  no last.event

  all t : Trace - last, t" : t.next {
    some e : Event {
      t.event = e 
      t".state = transitions[t.state][t.event]
    }
  }
}

pred show( t : set Trace ) { }

run show  for 10
