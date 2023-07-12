-- ISVS project: Key-value-store with snapshot isolation
-- Ported from TLA+ @ https://en.wikipedia.org/wiki/TLA%2B#Examples
-- Part I: No snapshot isolation

-- Macro for relations that don't change during transitions
let unchanged[r] { (r)' = (r) }

-- Set of all keys in the key-value-store
sig Key {}

-- Set of all values
sig Value {}

-- The store (changed over time by transactions committing)
one sig Store {
	var store: Key -> lone Value,						-- Each key points to one or no value
}

-- Add a key-value-pair to store
pred add[k: Key, v: Value] {
	no Store.store[k]											-- Key may not have value yet, otherwise update must be done
	Store.store' = Store.store ++ k -> v
}

-- Update the value of a key-value-pair in store
pred update[k: Key, v: Value] {
	some Store.store[k]										-- Key must have value, otherwise add must be done
	Store.store' = Store.store ++ k -> v
}

-- Remove a key-value-pair from store
pred remove[k: Key] {
	some Store.store[k]										-- Key must have value
	Store.store' = Store.store - (k -> Value)
}

-- Do nothing / stutter (not necessary, but is useful for debugging)
pred nop {
	unchanged[store]
}

-- Initial state
pred init {
	no Store.store 												-- no values are stored
}

-- Next state transition
fun next: Transition {
	t_add.Value.Key
	+ t_update.Value.Key
	+ t_remove.Key
	+ t_nop
}

-- Begin with init state and always transition using `next`
fact KeyValueStore {
	init
	always some { this/next }
}
-- ENDSECTION MAIN



-- SECTION VISUALIZATION
-- These functions are used to wrap transition predicates
-- This allows to show, which transition happens in each step in the visualizer
enum Transition { Add, Update, Remove, Nop }

fun t_add: Transition -> Key -> Value {
	{ tp: Add, k: Key, v: Value | add[k,v] }
}

fun t_update: Transition -> Key -> Value {
	{ tp: Update, k: Key, v: Value | update[k,v] }
}

fun t_remove: Transition -> Key {
	{ tp: Remove, k: Key | remove[k] }
}

fun t_nop: Transition {
	{ tp: Nop | nop }
}
-- ENDSECTION VISUALIZATION



-- SECTION RUN / CHECK CONFIGURATIONS
run Scenario {
	some disj k1, k2, k3 : Key, disj v1, v2: Value | {
		add[k1, v2]
		;update[k1, v1]
		;add[k2, v2]
		;update[k2, v1]
		;remove[k1]
		;add[k3, v1]
	}

} for exactly 3 Key, exactly 3 Value, 20 steps

run Random {

} for exactly 3 Key, exactly 3 Value, exactly 20 steps
