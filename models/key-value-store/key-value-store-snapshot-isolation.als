-- ISVS project: Key-value-store with snapshot isolation
-- Ported from TLA+ @ https://en.wikipedia.org/wiki/TLA%2B#Examples
-- Part II: Snapshot isolation

-- Macro for relations that don't change during transitions
let unchanged[r] { (r)' = (r) }

-- Set of all keys in the key-value-store
sig Key {}

-- Set of all values
sig Value {}

-- The store (changed over time by transactions committing)
one sig Store {
	var store: Key -> lone Value,							-- Each key points to one or no value
	var openTx: set Transaction,							-- Set of open snapshot transactions
}

-- Set of all transactions
sig Transaction {
	var snapshotStore: Key -> lone Value,			-- Snapshot of `store` for this transaction
	var written: set Key,										-- Keys written to in this transaction
	var missed: set Key,										-- Writes (from concurrently committed transactions) invisible to this transaction
}

-- Open a new transaction
pred openTx[t: Transaction] {
	t not in Store.openTx
	openTx' = openTx + (Store -> t)
	snapshotStore' = snapshotStore + (t -> Store.store)

	unchanged[written]
	unchanged[missed]
	unchanged[store]
}

-- Add a key-value-pair to an open transaction
pred add[t: Transaction, k: Key, v: Value] {
	t in Store.openTx
	no t.snapshotStore[k]										-- Key may not have value yet, otherwise update must be done
	snapshotStore' = snapshotStore + (t -> k -> v)
	written' = written + (t ->  k)							-- Add k to t.written
	
	unchanged[openTx]
	unchanged[missed]
	unchanged[store]
}

-- Update the value of a key-value-pair in an open transaction
pred update[t: Transaction, k: Key, v: Value] {
	t in Store.openTx
	some t.snapshotStore[k]									-- Key must have value, otherwise add must be done
	snapshotStore' = snapshotStore - (t -> k -> Value) + (t -> k -> v)
	written' = written + (t -> k)								-- Add k to t.written
	
	unchanged[openTx]
	unchanged[missed]
	unchanged[store]
}

-- Remove a key-value-pair from an open transaction
pred remove[t: Transaction, k: Key] {
	t in Store.openTx
	some t.snapshotStore[k]									-- Key must have value
	snapshotStore' = snapshotStore - (t -> k -> Value)
	written' = written + (t -> k)								-- Add k to t.written

	unchanged[openTx]
	unchanged[missed]
	unchanged[store]
}

-- Rollback open transaction, doesn't affect store
pred rollbackTx[t: Transaction] {
	t in Store.openTx
	openTx' = openTx - (Store -> t)
	snapshotStore' = snapshotStore - t <: snapshotStore
	written' = written - (t -> Key)
	missed' = missed - (t -> Key)

	unchanged[store]
}

-- Commit open transaction, merge with store
pred commitTx[t: Transaction] {
	t in Store.openTx
	no (t.missed & t.written)
	openTx' = Store -> (Store.openTx - t)
	snapshotStore' = snapshotStore - t <: snapshotStore
	written' = written - (t -> Key)

	-- All other currently open transactions add what t has written to their set of missed writes
	all tx: Transaction | tx.missed'= (tx in (Store.openTx - t) implies tx.missed + t.written else none)
	-- Update all keys in store that t has written too (including removal!)
	all k: Key | Store.store'[k] = (k in t.written implies t.snapshotStore[k] else Store.store[k])
}

-- Do nothing / stutter (not necessary, but is useful for debugging)
pred nop {
	unchanged[store]
	unchanged[openTx]
	unchanged[snapshotStore]
	unchanged[written]
	unchanged[missed]
}

-- Initial state
pred init {
	no Store.store 													-- no values are stored
	no Store.openTx												-- no open transactions
	no snapshotStore												-- no snapshots
	no written														-- no writes yet
	no missed															-- no missed writes yet
}

-- Next state transition
fun next: Transition {
	t_openTx.Transaction 
	+ t_add.Value.Key.Transaction
	+ t_update.Value.Key.Transaction
	+ t_remove.Key.Transaction
	+ t_rollbackTx.Transaction
	+ t_commitTx.Transaction
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
-- This allows showing in the visualizer which transition happens in each step
enum Transition { Open, Add, Update, Remove, Rollback, Commit, Nop }

fun t_openTx: Transition -> Transaction {
	{ tp: Open, t: Transaction | openTx[t] }
}

fun t_add: Transition -> Transaction -> Key -> Value {
	{ tp: Add, t: Transaction, k: Key, v: Value | add[t,k,v] }
}

fun t_update: Transition -> Transaction -> Key -> Value {
	{ tp: Update, t: Transaction, k: Key, v: Value | update[t,k,v] }
}

fun t_remove: Transition -> Transaction -> Key {
	{ tp: Remove, t: Transaction, k: Key | remove[t,k] }
}

fun t_rollbackTx: Transition -> Transaction {
	{ tp: Rollback, t: Transaction | rollbackTx[t] }
}

fun t_commitTx: Transition -> Transaction {
	{ tp: Commit, t: Transaction | commitTx[t] }
}

fun t_nop: Transition {
	{ tp: Nop | nop }
}
-- ENDSECTION VISUALIZATION



-- SECTION ANOMALY VERIFICATION
-- Assertions assume the anomaly *cannot* occur. If a counterexample is found
-- the specified isolation strategy does not prevent the specified anomaly

assert DirtyWrite {
	-- Writes from concurrent transactions may not override each other
	no disj t1, t2: Transaction, k: Key, disj v1, v2: Value | {
		openTx[t1]
		;openTx[t2]
		;add[t1,k,v1]
		;add[t2,k,v2]
		;commitTx[t1]
		;commitTx[t2]
	}
}
check DirtyWrite expect 0

assert DirtyRead {
	-- Writes from concurrent transactions may not affect each others reads
	no disj t1, t2: Transaction, k: Key, disj v1, v2: Value | {
		-- Since the following add implies that k cannot have a value when t1 is opened
		-- The following condition is unnecessary, it does however make clearer what this intends to verify
		Store.store[k] = v2
		;openTx[t1]
		;openTx[t2]
		;add[t1,k,v1]
		;t2.snapshotStore[k] = v1
	}
}
check DirtyRead expect 0

assert NonRepeatableRead {
	-- Writes from concurrently committed transactions may not affect reads of others
	-- Only commits before opening a transaction may be taken into account
	no disj t1, t2: Transaction, k: Key, disj v1, v2: Value | {
		Store.store[k] = v1
		openTx[t1]
		;openTx[t2]
		;t1.snapshotStore[k] = v1
		;update[t2,k,v2]
		;commitTx[t2]
		;t1.snapshotStore[k] = v2
	}
}
check NonRepeatableRead expect 0

assert PhantomRow {
	-- Concurrent transactions may not add new rows (key-value-pairs) to each other
	no disj t1, t2: Transaction, k: Key, v: Value | {
		#Store.store = 0
		openTx[t1]
		;openTx[t2]
		;#t1.snapshotStore = 0
		;add[t2,k,v]
		;commitTx[t2]
		-- Make sure commitTx[t2] and the verification occur at the same time.
		-- Otherwise t1 might have just added a new row itself
		#t1.snapshotStore = 1
	}
}
check PhantomRow expect 0

pred noDuplicateWrites {
	-- No transaction is allowed to add/update to a value, that's already in its snapshot
	-- This should ensure no duplicated values enter the store
	all t: Transaction | all v: t.snapshotStore[Key] | no k: Key | add[t,k,v] or update[t,k,v]
}
assert WriteSkew {
	-- Never writing an existing values should ensure no duplicated values in store
	always noDuplicateWrites implies always #Store.store[Key] = #Store.store
}
check WriteSkew expect 1
-- ENDSECTION ANOMALY VERIFICATION



-- SECTION RUN / CHECK CONFIGURATIONS
assert MissedWrites {
	-- If store and snapshotStore[t] have different values mapped to a key, and t hasn't written to the key yet,
	-- it must have been a missed write from a concurrent transaction
	always all t: Store.openTx, k: Key | (Store.store[k] != t.snapshotStore[k] and k not in t.written) implies k in t.missed
	-- Transactions shall be cleaned up after disposal (closing them)
	always all t: Transaction - Store.openTx, k: Key |  {
		no t.snapshotStore[k]
		no t.written
		no t.missed
	}
}

-- Limiting this to 5 steps as is takes very long
check MissedWrites for 5 steps expect 0

run Scenario {
	some disj t1, t2, t3: Transaction, disj k1, k2, k3 : Key, disj v1, v2: Value | {
		openTx[t3]
		;add[t3, k1, v2]
		;commitTx[t3]
		;openTx[t1]
		;openTx[t2]
		;update[t1, k1, v1]
		;add[t1, k2, v2]
		;update[t1, k2, v1]
		;remove[t1, k1]
		;add[t2, k3, v1]
		;commitTx[t2]
		;commitTx[t1]
		;always nop
	}
} for exactly 3 Transaction, exactly 3 Key, exactly 3 Value, 20 steps expect 1

-- Finds some random progression of steps leading to a store where every key is mapped to some value
run Random {
	eventually #Store.store = 3
} for exactly 3 Transaction, exactly 3 Key, exactly 3 Value, exactly 20 steps expect 1
