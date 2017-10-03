
/**
  A partial formal definition of a Map in Java

	See http://aqute.biz/2017/07/15/Alloy.html
*/


sig Object {}
one sig null extends Object 	{}
enum boolean { true, false }

sig Map {
	entries : Object -> lone Object
}

fun Map.size : Int {
		# this.entries
}

pred Map.isEmpty {
		no entries
}

pred Map.containsKey( k : Object ) {
	one this.entries[k]
}


pred Map.containsValue( v : Object ) {
	one this.entries.v
}

fun Map.get( k : Object ) : Object {
	let v = this.entries[k] | one v implies v else null
}

pred Map.put( m' : Map,  k, v, r : Object ) {
	this.get[k] = r
	m'.entries = this.entries ++ k -> v	
}

pred Map.remove( m' : Map,  k, r: Object ) {
	this.containsKey[k] 
		implies { 
					m'.entries = this.entries - k->Object
			and	this.get[k] = r
		} else {
			r = null
			m'.entries = this.entries
		}
}

pred Map.putAll( m', other : Map ) {
	m'.entries = this.entries ++ other.entries
}

fun Map.keySet : set Object {
	this.entries.Object
}

fun Map.values : set Object {
	this.entries[Object]
}

pred Map.clear( m' : Map ) {
	m'.isEmpty
}

fun Map.entrySet : Object -> Object {
	this.entries
}

pred equals( a,b : Map ) {
	a.keySet = b.keySet
	all k : a.keySet | a.get[k] = b.get[k]
}

pred Map.putIfAbsent( m' : Map, k, initial, r : Object ) {
	this.containsKey[k] 
		implies r = this.get[k] 
		else ( r=null and this.put[m',k,initial,null])
}

pred Map.remove( m' : Map, k, v : Object, r : boolean ) {
	k -> v in this.entries 
		implies ( m'.entries = this.entries - k -> v 
			and r = true ) 
		else r=false
}

pred Map.replace( m' : Map, k, oldValue, newValue : Object, r : boolean ) {
		this.put[m',k,newValue,oldValue] implies r = true else r = false
}

/*
 * Replaces the entry for the specified key only if it is
 * currently mapped to some value.
 */

pred Map.replace( m' : Map, k, v, r : Object ) {
		this.containsKey[k] implies this.put[m',k,v,r] else r = null
}



// Verifications

pred Map.put'(m' : Map, k, v, r : Object ) {

	m'.containsKey[k]
	m'.get[k] = v 
	this.get[k]  = r 

	this.containsKey[k]
		implies {
			this.size = m'.size

			r = null or r != null
		} else {
			this.size.plus[1] = m'.size
			r = null
		}
}

pred Map.clear'[ m' : Map ] {
	m'.size = 0
	all k : Object | {
		m'.get[k] = null
		not m'.containsKey[k]
	}
}

pred Map.remove'( m' : Map, k, r : Object) {
	not m'.containsKey[k]

	this.containsKey[k] implies {
		this.get[k] = r
		this.size.minus[1] = m'.size	
	} else {
		r = null
		this.size = m'.size				
	}
}

pred Map.putAll'( m', other : Map ) {

	this.keySet + other.keySet = m'.keySet

	all k : this.keySet + other.keySet | {
		let v = k in other.keySet 
			implies other.get[k] 
			else 		this.get[k] | {
				m'.get[k] = v
			}
	}
}

assert verify {

	all m, m', other : Map, k, v, r : Object | {
		m.put[m', k, v, r ] 		implies m.put'[m',k,v,r]
		m.clear[m']          		implies m.clear'[m']
		m.remove[m',k, r]				implies m.remove'[m',k,r]
		m.putAll[m',other]			implies m.putAll'[m',other]
	}

}

check verify for 4 but 2 Map



fact {
	# Map > 0
}
