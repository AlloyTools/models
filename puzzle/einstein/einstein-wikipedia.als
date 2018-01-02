
/**
 * See https://en.wikipedia.org/wiki/Zebra_Puzzle
 */
 
open util/ordering[House]


enum Color { yellow, blue, red,   ivory, green}
enum Nationality {Norwegian, Ukrainian, Englishman, Spaniard, Japanese }
enum Drink {water, tea,milk,juice,coffee}
enum Smoke {Kools,Chesterfield,OldGold,LuckyStrike,Parliament}
enum Pet {fox,horse,snails,dog,zebra}

sig House {
    house    : one Color,
    home     : one Nationality,
    drunk    : one Drink,
    smoker   : one Smoke,
    owns     : one Pet
} 


fact  disjunct {
	all disj h1, h2 : House | 
		all f : House$.subfields | 
			h1.(f.value) != h2.(f.value)
}

pred House.nextTo[ other : House ] { 
	other in this.(prev+next) 
}

let centerHouse = first.next.next

fact {


	// There are five houses.

	# House = 5

	// The Englishman lives in the red house.
	Englishman.~home = red.~house

	// The Spaniard owns the dog.
	Spaniard.~home = owns.dog

	// Coffee is drunk in the green house.
	coffee.~drunk = green.~house

	// The Ukrainian drinks tea.
	Ukrainian.~home = drunk.tea

	// The green house is immediately to the right of the ivory house.
	green.~house = ivory.~house.next

	// The Old Gold smoker owns snails.
	OldGold.~smoker = owns.snails

	// Kools are smoked in the yellow house.
	Kools.~smoker = yellow.~house

	// Milk is drunk in the middle house.
	milk.~drunk = centerHouse

	// The Norwegian lives in the first house.
	Norwegian.~home = first

	// The man who smokes Chesterfields lives in the house next to the man with the fox.
	Chesterfield.~smoker.nextTo[ owns.fox ]

	// Kools are smoked in the house next to the house where the horse is kept.
	Kools.~smoker.nextTo[ owns.horse ]

	// The Lucky Strike smoker drinks orange juice.
	LuckyStrike.~smoker = drunk.juice

	// The Japanese smokes Parliaments.
	Japanese.~home = smoker.Parliament

	// The Norwegian lives next to the blue house.
	Norwegian.~home.nextTo[ blue.~house ]
}

run { one drunk.water and one owns.zebra } for 5

	
