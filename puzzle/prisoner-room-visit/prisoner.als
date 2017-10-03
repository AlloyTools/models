
open util/ordering[State]
open util/integer

/*Define Players*/
abstract sig Prisoner {}
sig OtherPrisoner extends Prisoner{}
one sig CounterPrisoner extends Prisoner {}
one sig NULL{}

fact { Prisoner = OtherPrisoner 
  + CounterPrisoner }
fact { #Prisoner > 1 }

/*Define Boolean*/
abstract sig Bool{}
one sig True extends Bool {}
one sig False extends Bool {}

/*Define Switches*/
abstract sig Switches{}
one sig SwitcheA extends Switches{}
one sig SwitcheB extends Switches{}
fact { Switches = SwitcheA + SwitcheB }

/*Define Status*/
abstract sig Status{}
one sig Up extends Status {}
one sig Down extends Status {}

/*Define State*/
sig State {announced:Bool,
	       SwitchesStatus: Switches->one Status,
	       count:Int,
	       timesSwitched: OtherPrisoner ->one  Int,
	       currentPrisoner: one (Prisoner+NULL)
}

/*Define initial state*/
pred TineSwichedSetToZero{all p:OtherPrisoner{ p->0 in first.timesSwitched}}
pred CountSetToZero{first.count=0}
pred SwitchesInBoolean{all s:Switches{ (s->Down in first.SwitchesStatus) or (s->Up in first.SwitchesStatus)}}
pred AnnouncedSetToFalse{ first.announced = False}
pred CurrentPlayerSetToNull {first.currentPrisoner = NULL}

fact Init{TineSwichedSetToZero and CountSetToZero and SwitchesInBoolean and AnnouncedSetToFalse and CurrentPlayerSetToNull}

pred NonCounterStep[game, game': State,p:Prisoner]{
	p in OtherPrisoner
	game'.currentPrisoner = p
	game'.announced = game.announced
	game'.count = game.count
	(game.announced= True =>
		game'.SwitchesStatus = game.SwitchesStatus
		and game'.timesSwitched = game.timesSwitched
	else
		((game.SwitchesStatus[SwitcheA] = Down and p.(game.timesSwitched) <2) =>
			SwitcheA.(game'.SwitchesStatus) = Up
			and SwitcheB.(game'.SwitchesStatus) = SwitcheB.(game.SwitchesStatus)
			and game'.timesSwitched = game.timesSwitched - p->p.(game.timesSwitched) + p->(p.(game.timesSwitched)+1)
		else
			game'.timesSwitched = game.timesSwitched
			and SwitcheA.(game'.SwitchesStatus) = SwitcheA.(game.SwitchesStatus)
			and (SwitcheB.(game.SwitchesStatus) = Up=>
				SwitcheB.(game'.SwitchesStatus) = Down
			else
				SwitcheB.(game'.SwitchesStatus) = Up)))
}

pred CounterStep[game, game': State, p:Prisoner]{
	p = CounterPrisoner
	game'.currentPrisoner = p
	game'.timesSwitched = game.timesSwitched
	(game.announced= True =>
		game'.SwitchesStatus = game.SwitchesStatus
		and game'.announced = game.announced
		and game'.count =game.count
	else
		(SwitcheA.(game.SwitchesStatus) = Up =>
			SwitcheA.(game'.SwitchesStatus) = Down
			and SwitcheB.(game'.SwitchesStatus) = SwitcheB.(game.SwitchesStatus)
			and game'.count =game.count +1
			and (game'.count = 2.mul[(#Prisoner-1)] =>
				game'.announced = True
			else
				game'.announced = game.announced)
		else
			game'.count = game.count
			and game'.announced = game.announced
			and SwitcheA.(game'.SwitchesStatus) = SwitcheA.(game.SwitchesStatus)
			and (SwitcheB.(game.SwitchesStatus) = Up=>
				SwitcheB.(game'.SwitchesStatus) = Down
			else
				SwitcheB.(game'.SwitchesStatus) = Up)))
}

fact Steps{
		all s: State, s': s.next {
			(one p:OtherPrisoner | NonCounterStep[s, s',p])
			 or (one p:CounterPrisoner | CounterStep[s, s',p])
		}
}

/*Checking types*/
assert  TypeOK {all s:State{
			s.count >=0
			and s.count<= 2.mul[(#Prisoner-1)]
			and  (all p:OtherPrisoner| p.(s.timesSwitched) <=2)
	}
}
check TypeOK for 3 Prisoner, 12 State

/*Checking safety*/
pred StateDone[s:State]{s.count =  2.mul[(#Prisoner-1)]}
pred Announced[s:State]{s.announced = True}

  /*(*************************************************************************)
  (* This formula asserts that safety condition: that Done true implies    *)
  (* that every prisoner other than the counter has flipped switch A at    *)
  (* least once--and hence has been in the room at least once.  Since the  *)
  (* counter increments the count only when in the room, and Done implies  *)
  (* count > 0, it also implies that the counter has been in the room.*)
  (*This is also checks the counter's announcement that all the prisoners was in the room if and only if it is true (means Done)  *)
  (*************************************************************************)*/
assert Safety{all s:State{
			(StateDone[s] =>
				(all p:OtherPrisoner| p.(s.timesSwitched)>0))
			and  (Announced[s] iff StateDone[s])
	}
}
check Safety for 3 Prisoner, 10 State

/* Count always eaqual to the sum of timesSwitched of all OtherPrisoners(+-1)*/
assert CountInvariant{all s:State {
				(let totalSwitched = (sum p:OtherPrisoner | p.(s.timesSwitched)) |
				(SwitcheA.(s.SwitchesStatus) = Up => 
					((s.count = totalSwitched -1) or (s.count = totalSwitched))
				else
					((s.count = totalSwitched) or (s.count = totalSwitched +1))))
	}
}

check CountInvariant for 3 Prisoner, 10 State


/*Checking fairness*/
pred AfterNonCounterPlayerEventaullyCounterPlayertEnterTheRoom{
		all s: State|
			((s.currentPrisoner in OtherPrisoner) => 
				(some s': s.^next | s'.currentPrisoner = CounterPrisoner))
}

pred PrisonerComesImmediatelyAfterCounter[s: State, p:OtherPrisoner]{ 
			s.currentPrisoner = CounterPrisoner and s.next.currentPrisoner = p
}

pred Fairness {(all p:OtherPrisoner{ 
			some s,s':State {s' in s.^next 
					and PrisonerComesImmediatelyAfterCounter[s,p] 
					and PrisonerComesImmediatelyAfterCounter[s',p]
			}
		})
		AfterNonCounterPlayerEventaullyCounterPlayertEnterTheRoom
}

pred Done{some s:State | Announced[s]}

assert Theorem{Fairness => Done}
check Theorem for 3 Prisoner, 12 State

run {} for 4 int, exactly 3 Prisoner, 12 State
