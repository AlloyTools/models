/**
 * Syllogism (Greek: συλλογισμός syllogismos, 
 * "conclusion, inference") is a kind of logical argument 
 * that applies deductive reasoning to arrive at a 
 * conclusion based on two or more propositions that 
 * are asserted or assumed to be true.
 *
 * In its earliest form, defined by Aristotle, from the 
 * combination of a general statement (the major premise) 
 * and a specific statement (the minor premise), a conclusion 
 * is deduced. 
 * 
 * For example, knowing that all men are mortal (major premise) 
 * and that Socrates is a man (minor premise), we may validly 
 * conclude that Socrates is mortal. Syllogistic arguments 
 * are usually represented in a three-line form:
 *
 *   All men are mortal.
 *   Socrates is a man.
 *   Therefore Socrates is mortal.
 */

	sig Men{}
	one sig Socrates {}

	check {

		all mortal, men : some Men + Socrates {

			men in mortal
			and  
			Socrates in men 
			=> Socrates in mortal

		}
	} for 5 Men

/**
 * This is very error prone since the following is not correct:
 *
 *   All men are mortal.
 *   Socrates is a mortal.
 *   Therefore Socrates is a man.
 *
 * Running the following example will therefore fail
 */

	check {

		all mortal, men : some Men + Socrates {

			men in mortal
			and  
			Socrates in mortal 
			=> Socrates in men

		}
	} for 5 Men
