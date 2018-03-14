---
title: Web Attacks Intro
---

# Web Attacks

This model shows a store and provides a number of requests to modify the store. It then shows how 
to use the store with a good user `Alice` and have a bad user `Eve` that do not give any credentials.
Eve should therefore never be able to login or buy anything.

## Preamble

Order the Token and State sigs which will be used later. (The includes (`open`) must come first.)
We also define Item and Token which are needed later but only used for their identity. We
require some of them to be there because otherwise you run into the really nasty problem
that any comprehension seems to succeed because it misses atoms for one of the variables.

```alloy
	module store
	open util/ordering[Token] as tk
	open util/ordering[State] as st

	some sig Item, Token {}
```


## Actions

We later create a serial trace of actions that are performed in the store. The 
following actions are defined:

```alloy
	enum Action { 
		INIT, 
		BUY, 
		LOGIN, 
		STUTTER 
	}
```

The `STUTTER` action is necessary to not block the trace. I.e. if there are no more items and 
everybody is logged in then there are no alternative actions so then stutter can fill the gap.

## Authentication

We use a simple userid to digest table. The `digest` (total) function calculates a digest. In this case
we use the same atom for ease of use but this should be a one-way hash function like the SHA-x
algorithm.

We add the credentials for Alice but no credentials for Eve. That is, Eve has no access to the 
store.

```alloy
	fun digest[password : String ] : String { password }

	pred authenticate[userid,password : String] {
		userid->digest[password] in 
			("Alice" -> digest["Bob123"]) 
	}
```

## State

We need to create a trace of actions. We maintain this state in, ehh, `State`. For convenience
this State maintains the state for both the browser (the cookies) and the server (the stock,
token generator, etc.).

Notice that the order is very relevant here because it defines how the sig is displayed in the
table view. You should try to create 'sentences' with the order. For example, `Eve BUY item` 

It is important to realize that the cookies are _shared state_. This means that the browser is free 
to ignore or violete the contract of cookies. We can therefore not create any facts that rely in the 
cookies.

```alloy
	sig State {

		browser		: lone Browser,
		action		: Action,
		bought		: lone Item,

		// Reflects the browser state

		cookies		: Browser -> Token,

		// Reflects the server state

		stock		: set Item,
		cart		: Token -> (Item+String),
		token		: lone Token,
		nextToken	: Token,
	}
```
## Action Predicates

Later we define a trace of actions. A trace is a sequence of State atoms. We require
that the trace is constrained by the action predicates. That is, going from State<sup>n</sup> to
State<sup>n+1</sup> requires that one of the action predicates is `true`. 

## Login

The first action predicate is `login`. A browser gives us a userid and a password. These credentials
must be authenticated before the login succeeds. 

If this login is successful then we require a cookie with a _token_. 
This token is a capability, a browser that has that token can then
buy in the store.

The login fails if the user is already logged in. It might be interesting
to succeed a failed attempt due to lack of proper credentials. This would then
record the attack in the trace. That is not done here.

In the cart we record the user id as the first _bought_ item, this is a bit hackish. 
It records the name of the user of that cart, but it also creates at least one entry in
the cart. I.e. it _activates_ the cart. (Never realized you could hack in models?)

```alloy

	pred login[ s, s' : lone State ] {
		let 	browser = s'.browser, 
			userid = browser.userid,
			password = browser.password {

			one userid
			one password
			no s.cart.userid
			authenticate[ userid,password ] 

			s'.action = LOGIN
			s'.nextToken = s.nextToken.next
			s'.stock = s.stock
			s'.cart = s.cart + (s.nextToken->userid)
			s'.token = s.nextToken
			s'.bought = none	
			s'.cookies = s.cookies + (browser->s.nextToken)
		}
	}
```

## Buy

After login the browser has a cookie with a token. We use this token to record
the sale in the corresponding cart.

```alloy

	pred buy[ s, s' : State ] {
		let 	item 	= s'.bought, 
			tkn 	= s'.token {

			some item
			item in s.stock 
	
			one tkn
			some s.cart[tkn]
	
			s'.action = BUY
			s'.nextToken = s.nextToken
			s'.stock = s.stock-item
			s'.cart = s.cart + (tkn -> item)
			s'.token = tkn
			s'.bought = item
	
			s'.cookies = s.cookies
		}
	}
```

## Stutter

A stutter action is there to fill gaps. If the trace cannot make progress then it can always
provide a stutter step. They are kind of annoying because a trace with just stutters is
then a perfectly valid solution. You have to filter out those solutions with your `run` command.
For `check` commands they are generally irrelevant.

```alloy

	pred stutter[s, s' : State ] {

		s'.action = STUTTER
		s'.nextToken = s.nextToken
		s'.stock = s.stock
		s'.cart = s.cart
		s'.browser = none
		s'.token = none
		s'.bought = none

		s'.cookies = s.cookies
	}		

```

## The Clients

We're now ready to define the client side. Our model is that we have a _Browser_, 
a.k.a the _User Agent_. 

We're cheating a bit because we do not record the cookies in the browser, we rely 
on the shared state to store the cookies. (This is dangerous because it is 
now easy to make facts that assume the server knows about the browser.)

We are also definining two users: Alice and Eve. Alice is the good girl and gets a password. Eve is evil
and we do not constrain her use of credentials. In practice, this means that Alloy will use all
possible credentials for Eve.

```alloy
	abstract sig Browser {
		userid : String,
		password : String
	}

	one sig Alice extends Browser {} {
		userid = "Alice"
		password = "Bob123"
	}
	one sig Eve extends Browser {}
```

## Trace
We now create a trace of every combination of all possible actions. We constrain
the actions to those allowed by the action predicates `login`, `buy`, and `stutter`.

That is, each action predicate is used to constrain State<sup>n</sup> -> State<sup>n+1</sup> 

```alloy
	fact {

		st/first.nextToken = tk/first
		st/first.stock = Item
		no st/first.bought
		no st/first.cart
		no st/first.browser
		no st/first.cookies
		st/first.action = INIT

		all s' : State - first, s : s'.prev {

				login[s,s']
			or 
				buy[s,s']
			or
				stutter[s,s']

		}
	}
```

## Checking 

We do not want Eve to be able to buy anything, only Alice's credentials are recorded
in the password database so Eve should not be able to login nor buy anything.

So we can check that Eve can never buy anything nor can she login:

```alloy
        assert Evil {
		no s : State | s.browser = Eve
	}
	check Evil for 4
```

If we run this then it gives us the following output.

	┏━━━━━━━━━━┳━━━━━━━┳━━━━━━━━┳━━━━━━┳━━━━━━━━━━━┳━━━━━┳━━━━━━━━━━━━━━┳━━━━━━┳━━━━━━━━━┓
	┃this/State┃browser┃action  ┃bought┃cookies    ┃stock┃cart          ┃token ┃nextToken┃
	┠──────────╊━━━━━━━╋━━━━━━━━╋━━━━━━╋━━━━━━━━━━━╋━━━━━╋━━━━━━━━━━━━━━╋━━━━━━╋━━━━━━━━━┫
	┃State⁰    ┃       ┃INIT⁰   ┃      ┃           ┃Item⁰┃              ┃      ┃Token⁰   ┃
	┠──────────╊━━━━━━━╋━━━━━━━━╋━━━━━━╋━━━━━━━━━━━╋━━━━━╋━━━━━━━━━━━━━━╋━━━━━━╋━━━━━━━━━┫
	┃State¹    ┃       ┃STUTTER⁰┃      ┃           ┃Item⁰┃              ┃      ┃Token⁰   ┃
	┠──────────╊━━━━━━━╋━━━━━━━━╋━━━━━━╋━━━━━━━━━━━╋━━━━━╋━━━━━━━━━━━━━━╋━━━━━━╋━━━━━━━━━┫
	┃State²    ┃       ┃STUTTER⁰┃      ┃           ┃Item⁰┃              ┃      ┃Token⁰   ┃
	┠──────────╊━━━━━━━╋━━━━━━━━╋━━━━━━╋━━━━┯━━━━━━╋━━━━━╋━━━━━━┯━━━━━━━╋━━━━━━╋━━━━━━━━━┫
	┃State³    ┃Eve⁰   ┃LOGIN⁰  ┃      ┃Eve⁰│Token⁰┃Item⁰┃Token⁰│"Alice"┃Token⁰┃Token¹   ┃
	┗━━━━━━━━━━┻━━━━━━━┻━━━━━━━━┻━━━━━━┻━━━━┷━━━━━━┻━━━━━┻━━━━━━┷━━━━━━━┻━━━━━━┻━━━━━━━━━┛

You can see this also in the Browser table. We see that Eve has stolen the credentials
of Alice.
	
	┏━━━━━━━━━━━━┳━━━━━━━┳━━━━━━━━┓
	┃this/Browser┃userid ┃password┃
	┠────────────╊━━━━━━━╋━━━━━━━━┫
	┃Alice⁰      ┃"Alice"┃"Bob123"┃
	┠────────────╊━━━━━━━╋━━━━━━━━┫
	┃Eve⁰        ┃"Alice"┃"Bob123"┃
	┗━━━━━━━━━━━━┻━━━━━━━┻━━━━━━━━┛

## Attacks

This is a bit of a conumdrum but it shows the power of Alloy. This immediately shows how 
fragile passwords are. In the real world we demand from the users that they keep their 
passwords secret. We therefore record this (stupid!) assumption in a fact.


```alloy

	fact NoSharedPassword {
	//	all disj b1, b2 : Browser | b1.userid = b2.userid => b1.password != b2.password
	}
```
Uncomment the previous fact and the run the EveBuying command again. This gives the following output

	┏━━━━━━━━━━┳━━━━━━━┳━━━━━━━━┳━━━━━━┳━━━━━━━━━━━━━┳━━━━━┳━━━━━━━━━━━━━━┳━━━━━━┳━━━━━━━━━┓
	┃this/State┃browser┃action  ┃bought┃cookies      ┃stock┃cart          ┃token ┃nextToken┃
	┠──────────╊━━━━━━━╋━━━━━━━━╋━━━━━━╋━━━━━━━━━━━━━╋━━━━━╋━━━━━━━━━━━━━━╋━━━━━━╋━━━━━━━━━┫
	┃State⁰    ┃       ┃INIT⁰   ┃      ┃             ┃Item⁰┃              ┃      ┃Token⁰   ┃
	┠──────────╊━━━━━━━╋━━━━━━━━╋━━━━━━╋━━━━━━━━━━━━━╋━━━━━╋━━━━━━━━━━━━━━╋━━━━━━╋━━━━━━━━━┫
	┃State¹    ┃       ┃STUTTER⁰┃      ┃             ┃Item⁰┃              ┃      ┃Token⁰   ┃
	┠──────────╊━━━━━━━╋━━━━━━━━╋━━━━━━╋━━━━━━┯━━━━━━╋━━━━━╋━━━━━━┯━━━━━━━╋━━━━━━╋━━━━━━━━━┫
	┃State²    ┃Alice⁰ ┃LOGIN⁰  ┃      ┃Alice⁰│Token⁰┃Item⁰┃Token⁰│"Alice"┃Token⁰┃Token¹   ┃
	┠──────────╊━━━━━━━╋━━━━━━━━╋━━━━━━╋━━━━━━┿━━━━━━╋━━━━━╋━━━━━━┿━━━━━━━╋━━━━━━╋━━━━━━━━━┫
	┃State³    ┃Eve⁰   ┃BUY⁰    ┃Item⁰ ┃Alice⁰│Token⁰┃     ┃Token⁰│"Alice"┃Token⁰┃Token¹   ┃
	┃          ┠───────╂────────╂──────╂──────┴──────┨     ┃      ├───────╂──────╂─────────┨
	┃          ┃       ┃        ┃      ┃             ┃     ┃      │Item⁰  ┃      ┃         ┃
	┗━━━━━━━━━━┻━━━━━━━┻━━━━━━━━┻━━━━━━┻━━━━━━━━━━━━━┻━━━━━┻━━━━━━┷━━━━━━━┻━━━━━━┻━━━━━━━━━┛

Since Eve can no longer succeed in using Alice's credentials, it tries to steal the token that the
server handed to Alice's browser. It can do this by sniffing in on a wireless network at
Starbucks when Alice uses normal HTTP, not encrypted HTTPS.

It is interesting to see that the item ends up in Alice's cart. 

So we need to record a fact that our model can assume that in the real world the cookies are
protected using HTTPS and cannot be guessed. In our model that means we can 'trust' the
cookies to be protected. (Another indication of the fragility of the web.)

Again uncomment for making it active.

```alloy
	fact HTTPS {
	//	all s : State | one s.token implies s.token = s.cookies[s.browser]
	}
```

Instead of doing a run, we now want to make sure Eve cannot buy anything ever ... So if you
run the check again it should fail to find a counter example.

So now we know the web is safe! `#not`




