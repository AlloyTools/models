// Example from CACM 2019 paper by Jackson
// Alloy: A Language and Tool for Exploring Software Designs
// An exploration of an origin tracking mechanism to counter CSRF

abstract sig EndPoint { }

sig Server extends EndPoint {
	causes: set HTTPEvent
	}

sig Client extends EndPoint { }

abstract sig HTTPEvent {
	from, to, origin: EndPoint
	}

sig Request extends HTTPEvent {
	response: lone Response
	}

sig Response extends HTTPEvent {
	embeds: set Request
	}

sig Redirect extends Response {
	}

run {some response}

fact Directions {
	Request.from + Response.to in Client
	Request.to + Response.from in Server
	}

fact Causality {
	-- s causes e if
	-- 	e is (a response) from s, or
	-- 	e is (a request) embedded in r and s causes r
	all e: HTTPEvent, s: Server |
		e in s.causes iff e.from = s or some r: Response | e in r.embeds and r in s.causes
	}

fact RequestResponse {
	-- time order of requests
	all r: Request | r not in  r.^(response.embeds)
	-- every response comes from a single request
	all r: Response | one response.r
	
	all r: Response | r.to = response.r.from and r.from = response.r.to
	}
	
fact Origin {
	// for a redirect, origin is same as request, else server
	all r: Response | r.origin = (r in Redirect implies response.r.origin else r.from)
	// embedded requests have the same origin as the response
	all r: Response, e: r.embeds | e.origin = r.origin
	// requests that are not embedded come from the client
	all r: Request | no embeds.r implies r.origin in r.from
	}

pred obeysOrigins (s: Server) {
	// request is only accepted if origin is itself or sender
	all r: Request | r.to =s implies r.origin = r.to or r.origin = r.from
	}

check {
	no good, bad: Server {
		no r: Request | r.to = bad and r.origin in Client				
		good.obeysOrigins
		some r: Request | r.to = good and r in bad.causes
		}
	} for 5
