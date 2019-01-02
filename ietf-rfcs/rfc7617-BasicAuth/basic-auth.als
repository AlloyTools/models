
// https://tools.ietf.org/html/rfc7617 Basic Authentication


sig BasicChallenge extends Challenge {
	realm	: Realm,
	charset	: lone Charset
} {
	name = "Basic"
	(RealmParameter & parameters).realm = Realm
	one charset implies (CharsetParameter & parameters).charset = charset
}


sig BasicCredentials extends Credentials {
	user_id		: String,
	password	:	String,
	charset		: lone Charset
} {
	name = "Basic"
	let     s = user_id.cat[":"].cat[password], 
	        c = one charset implies charset else OTHER_CHARSET, 
			p =  (Token68Parameter  & parameters ){

			p.value = c.binary[s]

	}
}

fun String.cat[ other : String ] : String {
	other // wrong! but cannot concatenate
}

// https://tools.ietf.org/html/rfc7235 Authentication

one sig SC_UNAUTHORIZED_401 									extends ResponseCode {}


sig AuthorizationServer extends Server {
	protectionSpaces		: set Realm
}

abstract sig Challenge extends AuthScheme {}
abstract sig Credentials extends AuthScheme {}


sig WWWAuthenticate extends Header {
	challenges		:	seq Challenge
} {
	name = "WWW-Authenticate"
	some challenges
}

sig Authorization extends Header {
	credentials	: Credentials
} {
	name = "Authorization"
}

abstract sig AuthScheme {
	name			: String,
	parameters		: set Parameter
} {
	some (Token68Parameter & parameters) implies one parameters
}

abstract sig Parameter {
}

sig Binary {
}

abstract sig Token68Parameter extends Parameter {
	value   : Binary
}

abstract sig AuthParam extends Parameter {
	name    : String
}

sig Realm  {}

sig RealmParameter extends AuthParam {
	realm : Realm
} {
	name = "realm"
}

abstract sig Charset {
	maps : String -> Binary
}

fun Charset.binary[ s : String ] : Binary {
	this.maps[s] 
}



one sig ASCII extends Charset {}
one sig ISO8859 extends Charset {}
one sig UTF16 extends Charset {}
one sig UTF8 extends Charset {}
one sig OTHER_CHARSET extends Charset {}

sig CharsetParameter extends AuthParam {
	charset : Charset
} {
	name = "charset"
}


fact WWWAuthenticateChallengeResponse {
	all r : HttpResponse | 
		r.response = SC_UNAUTHORIZED_401 implies some (r.headers.elems & WWWAuthenticate )
}


// https://tools.ietf.org/html/rfc7230 (HTTP 1.1) and further

sig Server {}


sig Path {}
one sig EmptyPath extends Path {
}

sig URI {
	host			:	Server,
	path			: Path
}

enum Method { GET, POST, PUT, DELETE, PATCH, OPTIONS, HEAD }

enum ResponseCode {
	SC_OK_200, SC_NOT_FOUND_404, SC_TEMP_REDIRECT_302
}

abstract sig Body {}


sig HttpRequest {
	method		: Method,
	url				: URI,
	headers 	: seq Header,
	body			: lone Body
}

sig HttpResponse {
	response	: ResponseCode,
	headers 	: seq Header,
	payload		: lone Body,
}


abstract sig Header {
	name			: String
}


fact fixup {
	all a : Authorization | a in HttpRequest.headers.elems
	all a : WWWAuthenticate | a in HttpResponse.headers.elems
	all b : Credentials | b in Authorization.credentials
	all b : Challenge | b in Authorization.credentials
	all b : Body | lone r : HttpRequest | r.body = b
}

run {} for 3
