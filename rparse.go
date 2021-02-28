//
// Parse control rules using a standard hand written recursive descent
// parser.
//
// our grammar (not fully formal):
// a file is a sequence of rules; each rule ends at end of line
// or 'include FILENAME EOL'
//
// rule    -> [phase] what andl [with] EOL|EOF
// rclause -> andl [with] [rend rclause]
// rend    -> ';' EOL | ';'
// phase   -> @CONNECT | @HELO | @FROM | @TO | @DATA | @MESSAGE
// what    -> ACCEPT | REJECT | STALL
// andl    -> orl [andl]
// orl     -> term [OR orl]
// term    -> NOT term
//            ( andl )
//            ALL
//            TLS ON|OFF
//            DNS DNS-OPT[,DNS-OPT]
//            HELO-HAS HELO-OPT[,HELO-OPT]
//            FROM-HAS|TO-HAS ADDR-OPT[,ADDR-OPT]
//            FROM|TO|HELO|HOST arg
//            IP IPADDR|CIDR|FILENAME
//            DNSBL DOMAIN
//            SOURCE arg
//            DBL DOM-SRC[,DOM-SRC] DOMAIN
// with    -> WITH clause
// wclause -> wterm [wclause]
// wterm   -> MESSAGE arg
//            NOTE arg
//            SAVEDIR arg
//	      TLS-OPT OFF|NO-CLIENT
//            MAKE-YAKKER
// arg     -> VALUE
//            FILENAME
// arg actually is 'anything', keywords become values in it.
//
// TODO: SAVEDIR should take only a FILENAME

package main

import (
	"errors"
	"fmt"
	"net"
	"strings"
)

// our approach to lookahead is that parsing rules must deliberately
// consume the current token instead of getting it, looking at it,
// and then putting it back if they don't want it.
type parser struct {
	l       *lexer
	curtok  item
	currule *Rule
}

// consume the current token and advance to the next one
func (p *parser) consume() {
	// EOF is sticky because we pretend that it is an end of line
	// marker.
	if p.curtok.typ == itemEOF {
		return
	}
	if p.curtok.typ == itemError {
		// we panic because the rest of the code is supposed to not
		// do this. doing it anyways is an internal coding error.
		panic("trying to consume an error")
	}
	p.curtok = p.l.nextItem()
}

// isEol() is true at logical end of line, which includes EOF.
func (p *parser) isEol() bool {
	return p.curtok.typ == itemEOL || p.curtok.typ == itemEOF
}

// isERule() is true at logical end of line and at ';'
func (p *parser) isERule() bool {
	return p.isEol() || p.curtok.typ == itemSemicolon
}

// generate errors in various forms. the full form is for 'we expected Y
// but got X'. The other forms are for when the current token is not a
// useful part of the error.
func (p *parser) genError(msg string) error {
	ln, lp := p.l.lineInfo(p.curtok.pos)
	var fnd string
	switch p.curtok.typ {
	case itemEOF:
		fnd = "unexpected end of file"
	case itemEOL:
		fnd = "unexpected end of line"
	case itemError:
		// the real problem is that we hit a lexing error;
		// the msg we've been passed in is basically irrelevant.
		s := fmt.Sprintf("at line %d char %d: lexing error: %s",
			ln, lp, p.curtok.val)
		return errors.New(s)
	default:
		fnd = fmt.Sprintf("'%s'", p.curtok.val)
	}
	s := fmt.Sprintf("at line %d char %d: %s, found %s", ln, lp, msg, fnd)
	return errors.New(s)
}
func (p *parser) lineError(msg string) error {
	ln, _ := p.l.lineInfo(p.curtok.pos)
	s := fmt.Sprintf("at line %d: %s", ln, msg)
	return errors.New(s)
}
func (p *parser) posError(msg string) error {
	ln, lp := p.l.lineInfo(p.curtok.pos)
	s := fmt.Sprintf("at line %d char %d: %s", ln, lp, msg)
	return errors.New(s)
}

// parse: NOT term
func (p *parser) pNot() (expr Expr, err error) {
	p.consume()
	exr := &NotN{}
	exr.node, err = p.pTerm()
	if err != nil {
		return nil, err
	}
	if exr.node == nil {
		return nil, p.genError("expected something to NOT")
	}
	return exr, err
}

// parse: ( andl )
func (p *parser) pParen() (expr Expr, err error) {
	p.consume()
	er, err := p.pAndl()
	if err != nil {
		return nil, err
	}
	if p.curtok.typ != itemRparen {
		return nil, p.genError("expecting closing ')'")
	}
	if er == nil {
		return nil, p.posError("empty parenthesized expression")
	}
	p.consume()
	return er, err
}

// parse: arg
// this rejects special things like EOL.
func (p *parser) pArg() (arg string, err error) {
	if p.curtok.typ < itemHasValue {
		return "", p.genError("expected argument")
	}
	arg = p.curtok.val
	p.consume()
	return
}

// parse: domain
// a dnsbl domain necessarily contains dots, which means that it
// can only be an itemValue.
func (p *parser) pDomain() (arg string, err error) {
	if p.curtok.typ != itemValue {
		return "", p.genError("expected dnsbl domain")
	}
	arg = p.curtok.val
	if strings.IndexByte(arg, '.') == -1 {
		return "", p.posError("theoretical dnsbl domain contains no '.'")
	}
	// dot-terminate the domain for DNS lookups if it isn't already.
	if arg[len(arg)-1] != '.' {
		arg = arg + "."
	}
	p.consume()
	return
}

// parse: IP-ADDR|CIDR|FILENAME
// Unlike pArg, we know that IP addresses or CIDRs can never be
// tokenized as something other than an itemValue so we can
// immediately reject anything else.
func (p *parser) pIPArg() (arg string, err error) {
	switch p.curtok.typ {
	case itemFilename:
		arg = p.curtok.val
		p.consume()
		return
	case itemValue:
		arg = p.curtok.val
		if _, _, err := net.ParseCIDR(arg); err != nil && net.ParseIP(arg) == nil {
			return "", p.genError("argument is not a valid IP address or CIDR")
		}
		p.consume()
		return
	default:
		return "", p.genError("expected IP address, CIDR, or filename")

	}
}

// parse: ON|OFF
func (p *parser) pOnOff() (on bool, err error) {
	switch p.curtok.typ {
	case itemOn:
		p.consume()
		return true, nil
	case itemOff:
		p.consume()
		return false, nil
	default:
		return false, p.posError("expected on or off")
	}
}

// parse dbl arguments: HOST|EHLO|HELO|FROM DOMAIN
// we defer to pDomain() to pick up the domain.
func (p *parser) pDblArgs() (Option, string, error) {
	opt, err := p.pCommaOpts(dblMap)
	if err != nil {
		return opt, "", err
	}
	arg, err := p.pDomain()
	return opt, arg, err
}

// Minimum phase requirements for various things that cannot be evaluated
// at any time.
// This is used to set the overall phase requirement for the rule being
// generated
var minReq = map[itemType]Phase{
	itemFrom: pMfrom, itemHelo: pHelo, itemEhlo: pHelo, itemTo: pRto,
	itemFromHas: pMfrom, itemToHas: pRto, itemHeloHas: pHelo,
	itemSource: pMfrom,
	// We can't be sure that TLS is set up until we've seen a
	// MAIL FROM, because the first HELO/EHLO will be without
	// TLS and then they will STARTTLS again.
	itemTls: pMfrom,
	// itemDbl does not go in here because we need to handle it
	// specially. Rather than have a single priority (which would
	// have to be pMfrom), we determine the itemDbl priority on
	// the fly based on what domain sources it uses.
}

// Options for HELO-HAS, DNS, FROM-HAS, and TO-HAS. These map from lexer
// tokens to the option bitmap values that the token means.
var heloMap = map[itemType]Option{
	itemHelo: oHelo, itemEhlo: oEhlo, itemNone: oNone, itemNodots: oNodots,
	itemBareip: oBareip, itemProperip: oProperip, itemMyip: oMyip,
	itemRemip: oRemip, itemOtherip: oOtherip, itemIp: oIp,
	itemBogus: oBogus,
}
var dnsMap = map[itemType]Option{
	itemNodns: oNodns, itemInconsistent: oInconsist, itemNoforward: oNofwd,
	itemGood: oGood, itemExists: oExists,
}
var addrMap = map[itemType]Option{
	itemUnqualified: oUnqualified, itemRoute: oRoute, itemQuoted: oQuoted,
	itemNoat: oNoat, itemGarbage: oGarbage, itemBad: oBad,
	itemDomainValid: oDomainValid, itemDomainInvalid: oDomainInvalid,
	itemDomainTempfail: oDomainTempfail,
}

// That we map itemEhlo and itemHelo to the same option requires a special
// hack in optsReverse(). Doing better would be nice but probably requires
// using the 'stringer' command with custom processing (because of our
// 'o...' names).
var dblMap = map[itemType]Option{
	itemHost: oHost, itemEhlo: oEhlo, itemHelo: oEhlo, itemFrom: oFrom,
	itemAny: oAny,
}

// map from the starting token to the appropriate option map.
// NOTE: a specific map must be in this meta-map in order to have the
// Option.String() stuff work right; see optsReverse().
var mapMap = map[itemType]map[itemType]Option{
	itemFromHas: addrMap, itemToHas: addrMap,
	itemHeloHas: heloMap,
	itemDns:     dnsMap,
	itemDbl:     dblMap,
}

// parse: any variant of comma-separated options. We are called with
// a map that tells us which particular set of options to use and what
// they map to.
func (p *parser) pCommaOpts(m map[itemType]Option) (opt Option, err error) {
	for {
		ct := p.curtok.typ
		if m[ct] == oZero {
			return oZero, p.genError("expected valid option")
		}
		opt |= m[ct]
		p.consume()
		if p.curtok.typ == itemComma {
			p.consume()
		} else {
			break
		}
	}
	return opt, nil
}

// parse: a term. This is the big production at the bottom of the parse
// stack.
func (p *parser) pTerm() (expr Expr, err error) {
	ct := p.curtok.typ
	if ct == itemNot {
		return p.pNot()
	}
	if ct == itemLparen {
		return p.pParen()
	}

	// set phase requirement, if any.
	if minReq[ct] != pAny && minReq[ct] > p.currule.requires {
		p.currule.requires = minReq[ct]
	}

	// get argument
	// we split handling terms into separate 'get argument' and
	// 'generate expression node' operations because everything
	// that takes an argument has to check if the attempt to get
	// an argument ran into an error (and a number of things have
	// common operations but separate expression nodes).
	var arg string
	var ison bool
	var opts Option
	switch ct {
	case itemFrom, itemTo, itemHelo, itemEhlo, itemHost, itemSource:
		p.consume()
		arg, err = p.pArg()
	case itemIp:
		p.consume()
		arg, err = p.pIPArg()
	case itemDnsbl:
		p.consume()
		arg, err = p.pDomain()
	case itemTls:
		p.consume()
		ison, err = p.pOnOff()
	case itemAll:
		// directly handle 'all' here since it has no argument.
		p.consume()
		return &AllN{}, nil
	case itemFromHas, itemToHas, itemDns, itemHeloHas:
		p.consume()
		opts, err = p.pCommaOpts(mapMap[ct])
	case itemDbl:
		p.consume()
		opts, arg, err = p.pDblArgs()
	default:
		// The current token is not actually a valid term.
		// Since we are bottoming out on the parsing stack,
		// we need to start shuttling unrecognized things
		// back up it here.
		return nil, nil
	}

	if err != nil {
		return nil, err
	}
	// generate the expression node for the term now that we have a
	// valid argument.
	switch ct {
	case itemFrom:
		return newFromNode(arg), nil
	case itemTo:
		return newToNode(arg), nil
	case itemHelo, itemEhlo:
		return newHeloNode(arg), nil
	case itemHost:
		return newHostNode(arg), nil
	case itemSource:
		return newSourceNode(arg), nil
	case itemIp:
		return newIPNode(arg), nil
	case itemDnsbl:
		return &DNSblN{domain: arg}, nil
	case itemFromHas:
		return newFromHasOpt(opts), nil
	case itemToHas:
		return newToHasOpt(opts), nil
	case itemDns:
		return newDnsOpt(opts), nil
	case itemHeloHas:
		return newHeloOpt(opts), nil
	case itemTls:
		return &TlsN{on: ison}, nil
	case itemDbl:
		// Set minimum phase requirement specially, based on the
		// type of our lookup. We must check in this order so
		// that multiple sources pick the latest phase.
		var ph Phase
		switch {
		case (opts & oFrom) == oFrom:
			ph = pMfrom
		case (opts & oEhlo) == oEhlo:
			ph = pHelo
		default:
			ph = pAny
		}
		if ph != pAny && ph > p.currule.requires {
			p.currule.requires = ph
		}
		return newDblNode(opts, arg), nil
	default:
		// we should have trapped not-a-term above.
		// reaching here is a coding error.
		panic("should be impossible")
	}
}

// parse: orl -> term [OR orl]
func (p *parser) pOrl() (expr Expr, err error) {
	exp := &OrN{}
	er, err := p.pTerm()
	if err != nil {
		return nil, err
	}
	if p.curtok.typ != itemOr {
		return er, err
	}
	if er == nil {
		return nil, p.posError("empty left side of an or")
	}
	exp.left = er
	p.consume()
	er, err = p.pOrl()
	if err != nil {
		return nil, err
	}
	if er == nil {
		// We get here for two reasons: either we ran out of stuff
		// or we hit something that should have been a term but
		// isn't. We need to give different errors or I get really
		// confused.
		if p.isERule() || p.curtok.typ == itemRparen {
			return nil, p.posError("empty right side of an OR")
		}
		return nil, p.genError("expecting match operation")
	}
	exp.right = er
	return exp, err
}

// parse: andl -> orl [andl]
// We cheat by not recursing and simply looping.
func (p *parser) pAndl() (expr Expr, err error) {
	exp := &AndL{}
	for {
		er, err := p.pOrl()
		if err != nil {
			return nil, err
		}
		if er == nil {
			break
		}
		exp.nodes = append(exp.nodes, er)
	}
	// we suppress length-1 AndLs in favour of just returning the
	// underlying expression.
	// among other things, this makes us round-trip rules successfully;
	// otherwise we would accrete an extra andl node every round trip.
	switch {
	case len(exp.nodes) > 1:
		return exp, nil
	case len(exp.nodes) == 1:
		return exp.nodes[0], nil
	default:
		// this means we didn't actually parse anything because
		// the chain orl -> term wound up with term returning
		// nothing.
		return nil, nil
	}
}

// parse: wclause, including wterm
// we cheat twice: we parse both wclause and wterm in this, and we don't
// recurse.
func (p *parser) pWClause(rc *RClause) (bool, error) {
	var err error
	var arg string
	gotone := false
	for {
		ct := p.curtok.typ
		cv := p.curtok.val
		switch ct {
		case itemMessage, itemNote, itemSavedir:
			if rc.withs[cv] != "" {
				return gotone, p.posError(fmt.Sprintf("repeated '%s' option in with clause", cv))
			}
			p.consume()
			arg, err = p.pArg()
			if ct == itemNote {
				idx := strings.IndexByte(arg, '\n')
				if idx != -1 {
					return gotone, p.posError("note contains embedded newline")
				}
			}
		case itemTlsOpt:
			if _, ok := rc.withs[cv]; ok {
				return gotone, p.posError(fmt.Sprintf("repeated '%s' option in with clause", cv))
			}
			p.consume()
			arg, err = p.pArg()
			if arg != "off" && arg != "no-client" {
				return gotone, p.posError(fmt.Sprintf("illegal tls-opt option '%s' in with clause", arg))
			}
		case itemMakeYakker:
			if _, ok := rc.withs[cv]; ok {
				return gotone, p.posError(fmt.Sprintf("repeated '%s' option in with clause", cv))
			}
			p.consume()
			arg = ""
		default:
			return gotone, nil
		}
		if err != nil {
			return gotone, err
		}

		rc.withs[cv] = arg
		gotone = true
	}
}

// parse: [with]
func (p *parser) pWith(rc *RClause) error {
	if p.curtok.typ != itemWith {
		return nil
	}
	p.consume()
	good, err := p.pWClause(rc)
	switch {
	case err != nil:
		return err
	case p.isERule() && !good:
		return p.posError("empty with clause")
	case !p.isERule():
		return p.genError("expecting a with clause")
	default:
		return nil
	}
}

// parse: [phase]
var phases = map[itemType]Phase{
	itemAConnect: pConnect,
	itemAHelo:    pHelo, itemAFrom: pMfrom, itemATo: pRto, itemAData: pData,
	itemAMessage: pMessage,
}

func (p *parser) pPhase() {
	ct := p.curtok.typ
	if phases[ct] != pAny {
		p.currule.deferto = phases[ct]
		p.consume()
	}
}

// parse: rclause
// As is traditional, we cheat by not recursing.
func (p *parser) pRClause() error {
	var err error
	for {
		rc := newRClause()
		rc.expr, err = p.pAndl()
		if err != nil {
			return err
		}
		err = p.pWith(rc)
		if err != nil {
			return err
		}
		if !p.isERule() {
			// This is technically 'expecting end of line' but that
			// is not a useful error. What it really means is that
			// we ran into something that is not an operation down
			// in the depths of pTerm and it bubbled up to here.
			return p.genError("expecting an operation or 'with'")
		}
		if rc.expr == nil {
			return p.lineError("rule needs at least one operation, perhaps 'all'")
		}
		p.currule.addclause(rc)
		if p.currule.result == aNoresult && len(rc.withs) == 0 {
			return p.lineError("'set-with' rule with no with options")
		}

		// At this point, the current token must be ';' or EOF|EOL.
		// If it is EOF|EOL, we are done parsing rule clauses and
		// we escape.
		if p.isEol() {
			return nil
		}

		// current token must be ';'. Eat it and continue
		// accumulating more rule clauses, optionally eating
		// an EOL immediately after it too.
		p.consume()
		if p.curtok.typ == itemEOL {
			p.consume()
		}
	}
}

// Parse a rule. A rule is [phase] what [orl]
// *rules are the only thing that consume end of line markers*
// the lexer does not feed us empty lines, so there must be a
// word start in here. As a result we ignore this possibility.
var actions = map[itemType]Action{
	itemAccept: aAccept, itemReject: aReject, itemStall: aStall,
	itemSetWith: aNoresult,
}

func (p *parser) pRule() (r *Rule, err error) {
	p.currule = &Rule{}

	// bail if we are sitting on an EOF.
	if p.curtok.typ == itemEOF {
		return nil, nil
	}

	p.pPhase()
	ct := p.curtok.typ
	if actions[ct] == aError {
		return nil, p.genError("expecting an action")
	}
	p.currule.result = actions[ct]
	p.consume()

	err = p.pRClause()
	if err != nil {
		return nil, err
	}

	// pRClause can only return a nil err if we are sitting on an
	// acceptable EOL or EOF. The only remaining error is a phase
	// error of explicit phase < required phase.
	// we check for errors before consuming the EOL so that
	// the line numbers come out right in error messages.
	// TODO: we should really save the position at the start of the rule
	// for this; for multi-line rules we report the line number of the
	// *end* of the rule.
	if p.currule.deferto != pAny && p.currule.deferto < p.currule.requires {
		return nil, p.lineError("rule specifies a phase lower than its operations require so we cannot satisfy the phase requirement")
	}
	p.consume()
	return p.currule, err
}

// parse: 'include FILENAME EOL'
// we enter with the 'include' as the current token, so we must immediately
// consume it.
func (p *parser) pInclude() ([]*Rule, error) {
	p.consume()
	fname, err := p.pArg()
	if err != nil {
		return nil, err
	}
	rules, err := loadRules(fname)
	if err != nil {
		return rules, p.lineError(fmt.Sprintf("while including '%s': %s", fname, err))
	}
	if !p.isEol() {
		return rules, p.genError("expecting end of line")
	}
	p.consume()
	return rules, nil
}

// a file is a sequence of rules and/or include statements.
func (p *parser) pFile() (rules []*Rule, err error) {
	for {
		if p.curtok.typ == itemInclude {
			rl, e := p.pInclude()
			if e != nil {
				return rules, e
			}
			rules = append(rules, rl...)
			continue
		}
		r, e := p.pRule()
		if e != nil {
			return rules, e
		}
		if r != nil {
			rules = append(rules, r)
		}
		if p.curtok.typ == itemEOF {
			break
		}
	}
	return rules, nil
}

// Parse an input string into a set of rules and a possible error.
// If there is an error, you must ignore the rules.
func Parse(input string) (rules []*Rule, err error) {
	l := lex(input)
	p := &parser{l: l}
	// we must prime the current token with the first token in the
	// file.
	p.curtok = l.nextItem()
	r, e := p.pFile()
	// A parse error may have left the lexer with unconsumed input.
	// We need to explicitly drain the lexer to deal with this and
	// to terminate the goroutine.
	l.drain()
	return r, e
}
