//
// Test parsing and some evaluating
// TODO: more tests
//
package main

import (
	"bufio"
	"fmt"
	"github.com/siebenmann/smtpd"
	"strings"
	"testing"
)

var aParse = `
accept from a@b
@data reject to b@c or to fred or from a@b helo barney
stall from a@b not to d@e or (helo barney to charlie host fred)
reject helo somename from info@fbi.gov not to interesting@addr
reject helo-has none,nodots,helo from-has bad,quoted dns nodns
@message reject to-has garbage,route
accept dns good
reject dns noforward,inconsistent
accept ip 127.0.0.0/24 ip 127.0.0.10
reject ip 85.90.187.32/27 or host .edmpoint.com or ehlo .edmpoint.com
reject dnsbl sbl.spamhaus.org

# test all options for comma-separated things.
accept dns good or dns noforward,inconsistent,nodns or dns exists
accept tls on or tls off
accept from-has unqualified,route,quoted,noat,garbage,bad
accept to-has unqualified,route,quoted,noat,garbage,bad
accept helo-has helo,ehlo,none,nodots,bareip,properip,ip,myip,remip,otherip

`

func TestParse(t *testing.T) {
	rules, err := Parse(aParse + allSuccess)
	if err != nil {
		t.Fatalf("Error reported: %s\n", err)
	}
	if len(rules) == 0 {
		t.Fatalf("No parse error but nothing found")
	}
	for i := range rules {
		r1 := stringRule(rules[i])
		rls, err := Parse(r1)
		if err != nil || len(rls) != 1 {
			t.Fatalf("round tripping: %s\nerr: %s\nrules: %+v\n",
				r1, err, rls)
		}
		r2 := stringRule(rls[0])
		if r2 != r1 {
			t.Fatalf("failed to round trip.\nstart:\t%s\nend:\t%s\n", r1, r2)
		}
		//fmt.Printf("%s\n", rules[i].String())
	}
}

// This should be round-trippable.
func stringRule(r *Rule) string {
	if r.deferto != pAny {
		return fmt.Sprintf("%v %v %s", r.deferto, r.result,
			r.expr.String())
	} else {
		return fmt.Sprintf("%v %s", r.result, r.expr.String())
	}
}

var allSuccess = `
accept all
accept from jim@jones.com to joe@example.com not dns nodns
accept to joe@ from @.com
accept dns inconsistent dns noforward
accept helo-has ehlo tls on
accept not helo-has nodots from @.net or dns nodns or to @.com
accept helo-has nodots or (from @jones.com to @example.com)
accept from jim@jones.com to info@fbi.gov or to joe@example.com
accept not (from jim@ to @logan)
accept all or to jim@example.com
accept not from-has noat
accept not to-has quoted
# dns is not good because there are inconsistent and noforward stuff
accept not dns good
accept helo .ben
accept not helo-has bareip
accept host .b.c
accept host .f
# IP tests
accept ip 192.168.10.3 ip 192.168.10.0/24 ip /ips ip 192.168.010.003
accept not ip 127.0.0.10
`

var aList = `# This is a comment
INFO@FBI.GOV
root@

@example.com
postmaster@Example.Org
@.barney.net
# t
`
var ipList = `
127.0.0.0/8
# this should not generate an error even thought it would in the
# the actual rules.
not-valid
192.168.10.0/24
`

func setupFile(c *Context, name, conts string) error {
	reader := bufio.NewReader(strings.NewReader(conts))
	a, err := readList(reader)
	if err != nil {
		return err
	}
	c.files[name] = a
	return nil
}
func setupContext(t *testing.T) *Context {
	rd := &rDNSResults{[]string{"a.b.c", "d.e.f"}, []string{"g"},
		[]string{"h.i"}}
	st := &smtpTransaction{
		rdns:  rd,
		tlson: true,
		rip:   "192.168.10.3",
		lip:   "127.0.0.1",
	}
	c := &Context{trans: st,
		helocmd:  smtpd.EHLO,
		heloname: "joebob.ben",
		from:     "jim@jones.com",
		rcptto:   "joe@example.com",
		files:    make(map[string][]string),
		dnsbl:    make(map[string]*Result),
	}

	var rt, rf Result
	rt = true
	c.dnsbl["3.10.168.192.nosuch.domain."] = &rt
	c.dnsbl["3.10.168.192.notthere.domi."] = &rf

	err := setupFile(c, "/a/file", aList)
	if err != nil {
		t.Fatalf("Error during read: %#v", err)
	}
	err = setupFile(c, "/ips", ipList)
	if err != nil {
		t.Fatalf("Error during iplist read: %#v", err)
	}
	c.files["/empty"] = []string{}
	return c
}

func TestSuccess(t *testing.T) {
	c := setupContext(t)
	rules, err := Parse(allSuccess)
	if err != nil {
		t.Fatalf("error reported %s\n", err)
	}
	for i := range rules {
		c.rulemiss = false
		res := rules[i].expr.Eval(c)
		if !res {
			t.Errorf("rule did not succeed: %v\n", rules[i].expr)
		}
		if c.rulemiss {
			t.Errorf("rule set rulemiss: %v\n", rules[i].expr)
		}
	}
}

var inAddrs = []string{
	"INFO@FBI.GOV", "root@fred.com", "random@example.com",
	"postmaster@example.org", "root@example.com",
	"joe@fred.barney.net", "james@barney.net",
}
var outAddrs = []string{
	"fred@fbi.gov", "postmaster@example.net", "fred@random.org",
	"nosuch@james.net", "nosuch@barney.org",
}

func TestFileAddrMatching(t *testing.T) {
	c := setupContext(t)
	rules, e := Parse("accept from /a/file")
	if e != nil {
		t.Fatalf("parse error %v", e)
	}
	for _, in := range inAddrs {
		c.from = in
		if !rules[0].expr.Eval(c) {
			t.Errorf("address list does not match %s", in)
		}
	}
	for _, out := range outAddrs {
		c.from = out
		if rules[0].expr.Eval(c) {
			t.Errorf("address list matches %s", out)
		}
	}
}

func TestEmptyFile(t *testing.T) {
	c := setupContext(t)
	rules, e := Parse("accept from file:/empty")
	if e != nil {
		t.Fatalf("parse error %v", e)
	}
	rules[0].expr.Eval(c)
	if !c.rulemiss {
		t.Fatalf("rule did not set rulemiss")
	}
}

var heloTests = []struct {
	helo, match string
}{
	{"127.0.0.1", "helo-has bareip helo-has myip"},
	{"127.0.0.1", "not helo-has properip"},
	{"[127.0.0.1]", "helo-has properip helo-has myip"},
	{"[127.0.0.1]", "not helo-has bareip"},
	{"[192.168.10.3]", "helo-has remip"},
	{"[192.168.10.3]", "not helo-has myip"},
	{"[200.200.200.200]", "helo-has otherip"},
	{"127.10.100.10", "helo-has otherip"},
	{"[192.168.10.]", "not helo-has ip"},
	{"[]", "not helo-has ip"},
	{"192.168.10.", "not helo-has ip"},
	{"", "helo-has none"},
	{"", "helo-has nodots"},
	{"fred", "helo-has nodots"},
}

func TestHeloHas(t *testing.T) {
	c := setupContext(t)
	for _, s := range heloTests {
		c.heloname = s.helo
		rules, err := Parse(fmt.Sprintf("accept %s", s.match))
		if err != nil {
			t.Errorf("error parsing: %s\n\t%v\n", s.match, err)
			continue
		}
		if !rules[0].expr.Eval(c) {
			t.Errorf("HELO '%s' does not match: %s\n", s.helo,
				s.match)
		}
	}
}

// none of these lines should parse
var notParse = `helo
accept dns fred,barney
accept dns nodns, good
accept fred
accept host jones or
accept (host jones or)
accept host jones or barney
accept
accept not
accept not fred
accept not dns fred
accept host
accept ( host james
accept ( )
accept ip abcdef
accept ip ip
accept tls fred
accept or host fred
accept host fred or dns fred
accept dnsbl file:/a/somewhere
accept dnsbl host
accept dnsbl has-no-dots
@from accept to @fbi.gov`

func TestNotParse(t *testing.T) {
	for _, ln := range strings.Split(notParse, "\n") {
		rules, err := Parse(ln)
		if err == nil {
			t.Errorf("rule did not error out: '%s'\n\t%+v\n", ln, rules)
		}
	}
}

func TestDnsblHit(t *testing.T) {
	c := setupContext(t)
	rules, _ := Parse("accept dnsbl nosuch.domain")
	if !rules[0].expr.Eval(c) {
		t.Fatalf("did not hit in nosuch.domain")
	}
	if len(c.dnsblhit) != 1 && c.dnsblhit[0] != "nosuch.domain" {
		t.Fatalf("did not list nosuch.domain in c.dnsblhit:\n\t%#v\n", c.dnsblhit)
	}
	c.dnsblhit = []string{}
	rules, _ = Parse("accept dnsbl notthere.domi")
	if rules[0].expr.Eval(c) {
		t.Fatalf("did hit for notthere.domi")
	}
	if len(c.dnsblhit) != 0 {
		t.Fatalf("c.dnsblhit is not empty after notthere.domi test:\n\t%#v\n", c.dnsblhit)
	}
}
