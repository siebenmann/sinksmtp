//
// Do very crude tests of ValidDomain().
//

package main

import (
	"testing"
)

func TestBasicResults(t *testing.T) {
	// Has MX entry
	a, err := ValidDomain("gmail.com")
	if a != dnsGood || err != nil {
		t.Fatalf("gmail.com bad: valid %v / %v\n", a, err)
	}
	// Has A record but no MX (so far, this is crude)
	a, err = ValidDomain("www.google.com")
	if a != dnsGood || err != nil {
		t.Fatalf("www.google.com: valid %v / %v\n", a, err)
	}

	// Has a null MX. Yeah, this is not a great test either.
	// Really we need a synthetic resolver of our own with test
	// data, but that's too much work.
	a, err = ValidDomain("yahoo.net")
	if a != dnsBad || err == nil {
		t.Fatalf("yahoo.net: valid %v / %v\n", a, err)
	}

	// This either. fbi.org has a MX localhost, at least as of
	// 2017-05-21 and some time before.
	a, err = ValidDomain("fbi.org")
	if a != dnsBad || err == nil {
		t.Fatalf("fbi.org: valid %v / %v\n", a, err)
	}

	// No such thing.
	a, err = ValidDomain("nosuchdomain.fred")
	if a != dnsBad || err == nil {
		t.Fatalf("nosuchdomain.fred: valid %v / %v\n", a, err)
	}
}
