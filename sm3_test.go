// Copyright (c) 2022, superwindstorm <fengwd.hc@gmail.com>
// All rights reserved.
// Use of this source code is governed by a BSD 3-Clause
// license that can be found in the LICENSE file.

package sm3

import (
	"fmt"
	"testing"
)

func BenchmarkSM3(b *testing.B) {
	buf := make([]byte, 10*1024*1024)
	b.SetBytes(int64(len(buf)))
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		Sum(buf)
	}
}

var tests = []struct {
	in   string
	want string
}{
	{"abc", "66c7f0f462eeedd9d1f2d46bdc10e4e24167c4875cf2f7a2297da02b8f4ba8e0"},
	{"abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd", "debe9ff92275b8a138604889c18e5a4d6fdb70e5387e5765293dcba39c0c5732"},
}

func TestSm3(t *testing.T) {
	for _, tst := range tests {
		dig := Sum([]byte(tst.in))
		if fmt.Sprintf("%x", dig) != tst.want {
			t.Fatalf("Test SM3(\"%s\") failed", tst.in)
		}
	}
}
