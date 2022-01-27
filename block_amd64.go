// Copyright (c) 2022, superwindstorm <fengwd.hc@gmail.com>
// All rights reserved.
// Use of this source code is governed by a BSD 3-Clause
// license that can be found in the LICENSE file.

package sm3

import (
	"golang.org/x/sys/cpu"
)

var useAVX2 = cpu.X86.HasAVX2 && cpu.X86.HasBMI2

//go:noescape
func blockAsmAVX2(dig *digest, p []byte)

var block func(dig *digest, p []byte)

func init() {
	if useAVX2 {
		block = blockAsmAVX2
	} else {
		block = blockGeneric
	}
}

// export
var BlockAsmAVX2 = blockAsmAVX2
var BlockGeneric = blockGeneric
