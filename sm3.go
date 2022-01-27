// Copyright (c) 2022, superwindstorm <fengwd.hc@gmail.com>
// All rights reserved.
// Use of this source code is governed by a BSD 3-Clause
// license that can be found in the LICENSE file.

// Package sm3 implements the sm3 hash algorithms as defined
// in GB/T 32905-2016. SM3 has already been accepted by ISO
// in ISO/IEC 10118-3:2018.
//

package sm3

import (
	"hash"
)

type digest struct {
	h   [8]uint32
	x   [chunk]byte
	nx  int
	len uint64
}

// New returns a new hash.Hash computing the SM3 checksum.
func New() hash.Hash {
	d := new(digest)
	d.Reset()
	return d
}

// Reset reset the states
func (d *digest) Reset() {
	d.h[0] = init0
	d.h[1] = init1
	d.h[2] = init2
	d.h[3] = init3
	d.h[4] = init4
	d.h[5] = init5
	d.h[6] = init6
	d.h[7] = init7
	d.nx = 0
	d.len = 0
}

// Size returns the size of hash digest
func (d *digest) Size() int { return Size }

// BlockSize return the bytes of one block
func (d *digest) BlockSize() int { return BlockSize }

func (d *digest) Write(p []byte) (nn int, err error) {
	nn = len(p)
	d.len += uint64(nn)
	if d.nx > 0 {
		n := copy(d.x[d.nx:], p)
		d.nx += n
		if d.nx == chunk {
			block(d, d.x[:])
			d.nx = 0
		}
		p = p[n:]
	}

	if len(p) >= chunk {
		n := len(p) &^ (chunk - 1)
		block(d, p[:n])
		p = p[n:]
	}
	if len(p) > 0 {
		d.nx = copy(d.x[:], p)
	}
	return
}

// Sum returns the digest in bytes. The intenal states remain the same
func (d *digest) Sum(in []byte) []byte {
	// checkSum will change intenal states, so make a copy
	d0 := *d
	hash := d0.checkSum()
	return append(in, hash[:]...)
}

// Sum returns the SM3 checksum of the data.
func Sum(data ...[]byte) [Size]byte {
	var d digest
	d.Reset()
	for _, x := range data {
		d.Write(x)
	}
	return d.checkSum()
}
