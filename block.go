// Copyright (c) 2022, superwindstorm <fengwd.hc@gmail.com>
// All rights reserved.
// Use of this source code is governed by a BSD 3-Clause
// license that can be found in the LICENSE file.

package sm3

import (
	"encoding/binary"
	"math/bits"
)

// Size is the bytes of digest
const Size = 32

// BlockSize is the bytes of each block
const BlockSize = 64

const (
	chunk = 64
	init0 = 0x7380166f
	init1 = 0x4914b2b9
	init2 = 0x172442d7
	init3 = 0xda8a0600
	init4 = 0xa96f30bc
	init5 = 0x163138aa
	init6 = 0xe38dee4d
	init7 = 0xb0fb0e4e
)

func (d *digest) checkSum() [32]byte {
	// Write will change d.len
	length := d.len << 3
	var buf [chunk * 2]byte
	n := copy(buf[:], d.x[:d.nx])
	buf[n] = 0x80
	n++
	nn := chunk
	if n > chunk-8 {
		nn += chunk
	}
	binary.BigEndian.PutUint64(buf[nn-8:nn], length)
	block(d, buf[:nn])

	var result [Size]byte
	for i, s := range d.h {
		binary.BigEndian.PutUint32(result[i*4:], s)
	}
	return result
}

// Block functions
func blockGeneric(dig *digest, p []byte) {
	var w [68]uint32
	h0, h1, h2, h3, h4, h5, h6, h7 := dig.h[0], dig.h[1], dig.h[2], dig.h[3], dig.h[4], dig.h[5], dig.h[6], dig.h[7]

	for len(p) >= chunk {
		// Can interlace the computation of w with the
		// rounds below if needed for speed.
		for i := 0; i < 16; i++ {
			j := i * 4
			w[i] = uint32(p[j])<<24 | uint32(p[j+1])<<16 | uint32(p[j+2])<<8 | uint32(p[j+3])
		}
		for i := 16; i < 68; i++ {
			t := w[i-16] ^ w[i-9] ^ bits.RotateLeft32(w[i-3], 15)
			w[i] = t ^ bits.RotateLeft32(t, 15) ^ bits.RotateLeft32(t, 23) ^ bits.RotateLeft32(w[i-13], 7) ^ w[i-6]
		}

		a, b, c, d, e, f, g, h := h0, h1, h2, h3, h4, h5, h6, h7
		for i := 0; i < 16; i++ {
			x := bits.RotateLeft32(a, 12)
			ss1 := bits.RotateLeft32(x+e+rotT[i], 7)
			tt1 := (a ^ b ^ c) + d + (ss1 ^ x) + (w[i] ^ w[i+4])
			tt2 := (e ^ f ^ g) + h + ss1 + w[i]

			d, c, b, a = c, bits.RotateLeft32(b, 9), a, tt1
			h, g, f, e = g, bits.RotateLeft32(f, 19), e, tt2^bits.RotateLeft32(tt2, 9)^bits.RotateLeft32(tt2, 17)
		}

		for i := 16; i < 64; i++ {
			x := bits.RotateLeft32(a, 12)
			ss1 := bits.RotateLeft32(x+e+rotT[i], 7)
			tt1 := ((a & b) | (b & c) | (a & c)) + d + (ss1 ^ x) + (w[i] ^ w[i+4])
			tt2 := ((e & f) | (^e & g)) + h + ss1 + w[i]

			d, c, b, a = c, bits.RotateLeft32(b, 9), a, tt1
			h, g, f, e = g, bits.RotateLeft32(f, 19), e, tt2^bits.RotateLeft32(tt2, 9)^bits.RotateLeft32(tt2, 17)
		}

		p = p[chunk:]
		h0 ^= a
		h1 ^= b
		h2 ^= c
		h3 ^= d
		h4 ^= e
		h5 ^= f
		h6 ^= g
		h7 ^= h
	}
	dig.h[0], dig.h[1], dig.h[2], dig.h[3], dig.h[4], dig.h[5], dig.h[6], dig.h[7] = h0, h1, h2, h3, h4, h5, h6, h7
}

// rotate of Tj: rotT[i] = Tj << (j mod 32)
var rotT = []uint32{
	0x79cc4519,
	0xf3988a32,
	0xe7311465,
	0xce6228cb,
	0x9cc45197,
	0x3988a32f,
	0x7311465e,
	0xe6228cbc,
	0xcc451979,
	0x988a32f3,
	0x311465e7,
	0x6228cbce,
	0xc451979c,
	0x88a32f39,
	0x11465e73,
	0x228cbce6,
	0x9d8a7a87,
	0x3b14f50f,
	0x7629ea1e,
	0xec53d43c,
	0xd8a7a879,
	0xb14f50f3,
	0x629ea1e7,
	0xc53d43ce,
	0x8a7a879d,
	0x14f50f3b,
	0x29ea1e76,
	0x53d43cec,
	0xa7a879d8,
	0x4f50f3b1,
	0x9ea1e762,
	0x3d43cec5,
	0x7a879d8a,
	0xf50f3b14,
	0xea1e7629,
	0xd43cec53,
	0xa879d8a7,
	0x50f3b14f,
	0xa1e7629e,
	0x43cec53d,
	0x879d8a7a,
	0x0f3b14f5,
	0x1e7629ea,
	0x3cec53d4,
	0x79d8a7a8,
	0xf3b14f50,
	0xe7629ea1,
	0xcec53d43,
	0x9d8a7a87,
	0x3b14f50f,
	0x7629ea1e,
	0xec53d43c,
	0xd8a7a879,
	0xb14f50f3,
	0x629ea1e7,
	0xc53d43ce,
	0x8a7a879d,
	0x14f50f3b,
	0x29ea1e76,
	0x53d43cec,
	0xa7a879d8,
	0x4f50f3b1,
	0x9ea1e762,
	0x3d43cec5,
}
