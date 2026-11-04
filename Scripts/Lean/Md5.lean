module

/-!
# Scripts.Lean.Md5 — MD5 (RFC 1321), for the `md5 … before … after` line the price
scripts print.  Pure, over `ByteArray`; `#guard` rows on the RFC's test vectors.
-/

namespace Scripts.Lean.Md5

public section

private def s : Array UInt32 := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

private def k : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

private def rotl (x : UInt32) (c : UInt32) : UInt32 := (x <<< c) ||| (x >>> (32 - c))

/-- The message padded to a multiple of 64 bytes: `0x80`, zeros, the bit length (LE, 64-bit). -/
private def pad (m : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (m.size.toUInt64) * 8
  let mut b := m.push 0x80
  while b.size % 64 != 56 do b := b.push 0
  for i in [0:8] do b := b.push ((bitLen >>> (8 * i).toUInt64).toUInt8)
  return b

private def word (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i+1]!.toUInt32 <<< 8) ||| (b[i+2]!.toUInt32 <<< 16) ||| (b[i+3]!.toUInt32 <<< 24)

private def block (st : UInt32 × UInt32 × UInt32 × UInt32) (b : ByteArray) (off : Nat) :
    UInt32 × UInt32 × UInt32 × UInt32 := Id.run do
  let (a0, b0, c0, d0) := st
  let mut a := a0; let mut bb := b0; let mut c := c0; let mut d := d0
  for i in [0:64] do
    let (f, g) :=
      if i < 16 then ((bb &&& c) ||| ((~~~bb) &&& d), i)
      else if i < 32 then ((d &&& bb) ||| ((~~~d) &&& c), (5 * i + 1) % 16)
      else if i < 48 then (bb ^^^ c ^^^ d, (3 * i + 5) % 16)
      else (c ^^^ (bb ||| (~~~d)), (7 * i) % 16)
    let f := f + a + k[i]! + word b (off + 4 * g)
    a := d; d := c; c := bb
    bb := bb + rotl f s[i]!
  return (a0 + a, b0 + bb, c0 + c, d0 + d)

private def hexLE (x : UInt32) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for i in [0:4] do
    let byte := ((x >>> (8 * i).toUInt32) &&& 0xff).toNat
    out := out.push digits[byte / 16]! |>.push digits[byte % 16]!
  return out

/-- `hashlib.md5(bytes).hexdigest()`. -/
def md5 (m : ByteArray) : String := Id.run do
  let b := pad m
  let mut st : UInt32 × UInt32 × UInt32 × UInt32 := (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476)
  for i in [0:b.size / 64] do st := block st b (64 * i)
  let (a, bb, c, d) := st
  return hexLE a ++ hexLE bb ++ hexLE c ++ hexLE d

def md5Str (s : String) : String := md5 s.toUTF8

#guard md5Str "" == "d41d8cd98f00b204e9800998ecf8427e"
#guard md5Str "a" == "0cc175b9c0f1b6a831c399e269772661"
#guard md5Str "abc" == "900150983cd24fb0d6963f7d28e17f72"
#guard md5Str "message digest" == "f96b697d7cb7938d525a2f31aaf161d0"
#guard md5Str "abcdefghijklmnopqrstuvwxyz" == "c3fcd3d76192e4007dfb496cca67e13b"
#guard md5Str "12345678901234567890123456789012345678901234567890123456789012345678901234567890" == "57edf4a22be3c955ac49da2e2107b67a"

end

end Scripts.Lean.Md5
