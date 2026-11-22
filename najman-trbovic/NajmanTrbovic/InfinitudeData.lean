module

public import NajmanTrbovic.NormData

/-! Small-prime lifts and polynomial Bézout coefficients for Theorem 2.12. -/

@[expose] public section

namespace NajmanTrbovic

inductive InfinitudeCase where
  | n28
  | n30
  | n33
  | n35
  deriving DecidableEq, Repr

def InfinitudeCase.normCase : InfinitudeCase → NormCase
  | .n28 => .n28_neg7
  | .n30 => .n30_5
  | .n33 => .n33_neg11
  | .n35 => .n35_5

structure BezoutCertificate where
  left : List ℤ
  right : List ℤ
  constant : ℤ

def InfinitudeCase.certificate : InfinitudeCase → BezoutCertificate
  | .n28 => ⟨[-142, 1260, -1980, 1440, -720],
      [-66, 287, -525, 550, -300, 120], 224⟩
  | .n30 => ⟨[-298012, -1209884, -2044370, -1706824, -762404, -173114, -15048],
      [42676, 230038, 491421, 562197, 358161, 129995, 24931, 1881], 11520⟩
  | .n33 => ⟨[122848, -158160, 821532, -254848, 323056, 4672, 56560],
      [3927, -226831, 147082, -235477, 51606, -58057, -584, -7070], 3881196⟩
  | .n35 => ⟨[14736, -9056, 21204, 10744, 22100, 19200, -5328],
      [2441, -5149, 3089, -5527, -2235, -3727, -2733, 666], 24500⟩

def InfinitudeCase.smallWitness : InfinitudeCase → ℕ → ℤ
  | .n28, 7 => 2
  | .n28, 11 => 3
  | .n28, 23 => 5
  | .n28, 29 => 4
  | .n28, 37 => 5
  | .n28, 43 => 10
  | .n28, 53 => 8
  | .n28, 67 => 6
  | .n28, 71 => 16
  | .n28, 79 => 7
  | .n30, 5 => 1
  | .n30, 11 => 1
  | .n30, 19 => 3
  | .n30, 29 => 4
  | .n30, 31 => 1
  | .n30, 41 => 5
  | .n30, 59 => 5
  | .n30, 61 => 16
  | .n30, 71 => 7
  | .n30, 79 => 17
  | .n30, 89 => 8
  | .n33, 3 => 0
  | .n33, 5 => 2
  | .n33, 11 => 0
  | .n33, 23 => 5
  | .n33, 31 => 10
  | .n33, 37 => 14
  | .n33, 47 => 7
  | .n33, 53 => 13
  | .n33, 59 => 8
  | .n33, 67 => 25
  | .n33, 71 => 15
  | .n33, 89 => 37
  | .n33, 97 => 30
  | .n35, 5 => 2
  | .n35, 11 => 3
  | .n35, 19 => 1
  | .n35, 29 => 5
  | .n35, 31 => 12
  | .n35, 41 => 6
  | .n35, 59 => 19
  | .n35, 61 => 17
  | .n35, 71 => 8
  | .n35, 79 => 29
  | .n35, 89 => 9
  | _, _ => 0

end NajmanTrbovic
