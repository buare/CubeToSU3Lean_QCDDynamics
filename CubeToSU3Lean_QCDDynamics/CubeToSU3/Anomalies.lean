/-!
# Anomaly cancellation, in exact integer arithmetic

The candidate spectrum of the 331-type model is finite, so its five local gauge
anomalies and the mixed gravitational anomaly are finite sums of integers once
the `U(1)_X` charges are cleared of denominators. Every `X` below is stored as
`3X`, which is an integer; each anomaly sum is homogeneous in `X`, so vanishing
of the scaled sum is equivalent to vanishing of the original.

Nothing here depends on `CubeToSU3.Core`: this file is about the fermion
content, not about the cube. It is kept separate on purpose, so that the audit
in `Check.lean` shows the two are independent.

The one thing worth stressing: **anomaly cancellation only constrains chiral
theories.** A vectorlike assignment cancels automatically. So these theorems
are conditional on the chirality input `P3` recorded in `PhysicsInputs`, and
they are not evidence that the cube produced chirality.
-/

namespace CubeToSU3.Anomalies

/-- One left-handed Weyl multiplet.

* `mult` counts individual Weyl fermions, used for the cubic and gravitational
  sums.
* `x3` is three times the `U(1)_X` charge.
* `colorUnits` counts `SU(3)_c` triplets or antitriplets; the quadratic index is
  the same for both, so a plain count is correct.
* `flavorUnits` counts `SU(3)_L` triplets or antitriplets, likewise.
* `triality` is `+1` for `3`, `-1` for `3bar`, `0` for a flavour singlet. Only
  the cubic `SU(3)_L` anomaly distinguishes them.
-/
structure Multiplet where
  name : String
  mult : Int
  x3 : Int
  colorUnits : Int
  flavorUnits : Int
  triality : Int
deriving Repr

/-- Two quark families in `(3_c, 3_L, X = -1/3)` with their conjugate singlets. -/
def quarkFamilyA (tag : String) : List Multiplet :=
  [ ⟨"Q" ++ tag,  9, -1, 3, 3,  1⟩,
    ⟨"uc" ++ tag, 3, -2, 1, 0,  0⟩,
    ⟨"dc" ++ tag, 3,  1, 1, 0,  0⟩,
    ⟨"Jc" ++ tag, 3,  4, 1, 0,  0⟩ ]

/-- The third quark family, in the conjugate representation
`(3_c, 3bar_L, X = 2/3)`. This is the family the cube's `ker D` singles out. -/
def quarkFamilyB : List Multiplet :=
  [ ⟨"Q3",  9,  2, 3, 3, -1⟩,
    ⟨"dc3", 3,  1, 1, 0,  0⟩,
    ⟨"uc3", 3, -2, 1, 0,  0⟩,
    ⟨"Jc3", 3, -5, 1, 0,  0⟩ ]

/-- Three lepton families in `(1, 3bar_L, X = 0)`. -/
def leptonFamily (tag : String) : List Multiplet :=
  [ ⟨"L" ++ tag, 3, 0, 0, 1, -1⟩ ]

/-- The full left-handed content of the candidate model. -/
def content : List Multiplet :=
  quarkFamilyA "1" ++ quarkFamilyA "2" ++ quarkFamilyB ++
  leptonFamily "1" ++ leptonFamily "2" ++ leptonFamily "3"

def sumOver (f : Multiplet → Int) : Int :=
  (content.map f).foldl (· + ·) 0

/-- Cubic `SU(3)_L` anomaly. -/
def anomaly_L3 : Int := sumOver fun m => m.flavorUnits * m.triality

/-- Mixed `[SU(3)_L]^2 U(1)_X`. -/
def anomaly_L2X : Int := sumOver fun m => m.flavorUnits * m.x3

/-- Mixed `[SU(3)_c]^2 U(1)_X`. -/
def anomaly_c2X : Int := sumOver fun m => m.colorUnits * m.x3

/-- Mixed gravitational `grav^2 U(1)_X`. -/
def anomaly_gravX : Int := sumOver fun m => m.mult * m.x3

/-- Cubic `[U(1)_X]^3`. -/
def anomaly_X3 : Int := sumOver fun m => m.mult * m.x3 * m.x3 * m.x3

theorem L3_vanishes : anomaly_L3 = 0 := by decide
theorem L2X_vanishes : anomaly_L2X = 0 := by decide
theorem c2X_vanishes : anomaly_c2X = 0 := by decide
theorem gravX_vanishes : anomaly_gravX = 0 := by decide
theorem X3_vanishes : anomaly_X3 = 0 := by decide

/-- All five anomalies of the candidate model vanish. -/
theorem all_anomalies_vanish :
    anomaly_L3 = 0 ∧ anomaly_L2X = 0 ∧ anomaly_c2X = 0 ∧
    anomaly_gravX = 0 ∧ anomaly_X3 = 0 := by
  decide

/-- The `U(1)_X` charges are traceless over the three families, which is what
the projector construction in section 9 of the notes claims. Stored as `3X`,
the three family charges are `-1, -1, 2`. -/
theorem family_charges_traceless : (-1 : Int) + (-1) + 2 = 0 := by decide

/-! ## The exhaustive part

With `nQ` quark families in `3_L` and `nL` lepton families in `3_L` (the rest in
`3bar_L`), the cubic `SU(3)_L` anomaly is `3(2 nQ - 3) + (2 nL - 3)`. Over the
sixteen admissible pairs there are exactly two solutions, and they are conjugate
to one another. This is a genuinely exhaustive claim, so it is worth having the
kernel check it rather than a person.
-/

def cubicCondition (nQ nL : Int) : Int := 3 * (2 * nQ - 3) + (2 * nL - 3)

theorem cubic_solutions_exhaustive :
    ∀ q : Fin 4, ∀ l : Fin 4,
      cubicCondition q.val l.val = 0 ↔
        ((q.val = 2 ∧ l.val = 0) ∨ (q.val = 1 ∧ l.val = 3)) := by
  decide

/-- The two solutions are related by conjugating every representation, so up to
an overall reversal the anomaly condition forces exactly the split
"two quark families one way, the remaining family the other". This is the
structure the cube's `ker D + im D = 1 + 2` decomposition supplies -- but only
once chirality has been assumed. -/
theorem two_plus_one_forced :
    cubicCondition 2 0 = 0 ∧ cubicCondition 1 3 = 0 ∧
    cubicCondition 0 0 ≠ 0 ∧ cubicCondition 3 3 ≠ 0 := by
  decide

end CubeToSU3.Anomalies
