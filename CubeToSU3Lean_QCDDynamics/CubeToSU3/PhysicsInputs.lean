/-!
# Explicit external inputs

This module intentionally contains no claimed derivation of particle physics.
The four propositions name the additional assumptions needed to connect the
finite algebraic core to a physical model. They are kept separate from the
mathematical theorems in CubeToSU3.Core.

Using Unit as an axiom type would be misleading: Unit is already inhabited, so
such an axiom carries no assumption. These propositions are opaque until a
physical model gives them precise content.
-/

namespace CubeToSU3.PhysicsInputs

opaque PiHolonomyPostulate : Prop
opaque FlavorDictionaryPostulate : Prop
opaque BornRulePostulate : Prop
opaque PWavePhaseSpacePostulate : Prop

/-- Geometric quantization input: the selected face holonomy is π. -/
axiom pi_holonomy : PiHolonomyPostulate

/-- Interpretation input: selected modes are identified with physical flavours. -/
axiom flavor_dictionary : FlavorDictionaryPostulate

/-- Quantum-mechanical input: probabilities are norm-squares of amplitudes. -/
axiom born_rule : BornRulePostulate

/-- Dynamical input: the relevant partial width carries the p³ factor. -/
axiom p_wave_phase_space : PWavePhaseSpacePostulate

/-!
## Three further inputs, added after the chirality audit

`CubeToSU3.Cube.cube_index_zero` proves that the cube's own chirality operator
has vanishing index. So the left/right asymmetry of the weak interaction is not
a consequence of the finite core; it has to be named. Two neighbouring gaps are
named at the same time.
-/

opaque ChiralityPostulate : Prop
opaque ColorFactorPostulate : Prop
opaque WeakDirectionPostulate : Prop

/-- **P3.** Lorentz chirality exists, and the flavour triplet is assigned to the
left-handed Weyl field. Proved *not* to follow from the finite core: see
`CubeToSU3.cube_index_zero`. Note that the anomaly theorems in
`CubeToSU3.Anomalies` are only constraining once this is assumed, since a
vectorlike assignment cancels every anomaly automatically. -/
axiom chirality : ChiralityPostulate

/-- **Gap 1.** The colour factor `SU(3)_c` is a separate input. A single `A₂`
has rank two; the Standard Model gauge group has rank four, and the missing
rank is exactly `SU(3)_c`. The cube supplies one `A₂`, not two. -/
axiom color_factor : ColorFactorPostulate

/-- **A7.** The three `A₁` subsystems of the hexagon are geometrically
equivalent; selecting one of them as the weak direction breaks `S₃` to `Z₂` and
is not determined by the cube. -/
axiom weak_direction : WeakDirectionPostulate

/-!
## A10, added after the cross-product reformulation

`CubeToSU3.D_is_cross` shows `D v = v × 1`. Consequently `D` commutes with the
whole circle of rotations about the pole, not merely with the order-three
subgroup: `R(v × 1) = (Rv) × (R1) = (Rv) × 1` for every such `R`. So `D` alone
cannot distinguish the cube from a triangle, or from any configuration obtained
by turning about the pole; and `D = P - P²` is one member of the family
`R(θ) - R(-θ) = -(2 sin θ / √3) D`, singled out only because `θ = 120°` makes
the coefficient one.

Selecting `Z₃` out of that circle is therefore an input, on the same footing as
A7. Both are the same move: a continuous symmetry broken to a discrete one,
with nothing in the construction performing the break.
-/

opaque DiscretizationPostulate : Prop

/-- **A10.** The reduction of the pole's rotational symmetry to the order-three
subgroup -- equivalently, the choice `θ = 120°`, equivalently the choice of the
cube's eight corners rather than any other configuration about the same axis. -/
axiom discretization : DiscretizationPostulate

/-!
## A note on 遊年, which is not an input

`CubeToSU3.YouNian` shows that the traditional 遊年 tables are exactly the
Cayley table of `(Z₂)³`. That is a checked fact about a transcribed table, not
a postulate, so it takes no axiom. It is worth recording here only because it
answers a question the rest of the ledger raises: the cube's group structure
does carry real content, but `YouNian.D_not_group_hom` shows `D` destroys that
structure, so the content is unavailable to the algebra. Two complete and
disjoint structures on one set of eight points.
-/

/-- A single, inspectable ledger of every non-mathematical input in this file. -/
theorem physical_ledger :
    PiHolonomyPostulate ∧ FlavorDictionaryPostulate ∧
    BornRulePostulate ∧ PWavePhaseSpacePostulate ∧
    ChiralityPostulate ∧ ColorFactorPostulate ∧ WeakDirectionPostulate ∧
    DiscretizationPostulate :=
  ⟨pi_holonomy, flavor_dictionary, born_rule, p_wave_phase_space,
   chirality, color_factor, weak_direction, discretization⟩

end CubeToSU3.PhysicsInputs
