import CubeToSU3.Cube
import CubeToSU3.Anomalies
import CubeToSU3.ClosedWalks

/-!
# The other half of the ledger: what was tried and ruled out

`PhysicsInputs.lean` records what is *assumed*. This file records what was
*attempted and killed*, together with the theorem that kills it.

Both halves are needed. A ledger that only lists surviving assumptions makes a
project look cleaner than it is, because the dead ends leave no trace and can
be re-proposed later by someone who has forgotten them -- including the person
who proposed them the first time.

Three of the four entries below are backed by an actual theorem, so the kernel
will now refuse to let the candidate be reintroduced silently. The fourth is a
methodological rejection, not a mathematical one, and is marked as such.
-/

namespace CubeToSU3.Rejected

/-! ## Entry 1: `f/v = 6√6` fails the weight criterion

A dimensionless ratio of two vacuum expectation values must be unchanged when
every cube-derived matrix is rescaled by a common factor. Reason: with
`D_F = v K_H + f K_Σ` linear in the `K`s, rescaling `K → λK` moves the
stationary point from `(v, f)` to `(v/λ, f/λ)`, leaving `f/v` fixed. So any
formula proposed for `f/v` must be homogeneous of degree zero.

The candidate `ρ(A)·√(Tr A²) = 6√6` is homogeneous of degree **two**. Working
with its square keeps everything in the integers: `(6√6)² = 216`.
-/

/-- A candidate built as (spectral radius)² × Tr M², with the spectral radius
squared supplied as a parameter so that no real numbers are needed. -/
def candidateSquared (rho2 : Int) (M : Fin 8 → Fin 8 → Int) : Int :=
  rho2 * trace8 (mul8 M M)

/-- For the cube: `ρ(A)² = 9`, `Tr A² = 24`, so the square of the candidate is
`216 = (6√6)²`. -/
theorem candidate_value : candidateSquared 9 A = 216 := by decide

/-- The hexagon-area rewrite `3√3 · √8` is not a different candidate. Squared,
`(3√3)² · (√8)² = 27 · 8 = 216`: it is literally the same number, so it inherits
the same rejection. -/
theorem area_rewrite_is_same_number : 27 * 8 = 216 := by decide

/-- Under `A → cA` both factors pick up `c²`, so the square of the candidate
picks up `c⁴` and the candidate itself has weight two. -/
theorem trace_smul_sq (c : Int) (M : Fin 8 → Fin 8 → Int) :
    trace8 (mul8 (smul8 c M) (smul8 c M)) = c * c * trace8 (mul8 M M) := by
  simp only [trace8, mul8, smul8]
  simp [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem candidate_has_weight_two (c rho2 : Int) (M : Fin 8 → Fin 8 → Int) :
    candidateSquared (c * c * rho2) (smul8 c M) =
      (c * c) * (c * c) * candidateSquared rho2 M := by
  simp only [candidateSquared, trace_smul_sq]
  simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

/-- A concrete integer witness: doubling the matrix multiplies the square of the
candidate by sixteen. `216 → 3456`. -/
theorem candidate_not_invariant :
    candidateSquared (2 * 2 * 9) (smul8 2 A) = 16 * 216 := by decide

/-- What scale invariance actually means for a numerical invariant. -/
def ScaleInvariant (F : (Fin 8 → Fin 8 → Int) → Int) : Prop :=
  ∀ (c : Int) (M : Fin 8 → Fin 8 → Int), F (smul8 c M) = F M

/-- `Tr M²` is not scale invariant, so nothing built from it with a nonzero net
weight can be a ratio of vacuum expectation values. -/
theorem traceSq_not_scale_invariant :
    ¬ ScaleInvariant (fun M => trace8 (mul8 M M)) := by
  intro h
  have hEq : trace8 (mul8 (smul8 2 A) (smul8 2 A)) = trace8 (mul8 A A) := h 2 A
  revert hEq
  decide

/-! ## Entry 2: chirality from edge phases (axiom A4) is impossible

Axiom A4 attaches a common phase plane to each directed path. The hope was that
this could produce a chiral spectrum. It cannot: the cube's chiral index is
fixed by the sizes of the two bipartite sectors and is therefore independent of
any edge weight or phase.

`CubeToSU3.sectors_balanced` gives four and four; `CubeToSU3.cube_index_zero`
gives trivial kernels in both sectors. The rejection is recorded here so that
"give the edges phases and chirality will appear" cannot be proposed again
without contradicting a proved theorem.
-/

theorem chirality_from_phases_rejected :
    ((List.finRange 8).countP (fun i => S i == 1) =
     (List.finRange 8).countP (fun i => S i == -1)) ∧
    (∀ v : Vec8, hop v = Vec8.zero → v = Vec8.zero) := by
  refine ⟨by decide, fun v h => cube_kernel_trivial v h⟩

/-! ## Entry 3: the universal `Γ_□` rule fails on leptons

Section 9 assigns quark families by the geometric sign `Γ_□`, giving two
families one way and one the other. If the same rule is applied to leptons it
gives `n_L = 2`, and then the cubic condition does not vanish. So `Γ_□` is
applied selectively: it does real work on quarks and is switched off for
leptons. That is a gap in the derivation, and here it is an integer fact.
-/

open CubeToSU3.Anomalies in
/-- Applying `Γ_□` to leptons as well gives `n_L = 2`, and the cubic `SU(3)_L`
anomaly is then `+4`, not zero. The rule cannot be universal. -/
theorem gamma_rule_not_universal :
    cubicCondition 2 2 = 4 ∧ cubicCondition 2 2 ≠ 0 := by decide

open CubeToSU3.Anomalies in
/-- The two surviving assignments both need `n_L ∈ {0, 3}`, i.e. all three
lepton families on the same side. Nothing geometric in the notes selects that. -/
theorem lepton_assignment_is_input :
    ∀ l : Fin 4, cubicCondition 2 l.val = 0 → l.val = 0 := by decide

/-! ## Entry 4: free parameters are not legitimate targets

This entry has no theorem, and saying so is the point.

In the minimal 331 completion, `f` is fixed by `μ_ρ²/λ_ρ` and `v` by `μ²/λ`,
with the two sets of scalar-potential parameters independent. So `f/v` is a
free parameter: the theory does not require it to take any particular value.
The same holds for `v` itself, for `m_H`, and for every Yukawa ratio.

Predicting a free parameter is not a hard problem, it is an ill-posed one. The
contrast is `sin²θ_W`, which any embedding of `SU(2)×U(1)` into a simple group
*must* fix, and which is therefore a legitimate target.

This is a methodological rejection, so it is recorded as inspectable data
rather than dressed up as a theorem. Turning it into an axiom would be worse
than useless: it would suggest something was being assumed, when in fact
something is being declined.
-/

/-! ## Entry 6: the closed-walk route as a whole

`ClosedWalks.lean` follows the prescribed order -- axioms first -- and reaches a
negative result stronger than the weight criterion. The spectrum of `Qₙ` is
binomial and carries exactly one parameter, `n`. Under the isospectrality axiom
nothing outside the spectrum is visible, so every permitted invariant is a
function of `n` alone. The route emits one number, the dimension, and the
dimension was an input.

This closes a whole family rather than a candidate. Recorded so that "try
`Tr A⁴/(Tr A²)²`, or `Tr A⁶`, or some combination" cannot be proposed again as
though it were an open direction.

Note the scope. The isospectrality axiom is what does the work, and it is a
real restriction: `YouNian.lean` (the group law), Hamiltonian paths, and
`CrossProduct.lean` (the embedding) are all invisible to `Tr Aᵏ` and untouched.
-/

open CubeToSU3.ClosedWalks in
/-- The whole closed-walk output for the cube, and it is the input dimension. -/
theorem closed_walk_route_gives_only_the_dimension :
    3 * (3 * (T2 * T2) - 8 * T4) = 2 * (T2 * T2) ∧
    (∀ n : Fin 10,
      (n.val : Int) * (3 * (T2 * T2) - 8 * T4) = 2 * (T2 * T2) ↔ n.val = 3) := by
  refine ⟨dimension_recovered, dimension_unique⟩

structure Entry where
  candidate : String
  criterion : String
  killedBy : String
deriving Repr

def rejectionLedger : List Entry :=
  [ ⟨"f/v = ρ(A)·√(Tr A²) = 6√6",
     "E-1 weight: homogeneous of degree 2, must be 0",
     "candidate_has_weight_two, traceSq_not_scale_invariant"⟩,
    ⟨"f/v = (hexagon area)·√|Q₃| = 3√3·√8",
     "E-1 weight: same number as above, 216 when squared",
     "area_rewrite_is_same_number"⟩,
    ⟨"chirality from edge phases (axiom A4)",
     "index fixed by sector sizes, phase independent",
     "chirality_from_phases_rejected, cube_index_zero"⟩,
    ⟨"Γ_□ applied universally, including leptons",
     "gives n_L = 2, cubic anomaly = 4 ≠ 0",
     "gamma_rule_not_universal"⟩,
    ⟨"f/v, v, m_H, Yukawa ratios as prediction targets",
     "E-3 determinacy: free parameters, not determined quantities",
     "no theorem: methodological, see Entry 4"⟩,
    ⟨"the closed-walk route in general (any function of Tr A^k)",
     "spec(Q_n) is binomial: one parameter n, and n was an input",
     "closed_walk_route_gives_only_the_dimension"⟩ ]

/-- Six entries, five of them backed by a theorem. -/
theorem ledger_size : rejectionLedger.length = 6 := by decide

end CubeToSU3.Rejected
