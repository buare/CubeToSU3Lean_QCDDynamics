import CubeToSU3.GaugeLocal

/-!
# 格點規範:立方體上的 Wilson 圈

The continuum gauge module works over `Spacetime = Fin 4 → ℝ`, which is
contractible.  Over a contractible base every principal bundle is trivial, so no
construction there can produce a non-zero Chern class: non-triviality is not
something one can derive, it requires a different base.  Mathlib has no
principal bundles and no characteristic classes, so the continuum route to
non-triviality is out of reach.

The lattice route is not.  A connection on a lattice is a group element per
directed edge, holonomy around a closed loop is a *finite product* of group
elements, and its trace is gauge invariant.  Everything is finite, decidable,
and needs nothing beyond multiplication in `SU(3)`.

This file puts the lattice on the cube `Q₃` itself: eight vertices, twelve
edges, six faces.  That is the first object on which the discrete branch
(`Cube`, `QianKunAxis`, `RootMatch`) and the gauge branch meet.

The content is the lattice counterpart of `fieldStrength_gauge_covariant`:

    W (U^g) v b c = g v * W U v b c * (g v)⁻¹

the plaquette holonomy is conjugated at its base vertex, so its trace does not
move.  The proof is pure group multiplication — the `g`'s at the three other
corners cancel in adjacent pairs, and the two flips commute so the far corner
is reached the same way round either side.

`pureGauge_plaquette_one` is the converse direction that gives the word
"non-trivial" its meaning: a connection of the form `U v b = g v * (g (v⊕b))⁻¹`
has every plaquette equal to `1`.  Such a connection is flat — it is `1` in
disguise.  A connection whose plaquettes are *not* all `1` carries curvature
that no choice of gauge can remove.

Nothing here is a physical claim.

**角色須知:這裡的立方體是底空間,不是內部結構。**

專案其他地方(`QianKunAxis`、`RootMatch`、`Weyl`、`WeylReal`)把立方體當作
**纖維側的內部結構**:三個爻是 `su(3)` 的三個色方向,乾坤軸挑出一個 Cartan
方向,六個非軸頂點是 `A₂` 的六個根,`S₄` 是 `SU(3)` 的一個特選有限子群。那一
側和時空毫無關係。

本檔案反過來,把 `Q₃` 當作**底空間**——每條有向稜掛一個群元素,繞一個面走一
圈。在纖維叢的語言裡,底空間與纖維是兩個不能互換的角色,而這裡用的是前者。

所以這一塊是**格點規範理論的一個小示範**,不是「立方體的內部結構長出了曲率」。
它證明的定理都成立,而且格點規範理論本身是有意義的數學;但它不是
`QianKunAxis → RootMatch` 那條主線的自然延伸,讀者不該把兩者接在一起讀。

真正的格點規範理論用的是四維時空格子(`32⁴` 以上),而 `Q₃` 是三維的八個點,
既不是時空、也裝不下任何強子。這裡不做任何物理計算的宣稱。
-/

namespace CubeToSU3.Lattice

open CubeToSU3 CubeToSU3.Continuous

/-! ## The cube as a lattice -/

/-- Flip the `b`-th yao of vertex `v`: the edge of `Q₃` leaving `v` in
    direction `b`.  The `% 8` keeps the bound proof trivial; the XOR of two
    numbers below eight is already below eight, so it changes nothing. -/
def flip (v : Fin 8) (b : Fin 3) : Fin 8 :=
  ⟨(v.val ^^^ 2 ^ b.val) % 8, by omega⟩

theorem flip_flip : ∀ (v : Fin 8) (b : Fin 3), flip (flip v b) b = v := by decide

/-- Flips in different directions commute: the far corner of a face is reached
    the same way round either side.  This is what makes the middle pair of
    gauge factors cancel below. -/
theorem flip_comm : ∀ (v : Fin 8) (b c : Fin 3),
    flip (flip v b) c = flip (flip v c) b := by decide

theorem flip_ne : ∀ (v : Fin 8) (b : Fin 3), flip v b ≠ v := by decide

/-! ## Connections and gauge transformations -/

/-- A lattice connection: one group element per directed edge.  The reversed
    edge carries the inverse, so only the `2^b` direction is stored. -/
def Connection := Fin 8 → Fin 3 → SU3

/-- A lattice gauge transformation: one group element per vertex. -/
def LatticeGauge := Fin 8 → SU3

/-- The action on a connection: `U v b ↦ g v * U v b * (g (v ⊕ b))⁻¹`. -/
def gaugeAct (g : LatticeGauge) (U : Connection) : Connection :=
  fun v b => g v * U v b * (g (flip v b))⁻¹

/-- The pure-gauge connection built from `g`: transport from `v` to `v ⊕ b` is
    just the change of frame.  These are the flat connections. -/
def pureGauge (g : LatticeGauge) : Connection :=
  fun v b => g v * (g (flip v b))⁻¹

/-! ## Plaquette holonomy -/

/-- Holonomy around the face at `v` spanned by directions `b` and `c`:
    `v → v⊕b → v⊕b⊕c → v⊕c → v`, the last two steps traversed backwards. -/
def plaquette (U : Connection) (v : Fin 8) (b c : Fin 3) : SU3 :=
  U v b * U (flip v b) c * (U (flip v c) b)⁻¹ * (U v c)⁻¹

/-- **The lattice counterpart of gauge covariance.**  A gauge transformation
    conjugates the plaquette holonomy by the group element at its base vertex;
    the other three corners cancel in adjacent pairs. -/
theorem plaquette_gaugeAct (g : LatticeGauge) (U : Connection)
    (v : Fin 8) (b c : Fin 3) :
    plaquette (gaugeAct g U) v b c = g v * plaquette U v b c * (g v)⁻¹ := by
  unfold plaquette gaugeAct
  have hbc : flip (flip v b) c = flip (flip v c) b := flip_comm v b c
  rw [hbc]
  group

/-- Hence the trace of the holonomy is gauge invariant: it is an observable of
    the connection, not of the chosen frame. -/
theorem trace_plaquette_gaugeAct (g : LatticeGauge) (U : Connection)
    (v : Fin 8) (b c : Fin 3) :
    Matrix.trace (((plaquette (gaugeAct g U) v b c : SU3) : M3C))
      = Matrix.trace (((plaquette U v b c : SU3) : M3C)) := by
  rw [plaquette_gaugeAct]
  -- the coercion of a product of group elements is the product of the
  -- coercions, definitionally; spelling it out keeps `M3C` and `SU3` from
  -- being multiplied together
  have hcoe : ((g v * plaquette U v b c * (g v)⁻¹ : SU3) : M3C)
      = ((g v : SU3) : M3C) * ((plaquette U v b c : SU3) : M3C)
        * (((g v)⁻¹ : SU3) : M3C) := rfl
  have hinv : (((g v)⁻¹ : SU3) : M3C) * ((g v : SU3) : M3C) = 1 := by
    have h : ((g v)⁻¹ * g v : SU3) = 1 := inv_mul_cancel _
    calc (((g v)⁻¹ : SU3) : M3C) * ((g v : SU3) : M3C)
        = (((g v)⁻¹ * g v : SU3) : M3C) := rfl
      _ = ((1 : SU3) : M3C) := by rw [h]
      _ = 1 := rfl
  rw [hcoe, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

/-! ## Flatness -/

/-- **A pure-gauge connection has trivial holonomy.**  This is what makes
    "non-trivial" mean something: a connection whose plaquettes are not all `1`
    carries curvature that no change of frame can remove. -/
theorem pureGauge_plaquette_one (g : LatticeGauge) (v : Fin 8) (b c : Fin 3) :
    plaquette (pureGauge g) v b c = 1 := by
  unfold plaquette pureGauge
  have hbc : flip (flip v b) c = flip (flip v c) b := flip_comm v b c
  rw [hbc]
  group

/-- The trivial connection is pure gauge, hence flat. -/
theorem trivial_plaquette_one (v : Fin 8) (b c : Fin 3) :
    plaquette (fun _ _ => (1 : SU3)) v b c = 1 := by
  unfold plaquette
  group

/-- Flatness of a connection: every face has trivial holonomy. -/
def IsFlat (U : Connection) : Prop :=
  ∀ (v : Fin 8) (b c : Fin 3), plaquette U v b c = 1

theorem pureGauge_isFlat (g : LatticeGauge) : IsFlat (pureGauge g) :=
  fun v b c => pureGauge_plaquette_one g v b c

/-- Flatness is a gauge-invariant condition. -/
theorem isFlat_gaugeAct (g : LatticeGauge) (U : Connection) (h : IsFlat U) :
    IsFlat (gaugeAct g U) := by
  intro v b c
  rw [plaquette_gaugeAct, h v b c, mul_one, mul_inv_cancel]

/-! ## Axiom audit -/

#print axioms flip_flip
#print axioms flip_comm
#print axioms plaquette_gaugeAct
#print axioms trace_plaquette_gaugeAct
#print axioms pureGauge_plaquette_one
#print axioms isFlat_gaugeAct

end CubeToSU3.Lattice
