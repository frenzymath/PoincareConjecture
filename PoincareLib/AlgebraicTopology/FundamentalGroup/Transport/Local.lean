import PoincareLib.AlgebraicTopology.FundamentalGroup.Subdivision.Path

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/LocalPathTransport.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Coherent local transport on paths

Hatcher's van Kampen proof (Theorem 1.20, pp. 43-46) evaluates small path
segments in a target group. The local condition is that the two routes
around each supported square have the same value. Degenerate squares give
the subdivision identity. This is used for Morgan--Tian Proposition 15.3.
-/

set_option autoImplicit false

open Set
open scoped unitInterval

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- Affine restriction to a parameter interval in Hatcher's van Kampen
subdivision, Theorem 1.20 (pp. 43-46). -/
def intervalSubpath (p : C(unitInterval, X)) (a b : unitInterval) : C(unitInterval, X) :=
  p.comp (Path.parameterSegment a b).toContinuousMap

/-- Evaluation of an affine parameter restriction (Hatcher
Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem intervalSubpath_apply (p : C(unitInterval, X)) (a b t : unitInterval) :
    p.intervalSubpath a b t = p (Icc.convexComb a b t) := rfl

/-- Restricting to the whole unit interval changes nothing
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem intervalSubpath_zero_one (p : C(unitInterval, X)) :
    p.intervalSubpath 0 1 = p := by
  ext t
  simp

/-- A degenerate restriction is a constant path
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem intervalSubpath_self (p : C(unitInterval, X)) (a : unitInterval) :
    p.intervalSubpath a a = .const _ (p a) := by
  ext t
  simp

/-- A horizontal edge of a parameterized square
(Hatcher Theorem 1.20, pp. 45-46). -/
def horizontalPath (H : C(unitInterval × unitInterval, X)) (t : unitInterval) :
    C(unitInterval, X) := H.comp ⟨fun s => (s, t), by fun_prop⟩

/-- A vertical edge of a parameterized square
(Hatcher Theorem 1.20, pp. 45-46). -/
def verticalPath (H : C(unitInterval × unitInterval, X)) (s : unitInterval) :
    C(unitInterval, X) := H.comp ⟨fun t => (s, t), by fun_prop⟩

/-- Evaluation of a horizontal edge (Hatcher Theorem 1.20 construction,
pp. 45-46). -/
@[simp] theorem horizontalPath_apply (H : C(unitInterval × unitInterval, X))
    (s t : unitInterval) : H.horizontalPath t s = H (s, t) := rfl

/-- Evaluation of a vertical edge (Hatcher Theorem 1.20 construction,
pp. 45-46). -/
@[simp] theorem verticalPath_apply (H : C(unitInterval × unitInterval, X))
    (s t : unitInterval) : H.verticalPath s t = H (s, t) := rfl

/-- Restrict a square to a rectangle by affine coordinates
(Hatcher Theorem 1.20, pp. 45-46). -/
def rectangleRestrict (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) : C(unitInterval × unitInterval, X) :=
  H.comp ⟨fun z => (Icc.convexComb a b z.1, Icc.convexComb c d z.2),
    ((Icc.continuous_convexComb a b).comp continuous_fst).prodMk
      ((Icc.continuous_convexComb c d).comp continuous_snd)⟩

/-- Evaluation of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (z : unitInterval × unitInterval) :
    H.rectangleRestrict a b c d z =
      H (Icc.convexComb a b z.1, Icc.convexComb c d z.2) := rfl

/-- The bottom edge of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_bottom (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).horizontalPath 0 =
      (H.horizontalPath c).intervalSubpath a b := by
  ext t
  simp

/-- The top edge of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_top (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).horizontalPath 1 =
      (H.horizontalPath d).intervalSubpath a b := by
  ext t
  simp

/-- The left edge of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_left (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).verticalPath 0 =
      (H.verticalPath a).intervalSubpath c d := by
  ext t
  simp

/-- The right edge of a rectangular restriction
(Hatcher Theorem 1.20 construction, pp. 45-46). -/
@[simp] theorem rectangleRestrict_right (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) :
    (H.rectangleRestrict a b c d).verticalPath 1 =
      (H.verticalPath b).intervalSubpath c d := by
  ext t
  simp

end ContinuousMap

/-- Local group-valued transport for Hatcher's rectangle proof of
van Kampen (Theorem 1.20, pp. 43-46). Values on paths not contained in any
cover member are irrelevant; global transport is constructed by subdivision. -/
structure LocalPathTransport {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (G : Type*) [Monoid G] where
  /-- Values of small paths, with arbitrary values allowed on other paths
  (Hatcher Theorem 1.20 construction, pp. 43-46). -/
  value : C(unitInterval, X) → G
  /-- Constant paths have trivial transport
  (Hatcher Theorem 1.20 construction, pp. 43-46). -/
  map_const : ∀ x, value (.const _ x) = 1
  /-- Transport commutes around every square supported in one cover member
  (Hatcher Theorem 1.20 construction, pp. 43-46). -/
  square : ∀ (H : C(unitInterval × unitInterval, X)) (i : ι),
    (∀ z, H z ∈ U i) →
      value (H.horizontalPath 0) * value (H.verticalPath 1) =
        value (H.verticalPath 0) * value (H.horizontalPath 1)

namespace LocalPathTransport

variable {X ι G : Type*} [TopologicalSpace X] {U : ι → Set X} [Monoid G]

private theorem convexComb_mem {a b x y : unitInterval}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (t : unitInterval) :
    Icc.convexComb x y t ∈ Icc a b := by
  rcases le_total x y with h | h
  · exact ⟨hx.1.trans (Icc.le_convexComb h t), (Icc.convexComb_le h t).trans hy.2⟩
  · rw [← Icc.convexComb_symm y x]
    exact ⟨hy.1.trans (Icc.le_convexComb h _), (Icc.convexComb_le h _).trans hx.2⟩

/-- A degenerate square proves the ordered subdivision identity for a
supported interval (Hatcher Theorem 1.20, pp. 43-46). -/
theorem interval_mul (L : LocalPathTransport U G) (p : C(unitInterval, X))
    {a b c : unitInterval} (hab : a ≤ b) (hbc : b ≤ c) (i : ι)
    (hp : MapsTo p (Icc a c) (U i)) :
    L.value (p.intervalSubpath a b) * L.value (p.intervalSubpath b c) =
      L.value (p.intervalSubpath a c) := by
  let H : C(unitInterval × unitInterval, X) :=
    p.comp ⟨fun z => Icc.convexComb (Icc.convexComb a b z.1)
      (Icc.convexComb a c z.1) z.2,
      Icc.continuous_convexComb_prod.comp
        (((Icc.continuous_convexComb a b).comp continuous_fst).prodMk
          (((Icc.continuous_convexComb a c).comp continuous_fst).prodMk continuous_snd))⟩
  have h := L.square H i (fun z => hp (convexComb_mem
    ⟨Icc.le_convexComb hab z.1, (Icc.convexComb_le hab z.1).trans hbc⟩
    ⟨Icc.le_convexComb (hab.trans hbc) z.1, Icc.convexComb_le (hab.trans hbc) z.1⟩ z.2))
  have hbottom : H.horizontalPath 0 = p.intervalSubpath a b := by ext t; simp [H]
  have hright : H.verticalPath 1 = p.intervalSubpath b c := by ext t; simp [H]
  have hleft : H.verticalPath 0 = .const _ (p a) := by ext t; simp [H]
  have htop : H.horizontalPath 1 = p.intervalSubpath a c := by ext t; simp [H]
  simpa only [hbottom, hright, hleft, htop, L.map_const, one_mul] using h

end LocalPathTransport
