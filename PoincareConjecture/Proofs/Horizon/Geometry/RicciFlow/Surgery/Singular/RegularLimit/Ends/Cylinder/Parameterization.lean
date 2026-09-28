import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.ClosedHalf
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

def halfAxial (side : Bool) (a t : ℝ) : ℝ :=
  if side then a + (1 - a) * t else a * (1 - t)

noncomputable def halfAxialInverse (side : Bool) (a s : ℝ) : ℝ :=
  if side then (s - a) / (1 - a) else 1 - s / a

theorem halfAxial_mem (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    halfAxial side a t ∈ if side then Ico a 1 else Ioc 0 a := by
  cases side
  · change 0 < a * (1 - t) ∧ a * (1 - t) ≤ a
    constructor
    · exact mul_pos ha.1 (sub_pos.mpr ht.2)
    · nlinarith [mul_nonneg ha.1.le ht.1]
  · change a ≤ a + (1 - a) * t ∧ a + (1 - a) * t < 1
    constructor
    · nlinarith [mul_nonneg (sub_pos.mpr ha.2).le ht.1]
    · nlinarith [mul_lt_mul_of_pos_left ht.2 (sub_pos.mpr ha.2)]

theorem halfAxial_mem_open (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : halfAxial side a t ∈ Ioo (0 : ℝ) 1 := by
  have h := halfAxial_mem side ha ht
  cases side
  · exact ⟨h.1, h.2.trans_lt ha.2⟩
  · exact ⟨ha.1.trans_le h.1, h.2⟩

theorem halfAxialInverse_mem (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ if side then Ico a 1 else Ioc 0 a) :
    halfAxialInverse side a s ∈ Ico (0 : ℝ) 1 := by
  cases side
  · change 0 ≤ 1 - s / a ∧ 1 - s / a < 1
    constructor
    · exact sub_nonneg.mpr ((div_le_one ha.1).mpr hs.2)
    · linarith [div_pos hs.1 ha.1]
  · change 0 ≤ (s - a) / (1 - a) ∧ (s - a) / (1 - a) < 1
    exact ⟨div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr ha.2).le,
      (div_lt_one (sub_pos.mpr ha.2)).mpr (by linarith [hs.2])⟩

theorem halfAxial_left_inverse (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (t : ℝ) : halfAxialInverse side a (halfAxial side a t) = t := by
  have ha0 := ne_of_gt ha.1
  have ha1 := ne_of_gt (sub_pos.mpr ha.2)
  cases side <;> dsimp [halfAxial, halfAxialInverse] <;> field_simp <;> ring

theorem halfAxial_right_inverse (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (s : ℝ) : halfAxial side a (halfAxialInverse side a s) = s := by
  have ha0 := ne_of_gt ha.1
  have ha1 := ne_of_gt (sub_pos.mpr ha.2)
  cases side <;> dsimp [halfAxial, halfAxialInverse] <;> field_simp <;> ring

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

def halfParameterization (Q : OpenCylinderModel U) (side : Bool) (a : ℝ) :
    RoundCylinderSpace → M := fun z => Q.coordinate (z.1, halfAxial side a z.2)

theorem halfParameterization_mem (Q : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (z : UnitTwoSphere × Ico (0 : ℝ) 1) :
    Q.halfParameterization side a (z.1, (z.2 : ℝ)) ∈ Q.closedTail side a := by
  exact ⟨(z.1, halfAxial side a z.2), ⟨mem_univ _, halfAxial_mem side ha z.2.property⟩, rfl⟩

noncomputable def halfHomeomorph (Q : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (UnitTwoSphere × Ico (0 : ℝ) 1) ≃ₜ Q.closedTail side a where
  toFun z := ⟨Q.halfParameterization side a (z.1, (z.2 : ℝ)),
    Q.halfParameterization_mem side ha z⟩
  invFun x := ((Q.inverse x).1, ⟨halfAxialInverse side a (Q.inverse x).2, by
    obtain ⟨hxU, hx⟩ := (Q.mem_closedTail_iff side ha).mp x.property
    apply halfAxialInverse_mem side ha
    have hdom := (Q.inverse_mem x hxU).2
    cases side
    · exact ⟨hdom.1, hx⟩
    · exact ⟨hx, hdom.2⟩⟩)
  left_inv z := by
    have hz : (z.1, halfAxial side a z.2) ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
      ⟨mem_univ _, halfAxial_mem_open side ha z.2.property⟩
    apply Prod.ext
    · change (Q.inverse (Q.coordinate (z.1, halfAxial side a z.2))).1 = z.1
      exact congrArg Prod.fst (Q.left_inverse hz)
    · apply Subtype.ext
      change halfAxialInverse side a
        (Q.inverse (Q.coordinate (z.1, halfAxial side a z.2))).2 = z.2
      rw [Q.left_inverse hz, halfAxial_left_inverse side ha]
  right_inv x := by
    apply Subtype.ext
    change Q.coordinate ((Q.inverse x).1,
      halfAxial side a (halfAxialInverse side a (Q.inverse x).2)) = x
    rw [halfAxial_right_inverse side ha]
    exact Q.right_inverse ((Q.mem_closedTail_iff side ha).mp x.property).1
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Q.coordinate_smooth.continuousOn.comp_continuous
    · cases side <;> dsimp [halfParameterization, halfAxial] <;> fun_prop
    · intro z
      exact ⟨mem_univ _, halfAxial_mem_open side ha z.2.property⟩
  continuous_invFun := by
    have hQ : Continuous (fun x : Q.closedTail side a => Q.inverse x) :=
      Q.inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
        (fun x => ((Q.mem_closedTail_iff side ha).mp x.property).1)
    apply Continuous.prodMk hQ.fst
    apply Continuous.subtype_mk
    cases side <;> dsimp [halfAxialInverse] <;> fun_prop

theorem halfHomeomorph_eq (Q : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (z : UnitTwoSphere × Ico (0 : ℝ) 1) :
    (Q.halfHomeomorph side ha z : M) =
      Q.halfParameterization side a (z.1, (z.2 : ℝ)) := rfl

theorem halfParameterization_proper (Q : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hclosed : IsClosed (Q.closedTail side a))
    {L : Set M} (hL : IsCompact L) :
    IsCompact {z : UnitTwoSphere × Ico (0 : ℝ) 1 |
      Q.halfParameterization side a (z.1, (z.2 : ℝ)) ∈ L} := by
  exact (hclosed.isProperMap_subtypeVal.comp
    (Q.halfHomeomorph side ha).isProperMap).isCompact_preimage hL

end PoincareConjecture.OpenCylinderModel
