import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereSides

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : TopologicalSpace.Opens M}

theorem exists_three_isotopic_sphere_coordinates
    (T : OpenCylinderModel (U : Set M)) {S C H : Set M}
    (hS : SmoothSphereIsotopicIn (U : Set M) S T.middleSphere)
    (hC : SmoothSphereIsotopicIn (U : Set M) C T.middleSphere)
    (hH : SmoothSphereIsotopicIn (U : Set M) H T.middleSphere) :
    ∃ phiS phiC phiH : U ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1),
      (∀ x : U, cylinderSignedHeight phiS x = 0 ↔ (x : M) ∈ S) ∧
      (∀ x : U, cylinderSignedHeight phiC x = 0 ↔ (x : M) ∈ C) ∧
      (∀ x : U, cylinderSignedHeight phiH x = 0 ↔ (x : M) ∈ H) ∧
      (∃ x : U, cylinderSignedHeight phiS x < 0 ∧
        cylinderSignedHeight phiC x < 0 ∧ cylinderSignedHeight phiH x < 0) ∧
      (∃ x : U, 0 < cylinderSignedHeight phiS x ∧
        0 < cylinderSignedHeight phiC x ∧ 0 < cylinderSignedHeight phiH x) := by
  obtain ⟨phiS, aS, bS, haS, haShalf, hbShalf, hbS, hzS, htS⟩ :=
    T.exists_isotopic_sphere_coordinates hS
  obtain ⟨phiC, aC, bC, haC, _haChalf, _hbChalf, hbC, hzC, htC⟩ :=
    T.exists_isotopic_sphere_coordinates hC
  obtain ⟨phiH, aH, bH, haH, _haHhalf, _hbHhalf, hbH, hzH, htH⟩ :=
    T.exists_isotopic_sphere_coordinates hH
  let a := min aS (min aC aH)
  let b := max bS (max bC bH)
  have ha : 0 < a := lt_min haS (lt_min haC haH)
  have haHalf : a < 1 / 2 := (min_le_left _ _).trans_lt haShalf
  have hbHalf : 1 / 2 < b := hbShalf.trans_le (le_max_left _ _)
  have hb : b < 1 := max_lt hbS (max_lt hbC hbH)
  refine ⟨phiS, phiC, phiH,
    fun x => sub_eq_zero.trans (hzS x),
    fun x => sub_eq_zero.trans (hzC x),
    fun x => sub_eq_zero.trans (hzH x), ?_, ?_⟩
  · obtain ⟨x, hx⟩ := T.tail_nonempty false ha (haHalf.trans (by norm_num))
    obtain ⟨hxU, hxa⟩ :=
      (T.mem_tail_iff_m28 false ha (haHalf.trans (by norm_num))).mp hx
    have hxS := hxa.trans_le (min_le_left aS (min aC aH))
    have hxC := hxa.trans_le ((min_le_right aS (min aC aH)).trans (min_le_left aC aH))
    have hxH := hxa.trans_le ((min_le_right aS (min aC aH)).trans (min_le_right aC aH))
    refine ⟨⟨x, hxU⟩, ?_, ?_, ?_⟩
    · change ((phiS ⟨x, hxU⟩).2 : ℝ) - 1 / 2 < 0
      rw [htS ⟨x, hxU⟩ (Or.inl hxS)]
      exact sub_neg.mpr (hxa.trans haHalf)
    · change ((phiC ⟨x, hxU⟩).2 : ℝ) - 1 / 2 < 0
      rw [htC ⟨x, hxU⟩ (Or.inl hxC)]
      exact sub_neg.mpr (hxa.trans haHalf)
    · change ((phiH ⟨x, hxU⟩).2 : ℝ) - 1 / 2 < 0
      rw [htH ⟨x, hxU⟩ (Or.inl hxH)]
      exact sub_neg.mpr (hxa.trans haHalf)
  · have hbpos : 0 < b := (by norm_num : (0 : ℝ) < 1 / 2).trans hbHalf
    obtain ⟨x, hx⟩ := T.tail_nonempty true hbpos hb
    obtain ⟨hxU, hbx⟩ := (T.mem_tail_iff_m28 true hbpos hb).mp hx
    have hxS := (le_max_left bS (max bC bH)).trans_lt hbx
    have hxC := ((le_max_left bC bH).trans (le_max_right bS (max bC bH))).trans_lt hbx
    have hxH := ((le_max_right bC bH).trans (le_max_right bS (max bC bH))).trans_lt hbx
    refine ⟨⟨x, hxU⟩, ?_, ?_, ?_⟩
    · change 0 < ((phiS ⟨x, hxU⟩).2 : ℝ) - 1 / 2
      rw [htS ⟨x, hxU⟩ (Or.inr hxS)]
      exact sub_pos.mpr (hbHalf.trans hbx)
    · change 0 < ((phiC ⟨x, hxU⟩).2 : ℝ) - 1 / 2
      rw [htC ⟨x, hxU⟩ (Or.inr hxC)]
      exact sub_pos.mpr (hbHalf.trans hbx)
    · change 0 < ((phiH ⟨x, hxU⟩).2 : ℝ) - 1 / 2
      rw [htH ⟨x, hxU⟩ (Or.inr hxH)]
      exact sub_pos.mpr (hbHalf.trans hbx)

end PoincareConjecture.OpenCylinderModel
