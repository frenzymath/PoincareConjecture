import PoincareConjecture.Proofs.M25.Topology3D.Plane.LocalGraphSides

set_option autoImplicit false

open Set Metric Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_local_two_sides_within_of_straightening
    {X : Type*} [TopologicalSpace X] {C U V : Set X} {q : X}
    (e : X ≃ₜ (ℝ × ℝ)) (hU : IsOpen U) (hqU : q ∈ U) (hq : q ∈ C)
    (heC : ∀ z ∈ U, z ∈ C ↔ (e z).2 = 0) (hV : IsOpen V) (hqV : q ∈ V) :
    ∃ W A B : Set X, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∩ V ∧
      IsConnected A ∧ IsConnected B ∧ A ∪ B = W \ C ∧
      C ∩ W ⊆ closure A ∧ C ∩ W ⊆ closure B := by
  have hqzero : (e q).2 = 0 := (heC q hqU).mp hq
  obtain ⟨r, hr, hrUV⟩ := Metric.isOpen_iff.mp (e.isOpenMap (U ∩ V) (hU.inter hV))
    (e q) (mem_image_of_mem e ⟨hqU, hqV⟩)
  let a := (e q).1
  let R : Set (ℝ × ℝ) := Ioo (a - r) (a + r) ×ˢ Ioo (-r) r
  let A0 : Set (ℝ × ℝ) := Ioo (a - r) (a + r) ×ˢ Ioo (-r) 0
  let B0 : Set (ℝ × ℝ) := Ioo (a - r) (a + r) ×ˢ Ioo 0 r
  have hRball : R = ball (e q) r := by
    have heq : e q = (a, 0) := Prod.ext rfl hqzero
    rw [heq, ← ball_prod_same, Real.ball_eq_Ioo, Real.ball_zero_eq_Ioo]
  have hWUV : e ⁻¹' R ⊆ U ∩ V := by
    intro z hz
    obtain ⟨w, hw, hew⟩ := hrUV (hRball ▸ hz)
    exact e.injective hew ▸ hw
  have har : a - r < a + r := by linarith
  have hAr : A0 ⊆ R := fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hr⟩
  have hBr : B0 ⊆ R := fun z hz => ⟨hz.1, (neg_neg_of_pos hr).trans hz.2.1, hz.2.2⟩
  refine ⟨e ⁻¹' R, e ⁻¹' A0, e ⁻¹' B0,
    (isOpen_Ioo.prod isOpen_Ioo).preimage e.continuous, ?_, hWUV, ?_, ?_, ?_, ?_, ?_⟩
  · change e q ∈ R
    rw [hRball]
    exact mem_ball_self hr
  · exact e.isConnected_preimage.mpr
      ((isConnected_Ioo har).prod (isConnected_Ioo (neg_neg_of_pos hr)))
  · exact e.isConnected_preimage.mpr ((isConnected_Ioo har).prod (isConnected_Ioo hr))
  · apply subset_antisymm
    · rintro z (hz | hz)
      · refine ⟨hAr hz, ?_⟩
        intro hzC
        exact hz.2.2.ne ((heC z (hWUV (hAr hz)).1).mp hzC)
      · refine ⟨hBr hz, ?_⟩
        intro hzC
        exact hz.2.1.ne' ((heC z (hWUV (hBr hz)).1).mp hzC)
    · rintro z ⟨hz, hzC⟩
      have hz0 : (e z).2 ≠ 0 := fun hez => hzC ((heC z (hWUV hz).1).mpr hez)
      rcases hz0.lt_or_gt with hneg | hpos
      · exact Or.inl ⟨hz.1, hz.2.1, hneg⟩
      · exact Or.inr ⟨hz.1, hpos, hz.2.2⟩
  · rintro z ⟨hzC, hzR⟩
    rw [← e.preimage_closure]
    change e z ∈ closure A0
    rw [closure_prod_eq, closure_Ioo har.ne, closure_Ioo (neg_neg_of_pos hr).ne]
    exact ⟨⟨hzR.1.1.le, hzR.1.2.le⟩, by
      rw [(heC z (hWUV hzR).1).mp hzC]
      exact ⟨(neg_neg_of_pos hr).le, le_rfl⟩⟩
  · rintro z ⟨hzC, hzR⟩
    rw [← e.preimage_closure]
    change e z ∈ closure B0
    rw [closure_prod_eq, closure_Ioo har.ne, closure_Ioo hr.ne]
    exact ⟨⟨hzR.1.1.le, hzR.1.2.le⟩, by
      rw [(heC z (hWUV hzR).1).mp hzC]
      exact ⟨le_rfl, hr.le⟩⟩

end PoincareConjecture.M25.Topology3D
