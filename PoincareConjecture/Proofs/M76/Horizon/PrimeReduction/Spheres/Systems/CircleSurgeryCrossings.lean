import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryCofaceTransport








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem paired_face_crossings_of_equal_off_closed
    {X : Type*} [TopologicalSpace X]
    (Q : OpenPartialHomeomorph X V3) {S S' C : Set X} {T : Set V3}
    (hC : IsClosed C) (houtside : S' \ C = S \ C)
    {w : V3} (hwQ : w ∈ Q.target) (hwC : Q.symm w ∉ C)
    (hcrossing : ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧
        LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0) :
    ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧
        LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ S' ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0 := by
  intro O hO hwO
  let V := O ∩ (Q.target ∩ Q.symm ⁻¹' Cᶜ)
  have hV : IsOpen V := hO.inter (Q.isOpen_inter_preimage_symm hC.isOpen_compl)
  obtain ⟨B, hwB, hBV, hzero, hB, hBi, hS, hT⟩ :=
    hcrossing V hV ⟨hwO, hwQ, hwC⟩
  refine ⟨B, hwB, hBV.trans inter_subset_left, hzero, hB, hBi, ?_, hT⟩
  intro x hx
  have hxC : Q.symm x ∉ C := (hBV hx).2.2
  have hmem : Q.symm x ∈ S' ↔ Q.symm x ∈ S := by
    simpa only [mem_sdiff, hxC, not_false_eq_true, and_true] using
      (Set.ext_iff.mp houtside (Q.symm x))
  exact hmem.trans (hS x hx)

end PoincareConjecture.M76
