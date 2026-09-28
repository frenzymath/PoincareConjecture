import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SkeletonFaceGraphMotion









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem triangle_graph_crossings_after_fixed_motion
    {X : Type*} [TopologicalSpace X]
    (Q : OpenPartialHomeomorph X V3) (H : X ≃ₜ X)
    {S t W : Set X} {T : Set V3} (G : SimplicialComplex ℝ V3)
    (hGQ : G.space ⊆ Q.target)
    (hphysical : Q.symm '' G.space = S ∩ t)
    (hW : IsOpen W) (htW : t ⊆ W) (hfix : EqOn H id W)
    (hcross : ∀ w ∈ G.space ∩ intrinsicInterior ℝ T,
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0) :
    Q.symm '' G.space = (H '' S) ∩ t ∧
    ∀ w ∈ G.space ∩ intrinsicInterior ℝ T,
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ H '' S ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0 := by
  have hmem {x : X} (hx : x ∈ W) : x ∈ H '' S ↔ x ∈ S := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := H.injective (hyx.trans (hfix hx).symm)
      exact hyx' ▸ hy
    · exact fun hxS => ⟨x, hxS, hfix hx⟩
  refine ⟨?_, ?_⟩
  · rw [hphysical]
    ext x
    exact and_congr_left (fun hxt => (hmem (htW hxt)).symm)
  · intro w hw O hO hwO
    let V := Q.target ∩ Q.symm ⁻¹' W
    have hV : IsOpen V := Q.symm.isOpen_inter_preimage hW
    have hwV : w ∈ V := ⟨hGQ hw.1,
      htW (hphysical.subset ⟨w, hw.1, rfl⟩).2⟩
    obtain ⟨B, hwB, hBO, hBw, hB, hBinv, hBS, hBT⟩ :=
      hcross w hw (O ∩ V) (hO.inter hV) ⟨hwO, hwV⟩
    exact ⟨B, hwB, hBO.trans inter_subset_left, hBw, hB, hBinv,
      fun x hx => (hmem (hBO hx).2.2).trans (hBS x hx), hBT⟩

end PoincareConjecture.M76
