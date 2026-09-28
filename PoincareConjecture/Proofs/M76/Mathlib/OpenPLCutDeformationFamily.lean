import PoincareConjecture.Proofs.M76.Mathlib.CompactPLCutDeformationFamily
import PoincareConjecture.Proofs.M76.Mathlib.OpenSuperlevelDeformation

set_option autoImplicit false

open Set Geometry unitInterval

namespace OpenPartialHomeomorph

theorem exists_open_PL_cut_deformation_family
    {M E G ι : Type*} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (e : ι → OpenPartialHomeomorph M E)
    {C A : Set M} (hC : IsCompact C) (hACint : A ⊆ interior C)
    (K J : SimplicialComplex ℝ G) (hK : K.faces.Finite) (hJ : J.faces.Finite)
    (H : C ≃ₜ K.space) (F : M → G) (hF : Continuous F)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hHF : ∀ x : C, (H x : G) = F x) (hJA : J.space = F '' A)
    (ell : G →ᵃ[ℝ] ℝ) (halign : K.RespectsAffineHyperplane ell) :
    ∃ (z : M → ℝ) (Q : Set M), IsCompact Q ∧ Q ⊆ interior C ∧
      Continuous z ∧ (∀ x, x ∉ Q → z x = 0) ∧
      (∀ i, LocallyPiecewiseAffineOn (z ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ A, z x = 1) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        let P : Set M := {x | c ≤ z x}
        let O : Set M := {x | c < z x}
        IsCompact P ∧ IsOpen O ∧ A ⊆ O ∧ O ⊆ P ∧ P ⊆ interior C ∧
          ∃ (r : C(O, O)) (T : (ContinuousMap.id O).HomotopyRel r {x | (x : M) ∈ A}),
            range r = {x | (x : M) ∈ A} ∧
            (∀ (t : I) (x : O), 0 ≤ ell (F x) → 0 ≤ ell (F (T (t, x)))) ∧
            (∀ (t : I) (x : O), ell (F x) = 0 → ell (F (T (t, x))) = 0) ∧
            ∀ (t : I) (x : O), z (T (t, x)) =
              (1 - (t : ℝ)) * z x + (t : ℝ) := by
  obtain ⟨z, Q, hQ, hQC, hz, hzoff, hzPL, hzA, hlevel⟩ :=
    exists_compact_PL_cut_deformation_family_mass e hC hACint K J hK hJ H F hF
      hFPL hHF hJA ell halign
  refine ⟨z, Q, hQ, hQC, hz, hzoff, hzPL, hzA, ?_⟩
  intro c hc hc1
  obtain ⟨hP, _, hPC, T, _, hT0, hT1, hfix, hpos, hzero, hmass⟩ := hlevel c hc hc1
  obtain ⟨hO, hAO, r, L, hLT, hr⟩ :=
    ContinuousMap.exists_homotopyRel_open_superlevel hz hc1 hzA T hT0 hT1 hfix hmass
  refine ⟨hP, hO, hAO, fun x hx => (show c < z x from hx).le,
    hPC, r, L, hr, ?_, ?_, ?_⟩
  · intro t x hx
    rw [hLT]
    exact hpos t ⟨x, (show c < z x from x.property).le⟩ hx
  · intro t x hx
    rw [hLT]
    exact hzero t ⟨x, (show c < z x from x.property).le⟩ hx
  · intro t x
    rw [hLT]
    exact hmass t ⟨x, (show c < z x from x.property).le⟩

end OpenPartialHomeomorph
