import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Planar.SourceCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Collars.SourceComplex
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.AnnulusDimension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation









set_option autoImplicit false
open Set Geometry Metric PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rims" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

theorem exists_planar_annulus_rim_complexes :
    ∃ K A : SimplicialComplex ℝ P2,
      K.faces.Finite ∧ A.faces.Finite ∧ K.space = Ann ∧
      A.space = {x | depth 8 x = -1 ∨ depth 8 x = 1} ∧
      A.space ⊆ K.space ∧
      (∀ a ∈ K.faces, a.card ≤ 3) ∧ (∀ a ∈ A.faces, a.card ≤ 2) := by
  obtain ⟨_, H, _, hH, hHi, _, hHr⟩ :=
    ProtectedAnnulus.exists_planar_source_coordinates (S := ProtectedAnnulus.source) rfl
  obtain ⟨_, A₀, _, hA₀, _, hA₀s, hA₀K, _⟩ :=
    ProtectedAnnulus.exists_source_rim_complexes
  obtain ⟨F, ⟨K, hK, hKs, hFK⟩, hF⟩ := hH
  obtain ⟨G, hG, hGv⟩ := hHi
  have hA₀source : A₀.space ⊆ ProtectedAnnulus.source := by
    rw [hA₀s]
    exact fun _ hx => ⟨sphere_subset_closedBall hx.1, hx.2⟩
  obtain ⟨D, hD, hDs, hGD⟩ := hG.restrict A₀ hA₀ hA₀source
  obtain ⟨A, hA, hAs, hAc⟩ := hGD.exists_finite_triangulation_image hD
  have hAr : A.space = {x | depth 8 x = -1 ∨ depth 8 x = 1} := by
    rw [hAs, hDs]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hv := hGv ⟨y, hA₀source hy⟩
      rw [← hv]
      apply (hHr (H.symm ⟨y, hA₀source hy⟩)).mp
      rw [H.apply_symm_apply]
      exact hA₀s.subset hy
    · intro hx
      have hxAnn : x ∈ Ann := mem_squareAnnulus_iff_depth.mpr (by
        rcases hx with hx | hx <;> rw [hx] <;> norm_num)
      refine ⟨H ⟨x, hxAnn⟩, hA₀s.symm.subset ((hHr ⟨x, hxAnn⟩).mpr hx), ?_⟩
      rw [← hGv (H ⟨x, hxAnn⟩), H.symm_apply_apply]
  refine ⟨K, A, hK, hA, hKs, hAr, ?_, ?_, ?_⟩
  · intro x hx
    rw [hKs, mem_squareAnnulus_iff_depth]
    rcases hAr.subset hx with hx | hx <;> rw [hx] <;> norm_num
  · intro a ha
    simpa only [Fintype.card_coe, Module.finrank_prod, Module.finrank_self] using
      (K.indep ha).card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  · intro a ha
    obtain ⟨b, hb, _, hba⟩ := hAc a ha
    exact hba.trans (ProtectedAnnulus.source_rim_face_card_le D
      (hDs.trans hA₀s) hb)

end PoincareConjecture.M76.Dehn
