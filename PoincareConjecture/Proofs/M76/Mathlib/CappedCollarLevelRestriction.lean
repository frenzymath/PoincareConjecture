import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.RadialCutSide











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePL.exists_capped_collar_cut_restriction
    {T R d s : Set E} {A : E → ℝ} (H : E ≃ₜ E)
    (hfix : ∀ x ∈ R, H x = x) (hdplane : d ⊆ {x | A x = 0})
    {c : ℝ} (hc : c ≠ 0)
    {F : ((T ∪ R) ∩ {x | A x = c} : Set E) ≃ₜ
      (((H '' (d ∪ T)) ∪ R) ∩ {x | A x = c} : Set E)} (hF : F.IsFinitePL)
    (hmem : ∀ y : ((T ∪ R) ∩ {x | A x = c} : Set E),
      (y : E) ∈ s ↔ (F y : E) ∈ H '' (s ∪ d))
    (hFR : ∀ x : (R ∩ {x | A x = c} : Set E),
      (F ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKs : K.space = s) :
    ∃ G : (((T ∩ s) ∪ (R ∩ s)) ∩ {x | A x = c} : Set E) ≃ₜ
        (((H '' (d ∪ (T ∩ s))) ∪ (R ∩ s)) ∩ {x | A x = c} : Set E),
      G.IsFinitePL ∧ ∀ x : ((R ∩ s) ∩ {x | A x = c} : Set E),
        (G ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x := by
  let S := (T ∪ R) ∩ {x | A x = c}
  let Y := ((H '' (d ∪ T)) ∪ R) ∩ {x | A x = c}
  have htest (y : S) : (y : E) ∈ S ∩ s ↔ (F y : E) ∈ Y ∩ H '' (s ∪ d) :=
    ⟨fun hy => ⟨(F y).property, (hmem y).mp hy.2⟩,
      fun hy => ⟨y.property, (hmem y).mpr hy.2⟩⟩
  have hcopy := hF
  obtain ⟨_, ⟨J, hJ, hJS, _⟩, _⟩ := hcopy
  obtain ⟨W, hW, hWs⟩ := J.exists_finite_triangulation_inter K hJ hK
  have hWX : W.space = S ∩ s := by rw [hWs, hJS, hKs]
  let e := F.restrictSubsets inter_subset_left inter_subset_left htest
  have he : e.IsFinitePL := hF.restrictSubsets inter_subset_left inter_subset_left
    htest W hW hWX
  have hsource : S ∩ s = ((T ∩ s) ∪ (R ∩ s)) ∩ {x | A x = c} := by
    ext x
    simp only [S, mem_inter_iff, mem_union]
    tauto
  have hcapInter : (H '' (d ∪ T)) ∩ (H '' (s ∪ d)) = H '' (d ∪ (T ∩ s)) := by
    rw [← image_inter H.injective]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_union]
    tauto
  have htarget : Y ∩ H '' (s ∪ d) =
      ((H '' (d ∪ (T ∩ s))) ∪ (R ∩ s)) ∩ {x | A x = c} := by
    calc
      Y ∩ H '' (s ∪ d) =
          (((H '' (d ∪ T)) ∩ (H '' (s ∪ d))) ∩ {x | A x = c}) ∪
            ((R ∩ {x | A x = c}) ∩ (H '' (s ∪ d))) := by
        ext x
        simp only [Y, mem_inter_iff, mem_union]
        tauto
      _ = ((H '' (d ∪ (T ∩ s))) ∩ {x | A x = c}) ∪
          ((R ∩ {x | A x = c}) ∩ s) := by
        rw [hcapInter, H.fixed_level_inter_image_cap hfix hdplane hc]
      _ = ((H '' (d ∪ (T ∩ s))) ∪ (R ∩ s)) ∩ {x | A x = c} := by
        ext x
        simp only [mem_inter_iff, mem_union]
        tauto
  let G := (Homeomorph.setCongr hsource.symm).trans
    (e.trans (Homeomorph.setCongr htarget))
  exact ⟨G, he.setCongr hsource htarget, fun x => hFR ⟨x, x.property.1.1, x.property.2⟩⟩

end Homeomorph
