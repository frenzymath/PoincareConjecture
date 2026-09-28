import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralHeightBandSection










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePL.exists_heightBand_level_chart {S : Set (E × ℝ)} {B : Set E}
    {lower upper : E → ℝ} {r : E × ℝ → ℝ}
    {H : S ≃ₜ {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}}
    (hH : H.IsFinitePL) (hval : ∀ p, (H p : E × ℝ) = ((p : E × ℝ).1, r p)) (c : ℝ) :
    ∃ F : {x : E | x ∈ B ∧ c ∈ Icc (lower x) (upper x)} ≃ₜ
        (S ∩ {p | r p = c} : Set (E × ℝ)),
      F.IsFinitePL ∧ ∀ x, (F x : E × ℝ).1 = (x : E) := by
  have hcopy := hH.symm
  obtain ⟨_, ⟨K, hK, hspace, _⟩, _⟩ := hcopy
  obtain ⟨G, hG, hGeval⟩ := K.exists_heightBand_section_chart hK hspace c
  let A : (E × ℝ) →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ E ℝ).toAffineMap
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_affineLevel_complex hK A c
  have ha : K.space ∩ {p : E × ℝ | p.2 = c} ⊆
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} :=
    fun _ hp => hspace ▸ hp.1
  have hb : S ∩ {p | r p = c} ⊆ S := inter_subset_left
  have hmem (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}) :
      (p : E × ℝ) ∈ K.space ∩ {p : E × ℝ | p.2 = c} ↔
        (H.symm p : E × ℝ) ∈ S ∩ {p | r p = c} := by
    have hc : r (H.symm p) = (p : E × ℝ).2 := by
      have h := congrArg Prod.snd (hval (H.symm p))
      rw [H.apply_symm_apply] at h
      exact h.symm
    have hpK : (p : E × ℝ) ∈ K.space := hspace.symm ▸ p.property
    change ((p : E × ℝ) ∈ K.space ∧ (p : E × ℝ).2 = c) ↔
      (H.symm p : E × ℝ) ∈ S ∧ r (H.symm p) = c
    simp only [hpK, (H.symm p).property, hc, true_and]
  let Q := H.symm.restrictSubsets ha hb hmem
  have hQ : Q.IsFinitePL := hH.symm.restrictSubsets ha hb hmem J hJ hJs
  refine ⟨G.trans Q, hG.trans hQ, fun x => ?_⟩
  have h := congrArg Prod.fst (hval (H.symm ⟨G x, ha (G x).property⟩))
  rw [H.apply_symm_apply] at h
  exact h.symm.trans (congrArg Prod.fst (hGeval x))

end Homeomorph
