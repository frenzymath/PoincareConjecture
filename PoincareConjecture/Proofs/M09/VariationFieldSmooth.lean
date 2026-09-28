import PoincareConjecture.Proofs.M09.FamilyPhase

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T a b : ℝ} {p : BackwardTimePath F T a b}

set_option backward.isDefEq.respectTransparency false in
theorem squareVariationField_smooth (V : LVariation F T a b p) :
    let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
    IsOpen U ∧ sqrtParameterInterval a b ⊆ U ∧
      ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
        (fun s ↦ (⟨V.baseSquareCurve s, squareVariationField V s⟩ :
          TangentBundle (𝓡 n) M)) U := by
  let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  let f : ℝ × ℝ → M := fun z ↦ V.squareFamily z.1 z.2
  have hf : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ f V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [f, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hi : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) ∞
      (fun s : ℝ ↦ (s, (0 : ℝ))) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  have hzero : (0 : ℝ) ∈ Set.Ioo (-V.radius) V.radius :=
    ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  refine ⟨V.square_open.preimage (continuous_id.prodMk continuous_const),
    fun s hs ↦ V.square_contains ⟨hs, hzero⟩, ?_⟩
  exact (familyPhase_contMDiffOn f V.squareDomain V.square_open hf).comp
    hi.contMDiffOn (fun s (hs : s ∈ U) ↦ hs)

end PoincareConjecture.Proofs.M09
