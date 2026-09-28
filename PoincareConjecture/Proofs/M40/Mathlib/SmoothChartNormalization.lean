import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingRiemannian
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv














set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Topology Manifold ContDiff

universe uE uH uM uF

namespace PoincareConjecture.M40

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]




def chartNormalizationLinearEquiv (e : OpenPartialHomeomorph M F)
    (he : e.MDifferentiable I 𝓘(ℝ, F)) {x : M} (hx : x ∈ e.source) :
    TangentSpace I x ≃L[ℝ] F :=
  (he.mfderiv hx).trans (NormedSpace.fromTangentSpace (e x))




def normalizedSmoothChart (e : OpenPartialHomeomorph M F)
    (he : e.MDifferentiable I 𝓘(ℝ, F)) {x : M} (hx : x ∈ e.source) :
    OpenPartialHomeomorph M (TangentSpace I x) :=
  e.trans (chartNormalizationLinearEquiv e he hx).symm.toHomeomorph.toOpenPartialHomeomorph

variable (e : OpenPartialHomeomorph M F) (he : e.MDifferentiable I 𝓘(ℝ, F))
  {x : M} (hx : x ∈ e.source)




theorem normalizedSmoothChart_source :
    (normalizedSmoothChart e he hx).source = e.source := by
  change e.source ∩ Set.univ = e.source
  exact Set.inter_univ _




theorem normalizedSmoothChart_target :
    (normalizedSmoothChart e he hx).target =
      (chartNormalizationLinearEquiv e he hx) ⁻¹' e.target := by
  change Set.univ ∩ (chartNormalizationLinearEquiv e he hx) ⁻¹' e.target = _
  exact Set.univ_inter _



theorem normalizedSmoothChart_apply (y : M) :
    normalizedSmoothChart e he hx y =
      (chartNormalizationLinearEquiv e he hx).symm (e y) := rfl



theorem normalizedSmoothChart_symm_apply (z : TangentSpace I x) :
    (normalizedSmoothChart e he hx).symm z =
      e.symm (chartNormalizationLinearEquiv e he hx z) := rfl

section Riemannian

variable [RiemannianBundle (TangentSpace I : M → Type uE)]



theorem normalizedSmoothChart_contMDiffOn
    (hs : ContMDiffOn I 𝓘(ℝ, F) ∞ e e.source) :
    ContMDiffOn I 𝓘(ℝ, TangentSpace I x) ∞
      (normalizedSmoothChart e he hx) (normalizedSmoothChart e he hx).source := by
  rw [normalizedSmoothChart_source]
  exact (chartNormalizationLinearEquiv e he hx).symm.toContinuousLinearMap.contMDiff
    |>.comp_contMDiffOn hs



theorem normalizedSmoothChart_symm_contMDiffOn
    (hs : ContMDiffOn 𝓘(ℝ, F) I ∞ e.symm e.target) :
    ContMDiffOn 𝓘(ℝ, TangentSpace I x) I ∞
      (normalizedSmoothChart e he hx).symm (normalizedSmoothChart e he hx).target := by
  rw [normalizedSmoothChart_target]
  exact hs.comp (chartNormalizationLinearEquiv e he hx).toContinuousLinearMap.contMDiffOn
    (fun _ hz => hz)




theorem normalizedSmoothChart_mfderiv_apply (v : TangentSpace I x) :
    NormedSpace.fromTangentSpace (normalizedSmoothChart e he hx x)
      (mfderiv I 𝓘(ℝ, TangentSpace I x) (normalizedSmoothChart e he hx) x v) = v := by
  let A := chartNormalizationLinearEquiv e he hx
  change NormedSpace.fromTangentSpace (A.symm (e x))
    (mfderiv I 𝓘(ℝ, TangentSpace I x) (A.symm ∘ e) x v) = v
  rw [mfderiv_comp x A.symm.differentiableAt.mdifferentiableAt (he.mdifferentiableAt hx)]
  simp only [mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
  change A.symm (A v) = v
  exact A.symm_apply_apply v




theorem normalizedSmoothChart_norm_mfderiv_le :
    ‖mfderiv I 𝓘(ℝ, TangentSpace I x) (normalizedSmoothChart e he hx) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul, norm_tangentSpace_vectorSpace]
  change ‖NormedSpace.fromTangentSpace (normalizedSmoothChart e he hx x)
    (mfderiv I 𝓘(ℝ, TangentSpace I x) (normalizedSmoothChart e he hx) x v)‖ ≤ ‖v‖
  exact (congrArg norm (normalizedSmoothChart_mfderiv_apply e he hx v)).le




theorem normalizedSmoothChart_symm_norm_mfderiv_le :
    ‖mfderiv 𝓘(ℝ, TangentSpace I x) I (normalizedSmoothChart e he hx).symm
      (normalizedSmoothChart e he hx x)‖ ≤ 1 := by
  let A := chartNormalizationLinearEquiv e he hx
  let n := normalizedSmoothChart e he hx
  have hnx : x ∈ n.source := by
    simpa only [n, normalizedSmoothChart_source] using hx
  have hAx : A (n x) = e x := A.apply_symm_apply _
  have hinv : MDifferentiableAt 𝓘(ℝ, F) I e.symm (A (n x)) := by
    rw [hAx]
    exact he.mdifferentiableAt_symm (e.map_source hx)
  have hnorm (w : TangentSpace I x) :
      ‖(show TangentSpace I (n.symm (n x)) from w)‖ = ‖w‖ := by
    rw [n.left_inv hnx]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have hvalue : mfderiv 𝓘(ℝ, TangentSpace I x) I n.symm (n x) v =
      NormedSpace.fromTangentSpace (n x) v := by
    change mfderiv 𝓘(ℝ, TangentSpace I x) I (e.symm ∘ A) (n x) v = _
    rw [mfderiv_comp (n x) hinv A.differentiableAt.mdifferentiableAt]
    simp only [mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
    rw [hAx]
    change (he.mfderiv hx).symm
      ((he.mfderiv hx) (NormedSpace.fromTangentSpace (n x) v)) = _
    exact (he.mfderiv hx).symm_apply_apply _
  change ‖mfderiv 𝓘(ℝ, TangentSpace I x) I n.symm (n x) v‖ ≤ 1 * ‖v‖
  rw [one_mul]
  exact ((congrArg norm hvalue).trans
    ((hnorm (NormedSpace.fromTangentSpace (n x) v)).trans
      (norm_tangentSpace_vectorSpace (v := v)).symm)).le

variable [IsManifold I ∞ M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type uE)]





theorem normalizedSmoothChart_eventually_norm_mfderiv_lt
    (hs : ContMDiffOn I 𝓘(ℝ, F) ∞ e e.source)
    (hi : ContMDiffOn 𝓘(ℝ, F) I ∞ e.symm e.target)
    {C : ℝ} (hC : 1 < C) :
    (∀ᶠ y in 𝓝 x,
      ‖mfderiv I 𝓘(ℝ, TangentSpace I x) (normalizedSmoothChart e he hx) y‖ < C) ∧
    (∀ᶠ z in 𝓝 (normalizedSmoothChart e he hx x),
      ‖mfderiv 𝓘(ℝ, TangentSpace I x) I (normalizedSmoothChart e he hx).symm z‖ < C) := by
  letI : IsContinuousRiemannianBundle (TangentSpace I x)
      (TangentSpace 𝓘(ℝ, TangentSpace I x)) :=
    { exists_continuous :=
        ⟨(riemannianMetricVectorSpace (TangentSpace I x)).inner,
          (riemannianMetricVectorSpace (TangentSpace I x)).contMDiff.continuous,
          fun _ _ _ => rfl⟩ }
  let n := normalizedSmoothChart e he hx
  have hnx : x ∈ n.source := by
    simpa only [n, normalizedSmoothChart_source] using hx
  constructor
  · apply eventually_norm_mfderiv_lt
    · exact ((normalizedSmoothChart_contMDiffOn e he hx hs).contMDiffAt
        (n.open_source.mem_nhds hnx)).of_le (by norm_num)
    · exact (normalizedSmoothChart_norm_mfderiv_le e he hx).trans_lt hC
  · apply eventually_norm_mfderiv_lt
    · exact ((normalizedSmoothChart_symm_contMDiffOn e he hx hi).contMDiffAt
        (n.open_target.mem_nhds (n.map_source hnx))).of_le (by norm_num)
    · exact (normalizedSmoothChart_symm_norm_mfderiv_le e he hx).trans_lt hC

end Riemannian

end PoincareConjecture.M40
