import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorEndpointBound
import PoincareConjecture.Definitions.M64Annulus











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem boundary_motion_speed_bound
    (g : RiemannianMetric n M) {f : ℝ × ℝ → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1 f (Ioo (-epsilon) epsilon ×ˢ univ)) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ h ∈ Icc (-epsilon / 2) (epsilon / 2),
      ∀ x ∈ Icc (0 : ℝ) curvePeriod,
        g.tangentNorm (f (h, x)) (curveVelocity (fun y => f (h, y)) x) ≤ S := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let U : Set (ℝ × ℝ) := Ioo (-epsilon) epsilon ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  let V : ℝ × ℝ → TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) :=
    fun q => ⟨q, (0, 1)⟩
  have hV : Continuous V :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ × ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hspeed : ContinuousOn (fun q : ℝ × ℝ =>
      g.tangentNorm (f q) (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 n) f q (0, 1))) U := by
    intro q hq
    exact (Proofs.M58.continuous_bundle_norm.continuousAt.comp
      ((Proofs.M58.continuousAt_tangentMap_of_contMDiffAt
        (hf.contMDiffAt (hU.mem_nhds hq))).comp hV.continuousAt)).continuousWithinAt
  have hsub : Icc (-epsilon / 2) (epsilon / 2) ×ˢ Icc (0 : ℝ) curvePeriod ⊆ U := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩
  obtain ⟨S, hS⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hspeed.mono hsub)
  refine ⟨max S 0, le_max_right _ _, ?_⟩
  intro h hh x hx
  have hline := (hasDerivAt_const x h).prodMk (hasDerivAt_id x)
  have hmem : (h, x) ∈ U := hsub ⟨hh, hx⟩
  have hdiff := (hf.contMDiffAt (hU.mem_nhds hmem)).mdifferentiableAt
    one_ne_zero
  have hchain := mfderiv_comp_apply x hdiff hline.differentiableAt.mdifferentiableAt (1 : ℝ)
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun y : ℝ => (h, y)) x 1 = (0, 1) := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv, id_eq] using! hline.deriv
  rw [hd] at hchain
  change curveVelocity (fun y => f (h, y)) x =
    mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 n) f (h, x) (0, 1) at hchain
  rw [hchain]
  exact (le_abs_self _).trans ((hS (h, x) ⟨hh, hx⟩).trans (le_max_left _ _))

end PoincareConjecture.M64
