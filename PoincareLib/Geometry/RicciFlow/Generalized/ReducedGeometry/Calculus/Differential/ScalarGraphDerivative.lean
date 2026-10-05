import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Scalar differentiation along a manifold graph

Morgan-Tian Lemma 6.4, pp. 107-108. Split the derivative on parameter
times manifold into its two partial derivatives. The curve only needs
within differentiability, so the rule includes closed parameter endpoints.
-/

set_option autoImplicit false

open scoped Manifold

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]

-- Scalar tangent fibers reduce to the scalar field when evaluating the chain rule.
set_option backward.isDefEq.respectTransparency false in
/-- The within scalar derivative along a manifold graph is the sum of
its actual parameter partial and spatial differential on the within
velocity, as used in Lemma 6.4, pp. 107-108. -/
theorem scalar_graph_hasDerivWithinAt (F : 𝕜 × M → 𝕜)
    {γ : 𝕜 → M} {J : Set 𝕜} {s : 𝕜}
    (hF : MDifferentiableAt ((𝓘(𝕜, 𝕜)).prod I) (𝓘(𝕜, 𝕜)) F (s, γ s))
    (hγ : MDifferentiableWithinAt (𝓘(𝕜, 𝕜)) I γ J s)
    (hJ : UniqueDiffWithinAt 𝕜 J s) :
    HasDerivWithinAt (fun r => F (r, γ r))
      (deriv (fun r => F (r, γ s)) s +
        mvfderiv I (fun p => F (s, p)) (γ s)
          (mfderivWithin (𝓘(𝕜, 𝕜)) I γ J s (1 : 𝕜))) J s := by
  have hgraph := mdifferentiableWithinAt_id.prodMk hγ
  have hcomp := (hF.comp_mdifferentiableWithinAt s hgraph).differentiableWithinAt.hasDerivWithinAt
  have h := congrArg (fun L => L (1 : 𝕜))
    (mfderiv_comp_mfderivWithin s hF hgraph hJ.uniqueMDiffWithinAt)
  rw [mfderivWithin_prodMk mdifferentiableWithinAt_id hγ hJ.uniqueMDiffWithinAt,
    mfderivWithin_id hJ.uniqueMDiffWithinAt] at h
  change mfderivWithin (𝓘(𝕜, 𝕜)) (𝓘(𝕜, 𝕜)) (fun r => F (r, γ r)) J s (1 : 𝕜) =
    mfderiv ((𝓘(𝕜, 𝕜)).prod I) (𝓘(𝕜, 𝕜)) F (s, γ s)
      ((1 : 𝕜), mfderivWithin (𝓘(𝕜, 𝕜)) I γ J s (1 : 𝕜)) at h
  erw [mfderiv_prod_eq_add_apply hF] at h
  have hscalar (f : 𝕜 → 𝕜) :
      mfderiv (𝓘(𝕜, 𝕜)) (𝓘(𝕜, 𝕜)) f s (1 : 𝕜) = deriv f s := by
    have hf := congrArg (fun L : 𝕜 →L[𝕜] 𝕜 => L 1)
      (mfderiv_eq_fderiv (𝕜 := 𝕜) (f := f) (x := s))
    exact hf.trans fderiv_apply_one_eq_deriv
  have hwithin (f : 𝕜 → 𝕜) :
      mfderivWithin (𝓘(𝕜, 𝕜)) (𝓘(𝕜, 𝕜)) f J s (1 : 𝕜) = derivWithin f J s := by
    exact congrArg (fun L : 𝕜 →L[𝕜] 𝕜 => L 1)
      (mfderivWithin_eq_fderivWithin (𝕜 := 𝕜) (f := f) (s := J) (x := s))
  dsimp only [Prod.fst, Prod.snd] at h
  rw [hwithin, hscalar] at h
  convert hcomp using 1 <;> first | rfl | exact h.symm
