import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Basic









set_option autoImplicit false

open scoped Manifold

variable {𝕜 E H M F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]


set_option backward.isDefEq.respectTransparency false in


theorem vector_graph_hasDerivWithinAt (f : 𝕜 × M → F)
    {γ : 𝕜 → M} {J : Set 𝕜} {s : 𝕜}
    (hf : MDifferentiableAt ((𝓘(𝕜, 𝕜)).prod I) (𝓘(𝕜, F)) f (s, γ s))
    (hγ : MDifferentiableWithinAt (𝓘(𝕜, 𝕜)) I γ J s)
    (hJ : UniqueDiffWithinAt 𝕜 J s) :
    HasDerivWithinAt (fun r => f (r, γ r))
      (deriv (fun r => f (r, γ s)) s +
        mvfderiv I (fun p => f (s, p)) (γ s)
          (mfderivWithin (𝓘(𝕜, 𝕜)) I γ J s (1 : 𝕜))) J s := by
  have hgraph := mdifferentiableWithinAt_id.prodMk hγ
  have hcomp := (hf.comp_mdifferentiableWithinAt s hgraph).differentiableWithinAt.hasDerivWithinAt
  have h := congrArg (fun L => L (1 : 𝕜))
    (mfderiv_comp_mfderivWithin s hf hgraph hJ.uniqueMDiffWithinAt)
  rw [mfderivWithin_prodMk mdifferentiableWithinAt_id hγ hJ.uniqueMDiffWithinAt,
    mfderivWithin_id hJ.uniqueMDiffWithinAt] at h
  change mfderivWithin (𝓘(𝕜, 𝕜)) (𝓘(𝕜, F)) (fun r => f (r, γ r)) J s (1 : 𝕜) =
    mfderiv ((𝓘(𝕜, 𝕜)).prod I) (𝓘(𝕜, F)) f (s, γ s)
      ((1 : 𝕜), mfderivWithin (𝓘(𝕜, 𝕜)) I γ J s (1 : 𝕜)) at h
  erw [mfderiv_prod_eq_add_apply hf] at h
  have hderiv (g : 𝕜 → F) :
      mfderiv (𝓘(𝕜, 𝕜)) (𝓘(𝕜, F)) g s (1 : 𝕜) = deriv g s := by
    have hg := congrArg (fun L : 𝕜 →L[𝕜] F => L 1)
      (mfderiv_eq_fderiv (𝕜 := 𝕜) (f := g) (x := s))
    exact hg.trans fderiv_apply_one_eq_deriv
  have hwithin (g : 𝕜 → F) :
      mfderivWithin (𝓘(𝕜, 𝕜)) (𝓘(𝕜, F)) g J s (1 : 𝕜) = derivWithin g J s := by
    exact congrArg (fun L : 𝕜 →L[𝕜] F => L 1)
      (mfderivWithin_eq_fderivWithin (𝕜 := 𝕜) (f := g) (s := J) (x := s))
  dsimp only [Prod.fst, Prod.snd] at h
  rw [hwithin, hderiv] at h
  convert hcomp using 1 <;> first | rfl | exact h.symm
