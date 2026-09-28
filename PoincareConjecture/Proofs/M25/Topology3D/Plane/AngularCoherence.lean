import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubeAngle










set_option autoImplicit false

open Set Metric Function Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M25.Topology3D



theorem eventuallyEq_of_sphereCircleParameter_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) {X : Type*} [TopologicalSpace X] {x : X} {f g : X → ℝ}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hfg : f x = g x)
    (himage : ∀ᶠ y in 𝓝 x, sphereCircleParameter e (f y) = sphereCircleParameter e (g y)) :
    f =ᶠ[𝓝 x] g := by
  have hfx : f x ∈ Ioo (f x - Real.pi) (f x + Real.pi) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hgx : g x ∈ Ioo (f x - Real.pi) (f x + Real.pi) := by rwa [← hfg]
  have hfn : ∀ᶠ y in 𝓝 x, f y ∈ Ioo (f x - Real.pi) (f x + Real.pi) :=
    hf (isOpen_Ioo.mem_nhds hfx)
  have hgn : ∀ᶠ y in 𝓝 x, g y ∈ Ioo (f x - Real.pi) (f x + Real.pi) :=
    hg (isOpen_Ioo.mem_nhds hgx)
  filter_upwards [hfn, hgn, himage] with y hyf hyg hyeq
  exact injOn_sphereCircleParameter_Ico e
    (a := f x - Real.pi) (b := f x + Real.pi) (by linarith)
    ⟨hyf.1.le, hyf.2⟩ ⟨hyg.1.le, hyg.2⟩ hyeq



theorem hasDerivAt_curveTubeAngle_movingCenter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0)
    (γ : ℝ → E) (z s : ℝ) (hγ : DifferentiableAt ℝ γ s)
    (hmem : ((z, s), γ s) ∈ curveTubeAngularDomain e q0 T) :
    HasDerivAt (fun t => curveTubeAngle e q0 T ((z, t), γ t))
      (fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y)) (γ s) (deriv γ s)) s := by
  obtain ⟨hV, hA⟩ := curveTubeAngle_regular e q0 T hInv hx
  have hAp := hA.contDiffAt (hV.mem_nhds hmem)
  let f : ℝ → ℝ := fun t => curveTubeAngle e q0 T ((z, t), γ t)
  let g : ℝ → ℝ := fun t => curveTubeAngle e q0 T ((z, s), γ t)
  have hf : ContinuousAt f s := hAp.continuousAt.comp
    (f := fun t => ((z, t), γ t))
    ((continuousAt_const.prodMk continuousAt_id).prodMk hγ.continuousAt)
  have hg : ContinuousAt g s := hAp.continuousAt.comp
    (f := fun t => ((z, s), γ t))
    (continuousAt_const.prodMk hγ.continuousAt)
  have heq : f =ᶠ[𝓝 s] g := eventuallyEq_of_sphereCircleParameter_eq e hf hg rfl
    (Eventually.of_forall (fun t =>
      (sphereCircleParameter_curveTubeAngle e q0 T ((z, t), γ t)).trans
        (sphereCircleParameter_curveTubeAngle e q0 T ((z, s), γ t)).symm))
  have hslice : DifferentiableAt ℝ
      (fun y : E => curveTubeAngle e q0 T ((z, s), y)) (γ s) :=
    (hAp.comp (γ s) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  exact (hslice.hasFDerivAt.comp_hasDerivAt s hγ.hasDerivAt).congr_of_eventuallyEq heq

end PoincareConjecture.M25.Topology3D
