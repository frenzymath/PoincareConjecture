import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic











set_option autoImplicit false

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable {𝕜 E H M F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

namespace Bundle.Trivialization

variable (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
  [MemTrivializationAtlas e]



theorem mdifferentiableAt_continuousLinearMapAt_section
    {σ : ∀ x, V x} {x : M} (hx : x ∈ e.baseSet)
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x) :
    MDifferentiableAt I 𝓘(𝕜, F)
      (fun p => e.continuousLinearMapAt 𝕜 p (σ p)) x := by
  have h := (e.mdifferentiableAt_section_iff I σ hx).mp hσ
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  exact e.continuousLinearMapAt_apply_of_mem 𝕜 hp (σ p)



noncomputable def flatCovariantDerivative (σ : ∀ x, V x) (x : M) :
    TangentSpace I x →L[𝕜] V x :=
  (e.symmL 𝕜 x).comp
    (mvfderiv I (fun p => e.continuousLinearMapAt 𝕜 p (σ p)) x)

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]



theorem isCovariantDerivativeOn_flatCovariantDerivative :
    IsCovariantDerivativeOn F (e.flatCovariantDerivative (I := I)) e.baseSet where
  add hσ hτ hx := by
    have hσc := e.mdifferentiableAt_continuousLinearMapAt_section hx hσ
    have hτc := e.mdifferentiableAt_continuousLinearMapAt_section hx hτ
    ext v
    simp only [flatCovariantDerivative, Pi.add_apply, map_add,
      mvfderiv_fun_add hσc hτc, ContinuousLinearMap.comp_apply, add_apply]
  leibniz := by
    intro σ f x hσ hf hx
    have hσc := e.mdifferentiableAt_continuousLinearMapAt_section hx hσ
    ext v
    simp only [flatCovariantDerivative, Pi.smul_apply', map_smul,
      mvfderiv_fun_smul hf hσc, ContinuousLinearMap.comp_apply, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply, map_add]
    rw [e.symmL_continuousLinearMapAt hx]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]




theorem covariantDerivative_eq_flat_add_difference
    {cov : (∀ x, V x) → ∀ x, TangentSpace I x →L[𝕜] V x}
    (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    {σ : ∀ x, V x} {x : M} (hx : x ∈ e.baseSet)
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x)
    (v : TangentSpace I x) :
    cov σ x v =
      e.symmL 𝕜 x (mvfderiv I (fun p => e.continuousLinearMapAt 𝕜 p (σ p)) x v) +
        hcov.difference e.isCovariantDerivativeOn_flatCovariantDerivative x (σ x) v := by
  rw [IsCovariantDerivativeOn.difference_apply hcov
    e.isCovariantDerivativeOn_flatCovariantDerivative hx hσ]
  simp only [sub_apply, flatCovariantDerivative, ContinuousLinearMap.comp_apply]
  abel

end Bundle.Trivialization
