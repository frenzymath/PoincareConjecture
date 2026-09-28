import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian












set_option autoImplicit false

open Bundle Filter ContinuousLinearMap
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M40

section BundleHom

variable {X B₁ B₂ F₁ F₂ : Type*}
  [TopologicalSpace X] [TopologicalSpace B₁] [TopologicalSpace B₂]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ : B₁ → Type*} {E₂ : B₂ → Type*}
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, InnerProductSpace ℝ (E₁ x)]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, InnerProductSpace ℝ (E₂ x)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [IsContinuousRiemannianBundle F₁ E₁] [IsContinuousRiemannianBundle F₂ E₂]
  {b₁ : X → B₁} {b₂ : X → B₂}
  {T : ∀ y, E₁ (b₁ y) →L[ℝ] E₂ (b₂ y)} {x : X} {C : ℝ}




theorem eventually_norm_bundleHom_lt
    (hb₁ : ContinuousAt b₁ x) (hb₂ : ContinuousAt b₂ x)
    (hT : ContinuousAt (fun y =>
      inCoordinates F₁ E₁ F₂ E₂ (b₁ x) (b₁ y) (b₂ x) (b₂ y) (T y)) x)
    (hC : ‖T x‖ < C) : ∀ᶠ y in 𝓝 x, ‖T y‖ < C := by
  let t₁ := trivializationAt F₁ E₁ (b₁ x)
  let t₂ := trivializationAt F₂ E₂ (b₂ x)
  have hx₁ : b₁ x ∈ t₁.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  have hx₂ : b₂ x ∈ t₂.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  let D : X → E₁ (b₁ x) →L[ℝ] E₂ (b₂ x) := fun y =>
    (t₂.symmL ℝ (b₂ x)).comp
      ((inCoordinates F₁ E₁ F₂ E₂ (b₁ x) (b₁ y) (b₂ x) (b₂ y) (T y)).comp
        (t₁.continuousLinearMapAt ℝ (b₁ x)))
  have hD : ContinuousAt D x := continuousAt_const.clm_comp
    (hT.clm_comp continuousAt_const)
  have hDx : D x = T x := by
    ext v
    simp only [D, inCoordinates, comp_apply]
    rw [t₁.symmL_continuousLinearMapAt hx₁,
      t₂.symmL_continuousLinearMapAt hx₂]
  have hbudget : ∀ᶠ s : ℝ in 𝓝 0,
      (1 + s) * (‖T x‖ + s) * (1 + s) < C := by
    have hc : ContinuousAt (fun s : ℝ => (1 + s) * (‖T x‖ + s) * (1 + s)) 0 := by
      fun_prop
    exact hc.eventually_lt continuousAt_const (by simpa using hC)
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hbudget' : ∀ᶠ s : ℝ in 𝓝[>] 0,
      (1 + s) * (‖T x‖ + s) * (1 + s) < C := nhdsWithin_le_nhds hbudget
  obtain ⟨s, hs, hbudget⟩ := (hpos.and hbudget').exists
  have hr : 1 < 1 + s := by linarith
  have hDnorm : ∀ᶠ y in 𝓝 x, ‖D y‖ < ‖T x‖ + s :=
    hD.norm.eventually_lt continuousAt_const (by rw [hDx]; linarith)
  have hleft : ∀ᶠ y in 𝓝 x,
      ‖(t₂.symmL ℝ (b₂ y)).comp (t₂.continuousLinearMapAt ℝ (b₂ x))‖ < 1 + s :=
    hb₂.tendsto.eventually
      (eventually_norm_symmL_trivializationAt_comp_self_lt F₂ E₂ (b₂ x) hr)
  have hright : ∀ᶠ y in 𝓝 x,
      ‖(t₁.symmL ℝ (b₁ x)).comp (t₁.continuousLinearMapAt ℝ (b₁ y))‖ < 1 + s :=
    hb₁.tendsto.eventually
      (eventually_norm_symmL_trivializationAt_self_comp_lt F₁ E₁ (b₁ x) hr)
  filter_upwards [hDnorm, hleft, hright,
    hb₁.preimage_mem_nhds (t₁.open_baseSet.mem_nhds hx₁),
    hb₂.preimage_mem_nhds (t₂.open_baseSet.mem_nhds hx₂)] with y hyD hyl hyr hy₁ hy₂
  let A := (t₂.symmL ℝ (b₂ y)).comp (t₂.continuousLinearMapAt ℝ (b₂ x))
  let B := (t₁.symmL ℝ (b₁ x)).comp (t₁.continuousLinearMapAt ℝ (b₁ y))
  have hfactor : T y = (A.comp (D y)).comp B := by
    ext v
    simp only [A, B, D, inCoordinates, comp_apply]
    rw [t₁.continuousLinearMapAt_symmL hx₁,
      t₁.symmL_continuousLinearMapAt hy₁,
      t₂.continuousLinearMapAt_symmL hx₂,
      t₂.symmL_continuousLinearMapAt hy₂]
  calc
    ‖T y‖ = ‖(A.comp (D y)).comp B‖ := congrArg norm hfactor
    _ ≤ (‖A‖ * ‖D y‖) * ‖B‖ :=
      (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1 + s) * (‖T x‖ + s) * (1 + s) := by
      gcongr
    _ < C := hbudget

end BundleHom

section ManifoldDerivative

variable {E H F K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [IsManifold I 1 M] [IsManifold J 1 N]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [RiemannianBundle (TangentSpace J : N → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace J : N → Type _)]




theorem eventually_norm_mfderiv_lt
    {f : M → N} {x : M} {C : ℝ} (hf : ContMDiffAt I J 1 f x)
    (hC : ‖mfderiv I J f x‖ < C) :
    ∀ᶠ y in 𝓝 x, ‖mfderiv I J f y‖ < C := by
  apply eventually_norm_bundleHom_lt (F₁ := E) (F₂ := F)
    continuousAt_id hf.continuousAt ?_ hC
  simpa +unfoldPartialApp only [inTangentCoordinates, id_eq] using
    (hf.mfderiv_const (m := 0) (by norm_num)).continuousAt

end ManifoldDerivative

end PoincareConjecture.M40
