import PoincareConjecture.Proofs.M07.Analysis.ODE.ParameterSuperposition
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ImplicitContDiff









open Filter Set
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Poincare.ODE.Parameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem contDiff_picardResidual {T : ℝ} (hT : 0 ≤ T) {f : E → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (picardResidual hT f) := by
  have h1 : ContDiff ℝ ∞ (fun q : E × C(Set.Icc (0:ℝ) T, E) => q.2) := contDiff_snd
  have h2 : ContDiff ℝ ∞
      (fun q : E × C(Set.Icc (0:ℝ) T, E) => ContinuousMap.const (Set.Icc (0:ℝ) T) q.1) :=
    ContDiff.continuousLinearMap_comp
      (ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T) : E →L[ℝ] C(Set.Icc (0:ℝ) T, E))
      contDiff_fst
  have h3 : ContDiff ℝ ∞
      (fun q : E × C(Set.Icc (0:ℝ) T, E) => intervalPrimitive hT (superposition f q.2)) :=
    ContDiff.continuousLinearMap_comp (intervalPrimitive hT)
      ((contDiff_superposition_infty hf).comp contDiff_snd)
  exact (h1.sub h2).sub h3

theorem hasStrictFDerivAt_picardResidual {T : ℝ} (hT : 0 < T)
    {f : E → E} {f' : E → E →L[ℝ] E} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    {x₀ : E} {α₀ : C(Set.Icc (0:ℝ) T, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc : ∀ t, ContinuousAt f' (α₀ t))
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α₀ t)) :
    HasStrictFDerivAt (picardResidual hT.le f)
      (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E)
        - (ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T)).comp
            (ContinuousLinearMap.fst ℝ E C(Set.Icc (0:ℝ) T, E))
        - ((intervalPrimitive hT.le).comp (postcompCurve A₀)).comp
            (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E))) (x₀, α₀) := by
  set pt : E × C(Set.Icc (0:ℝ) T, E) := (x₀, α₀) with hpt_def
  set constE : E →L[ℝ] C(Set.Icc (0:ℝ) T, E) := ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T)
  set JP : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    (intervalPrimitive hT.le).comp (postcompCurve A₀) with hJP_def
  have hN : HasStrictFDerivAt (superposition f) (postcompCurve A₀) α₀ :=
    hasStrictFDerivAt_superposition hu hd hmem hc hA₀
  have h1 : HasStrictFDerivAt (fun q : E × C(Set.Icc (0:ℝ) T, E) => q.2)
      (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E))) pt := hasStrictFDerivAt_snd
  have h2 : HasStrictFDerivAt
      (fun q : E × C(Set.Icc (0:ℝ) T, E) => ContinuousMap.const (Set.Icc (0:ℝ) T) q.1)
      (constE.comp (ContinuousLinearMap.fst ℝ E (C(Set.Icc (0:ℝ) T, E)))) pt :=
    constE.hasStrictFDerivAt.comp pt hasStrictFDerivAt_fst
  have h3b : HasStrictFDerivAt
      (fun q : E × C(Set.Icc (0:ℝ) T, E) => superposition f q.2)
      ((postcompCurve A₀).comp (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E)))) pt :=
    hN.comp pt hasStrictFDerivAt_snd
  have h3 : HasStrictFDerivAt
      (fun q : E × C(Set.Icc (0:ℝ) T, E) => intervalPrimitive hT.le (superposition f q.2))
      (JP.comp (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E)))) pt :=
    (intervalPrimitive hT.le).hasStrictFDerivAt.comp pt h3b
  exact (h1.sub h2).sub h3

theorem contDiffAt_flow_of_picardResidual {T : ℝ} (hT : 0 < T)
    {f : E → E} (hf : ContDiff ℝ ∞ f)
    {x₀ : E} {α₀ : C(Set.Icc (0:ℝ) T, E)}
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = fderiv ℝ f (α₀ t))
    (hTL : T * ‖A₀‖ < 1)
    {σ : E → C(Set.Icc (0:ℝ) T, E)}
    (hσ0 : σ x₀ = α₀) (hσc : ContinuousAt σ x₀)
    (hσ : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le f (x, σ x) = 0) :
    ContDiffAt ℝ ∞ σ x₀ := by
  classical
  set pt : E × C(Set.Icc (0:ℝ) T, E) := (x₀, α₀) with hpt_def
  set JP : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    (intervalPrimitive hT.le).comp (postcompCurve A₀) with hJP_def
  have hcdf : ContDiffAt ℝ ∞ (picardResidual hT.le f) pt :=
    (contDiff_picardResidual hT.le hf).contDiffAt
  have hpn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hu0 : picardResidual hT.le f pt = 0 := by
    have h := hσ.self_of_nhds; rw [hσ0] at h; exact h
  have hG : HasStrictFDerivAt (picardResidual hT.le f)
      (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E)
        - (ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T)).comp
            (ContinuousLinearMap.fst ℝ E C(Set.Icc (0:ℝ) T, E))
        - JP.comp (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E))) pt :=
    hasStrictFDerivAt_picardResidual hT isOpen_univ
      (fun x _ => (hf.differentiable (by simp)).differentiableAt.hasFDerivAt)
      (fun _ => Set.mem_univ _) (fun _ => (hf.continuous_fderiv (by simp)).continuousAt) hA₀
  have hfderiv : fderiv ℝ (picardResidual hT.le f) pt
      = ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E)
        - (ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T)).comp
            (ContinuousLinearMap.fst ℝ E C(Set.Icc (0:ℝ) T, E))
        - JP.comp (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E)) := hG.hasFDerivAt.fderiv
  have hJPnorm : ‖JP‖ < 1 :=
    (norm_intervalPrimitive_comp_postcompCurve_le hT.le A₀).trans_lt hTL
  set w : (C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))ˣ :=
    Units.oneSub JP hJPnorm with hw_def
  have hinvertible :
      ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse w.mul_inv w.inv_mul
  have hinr : fderiv ℝ (picardResidual hT.le f) pt
        ∘L ContinuousLinearMap.inr ℝ E C(Set.Icc (0:ℝ) T, E)
      = (1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP := by
    rw [hfderiv]
    refine ContinuousLinearMap.ext fun β => ?_
    simp
  have if₂ : (fderiv ℝ (picardResidual hT.le f) pt
      ∘L ContinuousLinearMap.inr ℝ E C(Set.Icc (0:ℝ) T, E)).IsInvertible := by
    rw [hinr]; exact hinvertible
  set ψ : E → C(Set.Icc (0:ℝ) T, E) := hcdf.implicitFunction hpn if₂ with hψ_def
  have hψcd : ContDiffAt ℝ ∞ ψ x₀ := hcdf.contDiffAt_implicitFunction hpn if₂
  have hmap : Filter.Tendsto (fun x : E => (x, σ x)) (𝓝 x₀) (𝓝 pt) := by
    have h : Filter.Tendsto (fun x : E => (x, σ x)) (𝓝 x₀) (𝓝 (x₀, σ x₀)) :=
      continuousAt_id.prodMk hσc
    rwa [hσ0] at h
  have hev : ∀ᶠ x in 𝓝 x₀, σ x = ψ x := by
    filter_upwards [hmap.eventually (hcdf.eventually_apply_eq_iff_implicitFunction hpn if₂), hσ]
      with x hx hx0
    exact (hx.mp (by rw [hx0, hu0])).symm
  exact hψcd.congr_of_eventuallyEq hev

end Poincare.ODE.Parameter

end
