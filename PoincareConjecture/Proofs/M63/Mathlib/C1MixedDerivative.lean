import PoincareConjecture.Proofs.M63.Mathlib.ClassicalPrimitive
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology

universe u

theorem hasDerivAt_spatialDeriv_of_time_equation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega) {q R : ℝ × ℝ → E}
    (hq : ContDiffOn ℝ 1 q Omega) (hR : ContDiffOn ℝ 1 R Omega)
    (htime : ∀ z ∈ Omega, HasDerivAt (fun s => q (z.1, s)) (R z) z.2)
    {x t : ℝ} (hxt : (x, t) ∈ Omega) :
    HasDerivAt (fun s => deriv (fun y => q (y, s)) x)
      (fderiv ℝ R (x, t) (1, 0)) t := by
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp (hOmega.mem_nhds hxt)
  let l := x - eps / 2
  let r := x + eps / 2
  let alpha := t - eps / 2
  let beta := t + eps / 2
  have hxl : l < x := by dsimp [l]; linarith
  have hxr : x < r := by dsimp [r]; linarith
  have hat : alpha < t := by dsimp [alpha]; linarith
  have htb : t < beta := by dsimp [beta]; linarith
  have hab : alpha ≤ beta := hat.le.trans htb.le
  have hx : x ∈ Icc l r := ⟨hxl.le, hxr.le⟩
  have hrect : Icc l r ×ˢ Icc alpha beta ⊆ Omega := by
    intro z hz
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff,
      abs_lt, abs_lt]
    dsimp [l, r, alpha, beta] at hz
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  let Rx : ℝ × ℝ → E := fun z => fderiv ℝ R z (1, 0)
  have hRx : ContinuousOn Rx Omega :=
    ((hR.fderiv_of_isOpen hOmega (m := 0) (by norm_num)).clm_apply
      (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))).continuousOn
  have hqd (y s : ℝ) (hy : y ∈ Icc l r) (hs : s ∈ Icc alpha beta) :
      DifferentiableAt ℝ (fun z => q (z, s)) y :=
    ((hq.contDiffAt (hOmega.mem_nhds (hrect ⟨hy, hs⟩))).differentiableAt
      (by norm_num)).comp y (differentiableAt_id.prodMk (differentiableAt_const s))
  have hRd (y s : ℝ) (hy : y ∈ Icc l r) (hs : s ∈ Icc alpha beta) :
      HasDerivAt (fun z => R (z, s)) (Rx (y, s)) y :=
    ((hR.contDiffAt (hOmega.mem_nhds (hrect ⟨hy, hs⟩))).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_id y).prodMk (hasDerivAt_const y s))
  have hcontR (y : ℝ) (hy : y ∈ Icc l r) :
      ContinuousOn (fun s => R (y, s)) (Icc alpha beta) :=
    hR.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hs => hrect ⟨hy, hs⟩)
  have hcontRx (y : ℝ) (hy : y ∈ Icc l r) :
      ContinuousOn (fun s => Rx (y, s)) (Icc alpha beta) :=
    hRx.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hs => hrect ⟨hy, hs⟩)
  have hintR (y s : ℝ) (hy : y ∈ Icc l r) (hs : s ∈ Icc alpha beta) :
      IntervalIntegrable (fun v => R (y, v)) volume alpha s :=
    ContinuousOn.intervalIntegrable_of_Icc hs.1
      ((hcontR y hy).mono (Icc_subset_Icc_right hs.2))
  have hintRx (y s : ℝ) (hy : y ∈ Icc l r) (hs : s ∈ Icc alpha beta) :
      IntervalIntegrable (fun v => Rx (y, v)) volume alpha s :=
    ContinuousOn.intervalIntegrable_of_Icc hs.1
      ((hcontRx y hy).mono (Icc_subset_Icc_right hs.2))
  have hprim (y s : ℝ) (hy : y ∈ Icc l r) (hs : s ∈ Icc alpha beta) :
      q (y, s) = q (y, alpha) + ∫ v in alpha..s, R (y, v) := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
      (hq.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun v hv => hrect ⟨hy, hv.1, hv.2.trans hs.2⟩))
      (fun v hv => htime (y, v) (hrect ⟨hy, hv.1.le, hv.2.le.trans hs.2⟩))
      (hintR y s hy hs)
    rw [heq]
    dsimp only [Function.comp_def, id_eq]
    abel
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hRx.mono hrect)
  have hprime (s : ℝ) (hs : s ∈ Icc alpha beta) :
      deriv (fun y => q (y, s)) x = deriv (fun y => q (y, alpha)) x +
        ∫ v in alpha..s, Rx (x, v) := by
    have hdint := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun y v => R (y, v)) (F' := fun y v => Rx (y, v))
      (x₀ := x) (s := Ioo l r) (bound := fun _ => C) (a := alpha) (b := s)
      (Ioo_mem_nhds hxl hxr)
      (by
        filter_upwards [Ioo_mem_nhds hxl hxr] with y hy
        exact (hintR y s (Ioo_subset_Icc_self hy) hs).def'.aestronglyMeasurable)
      (hintR x s hx hs) (hintRx x s hx hs).def'.aestronglyMeasurable
      (Eventually.of_forall fun v hv y hy => by
        rw [uIoc_of_le hs.1] at hv
        exact hC (y, v) ⟨Ioo_subset_Icc_self hy, hv.1.le, hv.2.trans hs.2⟩)
      intervalIntegrable_const
      (Eventually.of_forall fun v hv y hy => by
        rw [uIoc_of_le hs.1] at hv
        exact hRd y v (Ioo_subset_Icc_self hy) ⟨hv.1.le, hv.2.trans hs.2⟩)
    have heq : (fun y => q (y, s)) =ᶠ[𝓝 x]
        (fun y => q (y, alpha) + ∫ v in alpha..s, R (y, v)) := by
      filter_upwards [Ioo_mem_nhds hxl hxr] with y hy
      exact hprim y s (Ioo_subset_Icc_self hy) hs
    exact (((hqd x alpha hx ⟨le_rfl, hab⟩).hasDerivAt.add hdint.2).congr_of_eventuallyEq
      heq).deriv
  exact hasDerivAt_of_ae_continuous_primitive hab (hintRx x beta hx ⟨hab, le_rfl⟩)
    (hcontRx x hx) EventuallyEq.rfl hprime ⟨hat, htb⟩
