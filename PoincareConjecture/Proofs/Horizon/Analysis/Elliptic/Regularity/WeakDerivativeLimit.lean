import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology

namespace Poincare.Analysis.Elliptic

variable {n : ℕ}

theorem integral_mul_partial_test {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (v : EuclideanSpace ℝ (Fin n))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, f x * fderiv ℝ φ x v) = -(∫ x in Ω, fderiv ℝ f x v * φ x) := by
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdf : ContinuousOn (fun x => fderiv ℝ f x v) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have hfirst : Integrable (fun x => fderiv ℝ φ x v * f x) := by
    apply Continuous.integrable_of_hasCompactSupport _ (hc.fderiv_apply ℝ v).mul_right
    exact (hdφ.continuousOn.mul hf.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_left.trans ((tsupport_fderiv_apply_subset ℝ v).trans hs))
  have hsecond : Integrable (fun x => φ x * fderiv ℝ f x v) := by
    apply Continuous.integrable_of_hasCompactSupport _ hc.mul_right
    exact (hφ.continuous.continuousOn.mul hdf).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_left.trans hs)
  have hprod : Integrable (fun x => φ x * f x) := by
    apply Continuous.integrable_of_hasCompactSupport _ hc.mul_right
    exact (hφ.continuous.continuousOn.mul hf.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_left.trans hs)
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hfirst hsecond hprod (fun x _ => hφ.differentiable (by simp) x)
    (fun x hx => (hf.contDiffAt (hΩ.mem_nhds (hs hx))).differentiableAt (by simp))
  have hleft : (∫ x in Ω, f x * fderiv ℝ φ x v) = ∫ x, fderiv ℝ φ x v * f x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hs (tsupport_fderiv_apply_subset ℝ v ht))), mul_zero])]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hright : (∫ x in Ω, fderiv ℝ f x v * φ x) = ∫ x, φ x * fderiv ℝ f x v := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero])]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  rw [hleft, hright, hparts, neg_neg]

theorem tendsto_integral_mul_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {v : ℕ → Lp ℝ 2 μ} {u : Lp ℝ 2 μ} (hv : Tendsto v atTop (𝓝 u))
    {ψ : X → ℝ} (hψ : MemLp ψ 2 μ) :
    Tendsto (fun k => ∫ x, v k x * ψ x ∂μ) atTop (𝓝 (∫ x, u x * ψ x ∂μ)) := by
  have heq (w : Lp ℝ 2 μ) :
      (∫ x, w x * ψ x ∂μ) = ⟪w, hψ.toLp ψ⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with x hx
    rw [hx]
    simp [mul_comm]
  simp_rw [heq]
  exact hv.inner tendsto_const_nhds

theorem weak_partial_of_tendsto_L2
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (i : Fin n)
    {uSeq vSeq : ℕ → Lp ℝ 2 (volume.restrict Ω)}
    {u v : Lp ℝ 2 (volume.restrict Ω)}
    (hu : Tendsto uSeq atTop (𝓝 u)) (hv : Tendsto vSeq atTop (𝓝 v))
    (hweak : ∀ k (φ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, uSeq k x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -(∫ x in Ω, vSeq k x * φ x)) :
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -(∫ x in Ω, v x * φ x) := by
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hdφLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
      2 (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict Ω
  have hl := tendsto_integral_mul_L2 hu hdφLp
  have hr := (tendsto_integral_mul_L2 hv hφLp).neg
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun k =>
    (hweak k φ hφ hc hs).symm))

private theorem exists_inner_representation_of_bound
    {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : V →ₗ[ℝ] H) (F : V →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v, ‖F v‖ ≤ C * ‖j v‖) :
    ∃ w : H, ‖w‖ ≤ C ∧ ∀ v, F v = ⟪w, j v⟫_ℝ := by
  let q := F.compLeftInverse j
  have hq : ‖q‖ ≤ C := by
    apply q.opNorm_le_bound hC
    rintro ⟨y, v, rfl⟩
    change ‖F.compLeftInverse j ⟨j v, _⟩‖ ≤ C * ‖j v‖
    rw [LinearMap.compLeftInverse_apply_of_bdd F j ⟨C, hbound⟩ v (j v) rfl]
    exact hbound v
  obtain ⟨G, hG, hGn⟩ := exists_extension_norm_eq (LinearMap.range j) q
  let w := (InnerProductSpace.toDual ℝ H).symm G
  refine ⟨w, ?_, fun v => ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H).symm G‖ ≤ C
    rw [LinearIsometryEquiv.norm_map, hGn]
    exact hq
  · have heq : G (j v) = F v := (hG ⟨j v, LinearMap.mem_range_self j v⟩).trans
      (LinearMap.compLeftInverse_apply_of_bdd F j ⟨C, hbound⟩ v (j v) rfl)
    rw [← heq]
    exact congrArg (fun L : H →L[ℝ] ℝ => L (j v))
      ((InnerProductSpace.toDual ℝ H).apply_symm_apply G).symm

private def compactSmoothTests (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n) → ℝ) where
  carrier := {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    (tsupport_add (f := f) (g := g)).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' c φ hφ := by
    refine ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left, ?_⟩
    apply subset_trans (closure_mono ?_) hφ.2.2
    intro x hx
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul] at hx ⊢
    exact (mul_ne_zero_iff.mp hx).2

private theorem compactSmoothTests_memLp {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (φ : compactSmoothTests Ω) : MemLp (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      2 (volume.restrict Ω) :=
  (φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2.1).restrict Ω

private noncomputable def compactSmoothTestsToL2 (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    compactSmoothTests Ω →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω) where
  toFun φ := (compactSmoothTests_memLp φ).toLp φ
  map_add' φ ψ := MemLp.toLp_add (compactSmoothTests_memLp φ) (compactSmoothTests_memLp ψ)
  map_smul' c φ := MemLp.toLp_const_smul c (compactSmoothTests_memLp φ)

private theorem compactSmoothTests_deriv_memLp {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (φ : compactSmoothTests Ω) (v : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x => fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x v)
      2 (volume.restrict Ω) :=
  (((φ.2.1.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (φ.2.2.1.fderiv_apply ℝ v)).restrict Ω

private noncomputable def derivativeTestPairing {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (v : EuclideanSpace ℝ (Fin n)) : compactSmoothTests Ω →ₗ[ℝ] ℝ where
  toFun φ := -(∫ x in Ω, u x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x v)
  map_add' φ ψ := by
    change -(∫ x in Ω, u x * fderiv ℝ (fun y => φ.1 y + ψ.1 y) x v) = _
    simp_rw [fderiv_fun_add (φ.2.1.differentiable (by simp) _)
      (ψ.2.1.differentiable (by simp) _), add_apply, mul_add]
    simpa only [Pi.mul_apply, neg_add] using congrArg Neg.neg
      (integral_add (hu.integrable_mul (compactSmoothTests_deriv_memLp φ v))
        (hu.integrable_mul (compactSmoothTests_deriv_memLp ψ v)))
  map_smul' c φ := by
    change -(∫ x in Ω, u x * fderiv ℝ (fun y => c * φ.1 y) x v) = c * _
    simp_rw [fderiv_const_mul (φ.2.1.differentiable (by simp) _),
      smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (u _) c, mul_assoc]
    rw [integral_const_mul, mul_neg]

theorem exists_weak_partial_of_test_bound
    {Ω : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (v : EuclideanSpace ℝ (Fin n))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      |∫ x in Ω, u x * fderiv ℝ φ x v| ≤ C * (eLpNorm φ 2 (volume.restrict Ω)).toReal) :
    ∃ g : Lp ℝ 2 (volume.restrict Ω), ‖g‖ ≤ C ∧
      ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ x in Ω, u x * fderiv ℝ φ x v) = -(∫ x in Ω, g x * φ x) := by
  have hb (φ : compactSmoothTests Ω) : ‖derivativeTestPairing hu v φ‖ ≤
      C * ‖compactSmoothTestsToL2 Ω φ‖ := by
    simpa only [derivativeTestPairing, LinearMap.coe_mk, AddHom.coe_mk, norm_neg,
      Real.norm_eq_abs, compactSmoothTestsToL2, Lp.norm_toLp] using
      hbound φ φ.2.1 φ.2.2.1 φ.2.2.2
  obtain ⟨g, hg, hrep⟩ := exists_inner_representation_of_bound (compactSmoothTestsToL2 Ω)
    (derivativeTestPairing hu v) hC hb
  refine ⟨g, hg, fun φ hφ hc hs => ?_⟩
  have h := hrep ⟨φ, hφ, hc, hs⟩
  have heq : ⟪g, compactSmoothTestsToL2 Ω ⟨φ, hφ, hc, hs⟩⟫_ℝ =
      ∫ x in Ω, g x * φ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(compactSmoothTests_memLp (⟨φ, hφ, hc, hs⟩ : compactSmoothTests Ω)).coeFn_toLp]
      with x hx
    change inner ℝ (g x) ((compactSmoothTestsToL2 Ω ⟨φ, hφ, hc, hs⟩) x) = g x * φ x
    rw [show (compactSmoothTestsToL2 Ω ⟨φ, hφ, hc, hs⟩) x = φ x from hx]
    simp [mul_comm]
  rw [heq] at h
  exact neg_eq_iff_eq_neg.mp h

theorem exists_weak_partial_of_bounded_approximation
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {uSeq vSeq : ℕ → Lp ℝ 2 (volume.restrict Ω)}
    {u : Lp ℝ 2 (volume.restrict Ω)} (hu : Tendsto uSeq atTop (𝓝 u))
    (v : EuclideanSpace ℝ (Fin n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ k, ‖vSeq k‖ ≤ C)
    (hweak : ∀ k (φ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, uSeq k x * fderiv ℝ φ x v) = -(∫ x in Ω, vSeq k x * φ x)) :
    ∃ g : Lp ℝ 2 (volume.restrict Ω), ‖g‖ ≤ C ∧
      ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ x in Ω, u x * fderiv ℝ φ x v) = -(∫ x in Ω, g x * φ x) := by
  apply exists_weak_partial_of_test_bound (Lp.memLp u) v hC
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hdφLp : MemLp (fun x => fderiv ℝ φ x v) 2 (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)).restrict Ω
  apply le_of_tendsto (tendsto_integral_mul_L2 hu hdφLp).abs
  apply Eventually.of_forall
  intro k
  have heq : (∫ x in Ω, vSeq k x * φ x) = ⟪vSeq k, hφLp.toLp φ⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφLp.coeFn_toLp] with x hx
    rw [hx]
    simp [mul_comm]
  rw [hweak k φ hφ hc hs, abs_neg, heq]
  calc
    |⟪vSeq k, hφLp.toLp φ⟫_ℝ| ≤ ‖vSeq k‖ * ‖hφLp.toLp φ‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ C * ‖hφLp.toLp φ‖ := mul_le_mul_of_nonneg_right (hbound k) (norm_nonneg _)
    _ = C * (eLpNorm φ 2 (volume.restrict Ω)).toReal := by rw [Lp.norm_toLp]

end Poincare.Analysis.Elliptic
