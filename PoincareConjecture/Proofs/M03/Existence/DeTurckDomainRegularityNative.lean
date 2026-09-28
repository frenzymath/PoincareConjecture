import PoincareConjecture.Proofs.M03.Existence.EuclideanTranslationNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanMollificationNative
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Data.Set.Finite.List
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Metric
open scoped Topology SchwartzMap ContDiff LineDeriv Convolution

noncomputable section

namespace PoincareConjecture.DeTurckDomainRegularityNative

open EuclideanTranslationNative

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def differenceQuotient (u : ScalarL2 n) (v : E) (h : ℝ) : ScalarL2 n :=
  h⁻¹ • (translateLp (h • v) u - u)

theorem inner_translateLp (u w : ScalarL2 n) (a : E) :
    inner ℝ (translateLp a u) w = inner ℝ u (translateLp (-a) w) := by
  calc
    _ = ∫ x, u (x + a) * w x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [translateLp_ae_eq a u] with x hx
      rw [hx]
      simp only [Real.inner_apply, mul_comm]
    _ = ∫ x, u x * w (x - a) := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun x => u x * w (x - a)) a
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [translateLp_ae_eq (-a) w] with x hx
      rw [hx]
      simp only [Real.inner_apply, sub_eq_add_neg, mul_comm]

theorem inner_differenceQuotient_adjoint (u w : ScalarL2 n) (v : E) (h : ℝ) :
    inner ℝ (differenceQuotient u v h) w =
      -(inner ℝ u (differenceQuotient w v (-h))) := by
  simp only [differenceQuotient, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right, inner_neg_right, inner_translateLp, neg_smul, inv_neg]
  ring

theorem continuous_differenceQuotient (v : E) (h : ℝ) :
    Continuous (fun u : ScalarL2 n => differenceQuotient u v h) := by
  have htrans : Continuous (translateLp (h • v) : ScalarL2 n → ScalarL2 n) :=
    (Lp.isometry_compMeasurePreserving
      (measurePreserving_add_right volume (h • v))).continuous
  change Continuous (fun u : ScalarL2 n => (h⁻¹ : ℝ) • (translateLp (h • v) u - u))
  exact (continuous_const : Continuous (fun _ : ScalarL2 n => (h⁻¹ : ℝ))).smul
    (htrans.sub continuous_id)

theorem norm_differenceQuotient_toLp_le {f : E → ℝ} (v : E)
    (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (hD : MemLp (fun x => fderiv ℝ f x v) 2 volume) (h : ℝ) :
    ‖differenceQuotient (hfL2.toLp f) v h‖ ≤
      ‖hD.toLp (fun x => fderiv ℝ f x v)‖ := by
  by_cases hh : h = 0
  · subst h
    simp only [differenceQuotient, inv_zero, zero_smul, norm_zero, norm_nonneg]
  · have hDhv : MemLp (fun x => fderiv ℝ f x (h • v)) 2 volume := by
      simpa only [map_smul, smul_eq_mul] using hD.const_mul h
    have henergy := translateLp_sub_norm_sq_le_directional hf hfL2 (h • v) hDhv
    simp only [map_smul, smul_eq_mul, mul_pow, integral_const_mul] at henergy
    rw [← scalar_toLp_norm_sq hD] at henergy
    have hnorm : ‖translateLp (h • v) (hfL2.toLp f) - hfL2.toLp f‖ ≤
        |h| * ‖hD.toLp (fun x => fderiv ℝ f x v)‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp
      simpa only [mul_pow, sq_abs] using henergy
    calc
      _ = |h⁻¹| * ‖translateLp (h • v) (hfL2.toLp f) - hfL2.toLp f‖ := by
        rw [differenceQuotient, norm_smul, Real.norm_eq_abs]
      _ ≤ |h⁻¹| * (|h| * ‖hD.toLp (fun x => fderiv ℝ f x v)‖) :=
        mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
      _ = _ := by
        rw [← mul_assoc, ← abs_mul, inv_mul_cancel₀ hh, abs_one, one_mul]

theorem norm_differenceQuotient_le_of_tendsto (u d : ScalarL2 n) (v : E)
    (f g : ℕ → ScalarL2 n) (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 d))
    (hbound : ∀ k h, ‖differenceQuotient (f k) v h‖ ≤ ‖g k‖) (h : ℝ) :
    ‖differenceQuotient u v h‖ ≤ ‖d‖ := by
  exact le_of_tendsto_of_tendsto
    (((continuous_differenceQuotient v h).tendsto u).comp hf).norm hg.norm
    (Eventually.of_forall (fun k => hbound k h))

theorem norm_differenceQuotient_le_of_denseRange {α β : Type*} [TopologicalSpace β]
    (e : α → β) (he : DenseRange e) (U D : β → ScalarL2 n)
    (hU : Continuous U) (hD : Continuous D) (v : E)
    (hbound : ∀ a h, ‖differenceQuotient (U (e a)) v h‖ ≤ ‖D (e a)‖)
    (z : β) (h : ℝ) : ‖differenceQuotient (U z) v h‖ ≤ ‖D z‖ := by
  exact he.induction_on z
    (isClosed_le ((continuous_differenceQuotient v h).comp hU).norm hD.norm)
    (fun a => hbound a h)

theorem inner_schwartz (u : ScalarL2 n) (φ : 𝓢(E, ℝ)) :
    inner ℝ u (φ.toLp 2 volume) = ∫ x, u x * φ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 volume] with x hx
  rw [hx]
  simp only [Real.inner_apply, mul_comm]

theorem inner_translate_schwartz (u : ScalarL2 n) (v : E) (h : ℝ)
    (φ : 𝓢(E, ℝ)) :
    inner ℝ (translateLp (h • v) u) (φ.toLp 2 volume) =
      ∫ x, u x * φ (x - h • v) := by
  rw [inner_schwartz]
  calc
    _ = ∫ x, u (x + h • v) * φ x := by
      apply integral_congr_ae
      filter_upwards [translateLp_ae_eq (h • v) u] with x hx
      rw [hx]
    _ = _ := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun x => u x * φ (x - h • v)) (h • v)

theorem inner_differenceQuotient_schwartz (u : ScalarL2 n) (v : E) (h : ℝ)
    (φ : 𝓢(E, ℝ)) :
    inner ℝ (differenceQuotient u v h) (φ.toLp 2 volume) =
      h⁻¹ * ((∫ x, u x * φ (x - h • v)) - ∫ x, u x * φ x) := by
  rw [differenceQuotient, real_inner_smul_left, inner_sub_left,
    inner_translate_schwartz, inner_schwartz]

theorem hasDerivAt_test_translation_pairing (u : ScalarL2 n) (v : E)
    (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ) :
    HasDerivAt (fun h : ℝ => ∫ x, u x * φ (x - h • v))
      (-(∫ x, u x * fderiv ℝ φ x v)) 0 := by
  have hD : Continuous (fun x => fderiv ℝ φ x v) :=
    ((φ.smooth 1).continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨B, hB⟩ := (hφ.fderiv_apply ℝ v).exists_bound_of_continuous hD
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨R, hR, hsupport⟩ := hφ.isBounded.exists_pos_norm_le
  let K : Set E := closedBall 0 (R + ‖v‖)
  let A : ℝ → E → ℝ := fun h x => u x * φ (x - h • v)
  let A' : ℝ → E → ℝ := fun h x => -(u x * fderiv ℝ φ (x - h • v) v)
  let dominator : E → ℝ := K.indicator (fun x => ‖u x‖ * B)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hloc : IntegrableOn (fun x => ‖u x‖ * B) K volume :=
    (((Lp.memLp u).locallyIntegrable (by norm_num)).integrableOn_isCompact hK).norm.mul_const B
  have hbound : Integrable dominator volume := hloc.integrable_indicator hK.measurableSet
  have hmeas (h : ℝ) : AEStronglyMeasurable (A h) volume :=
    (Lp.memLp u).aestronglyMeasurable.mul
      (φ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hA0 : Integrable (A 0) volume := by
    convert! (Lp.memLp u).integrable_mul (φ.memLp 2 volume) using 1 <;>
      first | rfl | (funext x; simp only [A, zero_smul, sub_zero, Pi.mul_apply])
  have hDmeas : AEStronglyMeasurable (A' 0) volume := by
    convert! ((Lp.memLp u).aestronglyMeasurable.mul hD.aestronglyMeasurable).neg using 1 <;>
      first | rfl | (funext x; simp only [A', zero_smul, sub_zero, Pi.neg_apply, Pi.mul_apply])
  have hderiv (h : ℝ) (x : E) : HasDerivAt (fun t => A t x) (A' h x) h := by
    have hpath : HasDerivAt (fun t : ℝ => x - t • v) (-v) h := by
      convert! (hasDerivAt_const h x).sub ((hasDerivAt_id h).smul_const v) using 1 <;>
        first | rfl | simp only [one_smul, zero_sub, Pi.sub_apply, id_eq]
    have htest : HasDerivAt (fun t : ℝ => φ (x - t • v))
        (fderiv ℝ φ (x - h • v) (-v)) h :=
      (φ.differentiable (x - h • v)).hasFDerivAt.comp_hasDerivAt h hpath
    simpa only [A, A', map_neg, mul_neg] using htest.const_mul (u x)
  have hdom (x : E) (h : ℝ) (hh : h ∈ Ioo (-1 : ℝ) 1) : ‖A' h x‖ ≤ dominator x := by
    by_cases hx : x ∈ K
    · dsimp only [dominator]
      rw [indicator_of_mem hx]
      simp only [A', norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left (hB (x - h • v)) (norm_nonneg _)
    · have hnot : x - h • v ∉ tsupport φ := by
        intro hs
        apply hx
        change ‖x - 0‖ ≤ R + ‖v‖
        rw [sub_zero]
        have hhv : ‖h • v‖ ≤ ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr ⟨hh.1.le, hh.2.le⟩)
        calc
          ‖x‖ = ‖(x - h • v) + h • v‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - h • v‖ + ‖h • v‖ := norm_add_le _ _
          _ ≤ R + ‖v‖ := add_le_add (hsupport _ hs) hhv
      dsimp only [dominator]
      rw [indicator_of_notMem hx]
      simp only [A', fderiv_of_notMem_tsupport ℝ hnot,
        ContinuousLinearMap.zero_apply, mul_zero, neg_zero, norm_zero, le_refl]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := A) (F' := A') (bound := dominator)
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas) hA0 hDmeas
    (Eventually.of_forall hdom) hbound
    (Eventually.of_forall (fun x h _ => hderiv h x))
  simpa only [A, A', zero_smul, sub_zero, integral_neg] using h.2

theorem tendsto_inner_differenceQuotient (u : ScalarL2 n) (v : E)
    (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ) :
    Tendsto (fun h => inner ℝ (differenceQuotient u v h) (φ.toLp 2 volume))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-(∫ x, u x * fderiv ℝ φ x v))) := by
  have heq : (fun h : ℝ => inner ℝ (differenceQuotient u v h) (φ.toLp 2 volume)) =
      slope (fun h : ℝ => ∫ x, u x * φ (x - h • v)) 0 := by
    funext h
    rw [inner_differenceQuotient_schwartz, slope_def_field]
    simp only [zero_smul, sub_zero, div_eq_mul_inv]
    ring
  rw [heq]
  exact (hasDerivAt_test_translation_pairing u v φ hφ).tendsto_slope

theorem exists_weakDerivative_of_bounded_differenceQuotients
    (u : ScalarL2 n) (v : E) {C : ℝ}
    (hbound : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖differenceQuotient u v h‖ ≤ C) :
    ∃ d : ScalarL2 n, ‖d‖ ≤ C ∧ ∀ φ : 𝓢(E, ℝ), HasCompactSupport φ →
      inner ℝ d (φ.toLp 2 volume) = -(∫ x, u x * fderiv ℝ φ x v) := by
  let ell : ℝ → WeakDual ℝ (ScalarL2 n) := fun h =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (ScalarL2 n)
      (differenceQuotient u v h))
  have hmem : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ell h ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (ScalarL2 n)) C := by
    filter_upwards [hbound] with h hh
    simpa only [mem_preimage, mem_closedBall, dist_zero_right, ell,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hh
  have hcompact : IsCompact
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (ScalarL2 n)) C) :=
    WeakDual.isCompact_closedBall (0 : StrongDual ℝ (ScalarL2 n)) C
  obtain ⟨L, hL, hcluster⟩ :=
    hcompact.exists_mapClusterPt (Filter.tendsto_principal.mpr hmem)
  let d : ScalarL2 n := (InnerProductSpace.toDual ℝ (ScalarL2 n)).symm
    (WeakDual.toStrongDual L)
  refine ⟨d, ?_, ?_⟩
  · simpa only [mem_preimage, mem_closedBall, dist_zero_right, d,
      LinearIsometryEquiv.norm_map] using hL
  · intro φ hφ
    have htest : MapClusterPt (L (φ.toLp 2 volume)) (𝓝[≠] (0 : ℝ))
        (fun h => inner ℝ (differenceQuotient u v h) (φ.toLp 2 volume)) := by
      simpa only [Function.comp_def, ell, StrongDual.toWeakDual_apply,
        InnerProductSpace.toDual_apply_apply] using
          MapClusterPt.continuousAt_comp
            (WeakDual.eval_continuous (φ.toLp 2 volume)).continuousAt hcluster
    have heq : L (φ.toLp 2 volume) = -(∫ x, u x * fderiv ℝ φ x v) :=
      eq_of_nhds_neBot (htest.clusterPt.mono
        (tendsto_inner_differenceQuotient u v φ hφ)).neBot
    simpa only [d, InnerProductSpace.toDual_symm_apply, WeakDual.toStrongDual_apply] using heq

theorem exists_weakCoordinateDerivative_of_bounded_differenceQuotients
    (u : ScalarL2 n) (j : Fin n) {C : ℝ}
    (hbound : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ‖differenceQuotient u (EuclideanSpace.single j 1) h‖ ≤ C) :
    ∃ d : ScalarL2 n, ‖d‖ ≤ C ∧ ∀ φ : 𝓢(E, ℝ), HasCompactSupport φ →
      inner ℝ d (φ.toLp 2 volume) =
        -(∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
  exists_weakDerivative_of_bounded_differenceQuotients u (EuclideanSpace.single j 1) hbound

theorem integrable_of_ae_compact_support (u : ScalarL2 n) {K : Set E}
    (hK : IsCompact K) (huK : ∀ᵐ x ∂volume, x ∉ K → u x = 0) :
    Integrable (u : E → ℝ) volume := by
  have hloc : IntegrableOn (u : E → ℝ) K volume :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
  exact hloc.integrable_of_ae_notMem_eq_zero huK

theorem hasDerivAt_test_translation_pairing_of_integrable (u : ScalarL2 n)
    (hu : Integrable (u : E → ℝ) volume) (v : E) (φ : 𝓢(E, ℝ)) :
    HasDerivAt (fun h : ℝ => ∫ x, u x * φ (x - h • v))
      (-(∫ x, u x * fderiv ℝ φ x v)) 0 := by
  let B : ℝ := SchwartzMap.seminorm ℝ 0 0 (∂_{v} φ)
  have hB (x : E) : ‖fderiv ℝ φ x v‖ ≤ B := by
    simpa only [B, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      (∂_{v} φ).norm_le_seminorm ℝ x
  have hD : Continuous (fun x => fderiv ℝ φ x v) :=
    ((φ.smooth 1).continuous_fderiv one_ne_zero).clm_apply continuous_const
  let A : ℝ → E → ℝ := fun h x => u x * φ (x - h • v)
  let A' : ℝ → E → ℝ := fun h x => -(u x * fderiv ℝ φ (x - h • v) v)
  let dominator : E → ℝ := fun x => ‖u x‖ * B
  have hbound : Integrable dominator volume := hu.norm.mul_const B
  have hmeas (h : ℝ) : AEStronglyMeasurable (A h) volume :=
    (Lp.memLp u).aestronglyMeasurable.mul
      (φ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hA0 : Integrable (A 0) volume := by
    convert! (Lp.memLp u).integrable_mul (φ.memLp 2 volume) using 1 <;>
      first | rfl | (funext x; simp only [A, zero_smul, sub_zero, Pi.mul_apply])
  have hDmeas : AEStronglyMeasurable (A' 0) volume := by
    convert! ((Lp.memLp u).aestronglyMeasurable.mul hD.aestronglyMeasurable).neg using 1 <;>
      first | rfl | (funext x; simp only [A', zero_smul, sub_zero, Pi.neg_apply, Pi.mul_apply])
  have hderiv (h : ℝ) (x : E) : HasDerivAt (fun t => A t x) (A' h x) h := by
    have hpath : HasDerivAt (fun t : ℝ => x - t • v) (-v) h := by
      convert! (hasDerivAt_const h x).sub ((hasDerivAt_id h).smul_const v) using 1 <;>
        first | rfl | simp only [one_smul, zero_sub, Pi.sub_apply, id_eq]
    have htest : HasDerivAt (fun t : ℝ => φ (x - t • v))
        (fderiv ℝ φ (x - h • v) (-v)) h :=
      (φ.differentiable (x - h • v)).hasFDerivAt.comp_hasDerivAt h hpath
    simpa only [A, A', map_neg, mul_neg] using htest.const_mul (u x)
  have hdom (x : E) (h : ℝ) (_hh : h ∈ Ioo (-1 : ℝ) 1) : ‖A' h x‖ ≤ dominator x := by
    simp only [A', dominator, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB (x - h • v)) (norm_nonneg _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := A) (F' := A') (bound := dominator)
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas) hA0 hDmeas
    (Eventually.of_forall hdom) hbound
    (Eventually.of_forall (fun x h _ => hderiv h x))
  simpa only [A, A', zero_smul, sub_zero, integral_neg] using h.2

theorem tendsto_inner_differenceQuotient_of_integrable (u : ScalarL2 n)
    (hu : Integrable (u : E → ℝ) volume) (v : E) (φ : 𝓢(E, ℝ)) :
    Tendsto (fun h => inner ℝ (differenceQuotient u v h) (φ.toLp 2 volume))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-(∫ x, u x * fderiv ℝ φ x v))) := by
  have heq : (fun h : ℝ => inner ℝ (differenceQuotient u v h) (φ.toLp 2 volume)) =
      slope (fun h : ℝ => ∫ x, u x * φ (x - h • v)) 0 := by
    funext h
    rw [inner_differenceQuotient_schwartz, slope_def_field]
    simp only [zero_smul, sub_zero, div_eq_mul_inv]
    ring
  rw [heq]
  exact (hasDerivAt_test_translation_pairing_of_integrable u hu v φ).tendsto_slope

theorem exists_weakDerivative_of_bounded_differenceQuotients_integrable
    (u : ScalarL2 n) (hu : Integrable (u : E → ℝ) volume) (v : E) {C : ℝ}
    (hbound : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖differenceQuotient u v h‖ ≤ C) :
    ∃ d : ScalarL2 n, ‖d‖ ≤ C ∧ ∀ φ : 𝓢(E, ℝ),
      inner ℝ d (φ.toLp 2 volume) = -(∫ x, u x * fderiv ℝ φ x v) := by
  let ell : ℝ → WeakDual ℝ (ScalarL2 n) := fun h =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (ScalarL2 n)
      (differenceQuotient u v h))
  have hmem : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ell h ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (ScalarL2 n)) C := by
    filter_upwards [hbound] with h hh
    simpa only [mem_preimage, mem_closedBall, dist_zero_right, ell,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hh
  have hcompact : IsCompact
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (ScalarL2 n)) C) :=
    WeakDual.isCompact_closedBall (0 : StrongDual ℝ (ScalarL2 n)) C
  obtain ⟨L, hL, hcluster⟩ :=
    hcompact.exists_mapClusterPt (Filter.tendsto_principal.mpr hmem)
  let d : ScalarL2 n := (InnerProductSpace.toDual ℝ (ScalarL2 n)).symm
    (WeakDual.toStrongDual L)
  refine ⟨d, ?_, ?_⟩
  · simpa only [mem_preimage, mem_closedBall, dist_zero_right, d,
      LinearIsometryEquiv.norm_map] using hL
  · intro φ
    have htest : MapClusterPt (L (φ.toLp 2 volume)) (𝓝[≠] (0 : ℝ))
        (fun h => inner ℝ (differenceQuotient u v h) (φ.toLp 2 volume)) := by
      simpa only [Function.comp_def, ell, StrongDual.toWeakDual_apply,
        InnerProductSpace.toDual_apply_apply] using
          MapClusterPt.continuousAt_comp
            (WeakDual.eval_continuous (φ.toLp 2 volume)).continuousAt hcluster
    have heq : L (φ.toLp 2 volume) = -(∫ x, u x * fderiv ℝ φ x v) :=
      eq_of_nhds_neBot (htest.clusterPt.mono
        (tendsto_inner_differenceQuotient_of_integrable u hu v φ)).neBot
    simpa only [d, InnerProductSpace.toDual_symm_apply, WeakDual.toStrongDual_apply] using heq

theorem exists_weakCoordinateDerivative_of_bounded_differenceQuotients_integrable
    (u : ScalarL2 n) (hu : Integrable (u : E → ℝ) volume) (j : Fin n) {C : ℝ}
    (hbound : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ‖differenceQuotient u (EuclideanSpace.single j 1) h‖ ≤ C) :
    ∃ d : ScalarL2 n, ‖d‖ ≤ C ∧ ∀ φ : 𝓢(E, ℝ),
      inner ℝ d (φ.toLp 2 volume) =
        -(∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
  exists_weakDerivative_of_bounded_differenceQuotients_integrable u hu
    (EuclideanSpace.single j 1) hbound

section WeakApproximation

open EuclideanMollificationNative

variable {ε : ℝ}

theorem mollify_integral (hε : 0 < ε) (u : ScalarL2 n) (x : E) :
    mollify hε u x = ∫ y, mollifier hε y * u (x - y) := by
  simpa only [Lp.toLp_coeFn] using mollify_toLp_eq_integral hε (Lp.memLp u) x

theorem mollify_kernel_integral (hε : 0 < ε) (u : ScalarL2 n) (x : E) :
    mollify hε u x = ∫ y, u y * mollifier hε (y - x) := by
  have htrans := (mollifier_memLp (n := n) hε).comp_measurePreserving
    (measurePreserving_add_right volume (-x))
  change inner ℝ (Lp.compMeasurePreserving (fun y : E => y + -x)
    (measurePreserving_add_right volume (-x))
    ((mollifier_memLp hε).toLp (mollifier hε))) u = _
  rw [Lp.toLp_compMeasurePreserving, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [htrans.coeFn_toLp] with y hy
  rw [hy]
  simp only [Function.comp_apply, sub_eq_add_neg, Real.inner_apply, mul_comm]

private theorem integrable_mollifier_difference (hε : 0 < ε) (u : ScalarL2 n) (x : E) :
    Integrable (fun y => mollifier hε y * (u (x - y) - u x)) volume := by
  have hshift := (Lp.memLp u).comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hm : Integrable (fun y => mollifier hε y * u (x - y)) volume := by
    convert! (mollifier_memLp hε).integrable_mul hshift using 1
  have h := hm.sub ((mollifier_integrable hε).mul_const (u x))
  convert! h using 1
  funext y
  simp only [Pi.sub_apply, mul_sub]

private theorem integrable_mollifier_difference_sq (hε : 0 < ε) (u : ScalarL2 n) (x : E) :
    Integrable (fun y => mollifier hε y * (u (x - y) - u x) ^ 2) volume := by
  obtain ⟨B, hB⟩ := (mollifier_compactSupport (n := n) hε).exists_bound_of_continuous
    (mollifier_continuous hε)
  have hshift := (Lp.memLp u).comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hm : Integrable (fun y => mollifier hε y * u (x - y)) volume := by
    convert! (mollifier_memLp hε).integrable_mul hshift using 1
  have hs : Integrable (fun y => mollifier hε y * u (x - y) ^ 2) volume :=
    hshift.integrable_sq.bdd_mul (mollifier_continuous hε).aestronglyMeasurable
      (Eventually.of_forall hB)
  have h := (hs.sub (hm.const_mul (2 * u x))).add
    ((mollifier_integrable hε).mul_const (u x ^ 2))
  apply h.congr
  exact Eventually.of_forall (fun y => by simp only [Pi.add_apply, Pi.sub_apply]; ring)

theorem mollify_sub_integral (hε : 0 < ε) (u : ScalarL2 n) (x : E) :
    mollify hε u x - u x = ∫ y, mollifier hε y * (u (x - y) - u x) := by
  have hshift := (Lp.memLp u).comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hm : Integrable (fun y => mollifier hε y * u (x - y)) volume := by
    convert! (mollifier_memLp hε).integrable_mul hshift using 1
  rw [mollify_integral]
  simp_rw [mul_sub]
  rw [integral_sub hm ((mollifier_integrable hε).mul_const (u x)),
    integral_mul_const, mollifier_integral, one_mul]

theorem mollify_sub_sq_le_integral (hε : 0 < ε) (u : ScalarL2 n) (x : E) :
    (mollify hε u x - u x) ^ 2 ≤
      ∫ y, mollifier hε y * (u (x - y) - u x) ^ 2 := by
  rw [mollify_sub_integral]
  exact weighted_integral_sq_le (mollifier_integrable hε)
    (integrable_mollifier_difference hε u x) (integrable_mollifier_difference_sq hε u x)
    (mollifier_nonneg hε) (mollifier_integral hε)

theorem integral_translation_difference_sq (u : ScalarL2 n) (y : E) :
    (∫ x, (u (x - y) - u x) ^ 2) = ‖translateLp (-y) u - u‖ ^ 2 := by
  rw [scalarLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (translateLp (-y) u) u, translateLp_ae_eq (-y) u]
    with x hsub htrans
  rw [hsub]
  change (u (x - y) - u x) ^ 2 = (translateLp (-y) u x - u x) ^ 2
  rw [htrans]
  simp only [sub_eq_add_neg]

theorem integrable_mollifier_translation_sq (hε : 0 < ε) (u : ScalarL2 n) :
    Integrable (fun p : E × E => mollifier hε p.1 * (u (p.2 - p.1) - u p.2) ^ 2)
      (volume.prod volume) := by
  have hm : StronglyMeasurable
      (fun p : E × E => mollifier hε p.1 * (u (p.2 - p.1) - u p.2) ^ 2) :=
    ((mollifier_continuous hε).stronglyMeasurable.comp_measurable measurable_fst).mul
      ((((Lp.stronglyMeasurable u).comp_measurable (measurable_snd.sub measurable_fst)).sub
        ((Lp.stronglyMeasurable u).comp_measurable measurable_snd)).pow 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Eventually.of_forall
    intro y
    have hd := ((Lp.memLp u).comp_measurePreserving
      (measurePreserving_add_right volume (-y))).sub (Lp.memLp u)
    simpa only [Function.comp_apply, Pi.sub_apply, sub_eq_add_neg] using
      hd.integrable_sq.const_mul (mollifier hε y)
  · have heq : (fun y : E => ∫ x, ‖mollifier hε y * (u (x - y) - u x) ^ 2‖) =
        (fun y : E => mollifier hε y * ‖translateLp (-y) u - u‖ ^ 2) := by
      funext y
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg hε y),
        abs_pow, sq_abs, integral_const_mul, integral_translation_difference_sq]
    rw [heq]
    exact integrable_mollifier_mul_continuous hε
      ((((continuous_translateLp u).comp continuous_neg).sub continuous_const).norm.pow 2)

theorem memLp_mollify_sub (hε : 0 < ε) (u : ScalarL2 n) :
    MemLp (fun x => mollify hε u x - u x) 2 volume := by
  have hm := (continuous_mollify hε u).aestronglyMeasurable.sub (Lp.aestronglyMeasurable u)
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrable_mollifier_translation_sq hε u).integral_prod_right.mono'
    (hm.pow 2)
  apply Eventually.of_forall
  intro x
  change ‖(mollify hε u x - u x) ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  exact mollify_sub_sq_le_integral hε u x

theorem memLp_mollify (hε : 0 < ε) (u : ScalarL2 n) : MemLp (mollify hε u) 2 volume := by
  have h := (memLp_mollify_sub hε u).add (Lp.memLp u)
  convert! h using 1
  funext x
  simp only [Pi.add_apply, sub_add_cancel]

def mollifyL2 (hε : 0 < ε) (u : ScalarL2 n) : ScalarL2 n :=
  (memLp_mollify hε u).toLp (mollify hε u)

theorem mollifyL2_ae_eq (hε : 0 < ε) (u : ScalarL2 n) :
    mollifyL2 hε u =ᵐ[volume] mollify hε u := (memLp_mollify hε u).coeFn_toLp

theorem norm_mollifyL2_sub_sq_le (hε : 0 < ε) (u : ScalarL2 n) :
    ‖mollifyL2 hε u - u‖ ^ 2 ≤
      ∫ y, mollifier hε y * ‖translateLp (-y) u - u‖ ^ 2 := by
  have hi := integrable_mollifier_translation_sq hε u
  calc
    _ = ∫ x, (mollify hε u x - u x) ^ 2 := by
      rw [scalarLp_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (mollifyL2 hε u) u, mollifyL2_ae_eq hε u]
        with x hsub hm
      simp only [hsub, Pi.sub_apply, hm]
    _ ≤ ∫ x, ∫ y, mollifier hε y * (u (x - y) - u x) ^ 2 :=
      integral_mono (memLp_mollify_sub hε u).integrable_sq hi.integral_prod_right
        (mollify_sub_sq_le_integral hε u)
    _ = ∫ y, ∫ x, mollifier hε y * (u (x - y) - u x) ^ 2 :=
      (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        dsimp only
        rw [integral_const_mul, integral_translation_difference_sq])

theorem norm_mollifyL2_sub_le_of_translate (hε : 0 < ε) (u : ScalarL2 n)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ y : E, ‖y‖ ≤ ε → ‖translateLp (-y) u - u‖ ≤ δ) :
    ‖mollifyL2 hε u - u‖ ≤ δ := by
  apply (sq_le_sq₀ (norm_nonneg _) hδ).mp
  apply (norm_mollifyL2_sub_sq_le hε u).trans
  calc
    _ ≤ ∫ y, mollifier hε y * δ ^ 2 := by
      apply integral_mono
        (integrable_mollifier_mul_continuous hε
          ((((continuous_translateLp u).comp continuous_neg).sub continuous_const).norm.pow 2))
        ((mollifier_integrable hε).mul_const _)
      intro y
      by_cases hy : mollifier hε y = 0
      · simp only [hy, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (norm_nonneg _) hδ).mpr
            (hbound y (norm_le_of_mollifier_ne_zero hε hy))) (mollifier_nonneg hε y)
    _ = δ ^ 2 := by rw [integral_mul_const, mollifier_integral, one_mul]

theorem translateLp_zero (u : ScalarL2 n) : translateLp (0 : E) u = u := by
  apply Lp.ext
  simpa only [add_zero] using translateLp_ae_eq (0 : E) u

theorem tendsto_mollifyL2 (eps : ℕ → ℝ) (heps : ∀ j, 0 < eps j)
    (heps0 : Tendsto eps atTop (𝓝 0)) (u : ScalarL2 n) :
    Tendsto (fun j => mollifyL2 (heps j) u) atTop (𝓝 u) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hc : Continuous (fun y : E => ‖translateLp (-y) u - u‖) :=
    (((continuous_translateLp u).comp continuous_neg).sub continuous_const).norm
  have hz : ‖translateLp (-(0 : E)) u - u‖ = 0 := by
    rw [neg_zero, translateLp_zero, sub_self, norm_zero]
  have hnear : ∀ᶠ y in 𝓝 (0 : E), ‖translateLp (-y) u - u‖ < δ / 2 :=
    (hc.continuousAt.tendsto.eventually (gt_mem_nhds (by rw [hz]; linarith)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  filter_upwards [heps0.eventually (gt_mem_nhds hr)] with j hj
  rw [dist_eq_norm]
  apply (norm_mollifyL2_sub_le_of_translate (heps j) u (by linarith) ?_).trans_lt
    (half_lt_self hδ)
  intro y hy
  exact (hball (by simpa only [Metric.mem_ball, dist_zero_right] using hy.trans_lt hj)).le

theorem contDiff_mollify (hε : 0 < ε) (u : ScalarL2 n) :
    ContDiff ℝ ∞ (mollify hε u) := by
  have heq : mollify hε u =
      (mollifier hε ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (u : E → ℝ)) := by
    funext x
    rw [mollify_integral]
    rfl
  rw [heq]
  exact (mollifier_compactSupport hε).contDiff_convolution_left _
    (mollifier_contDiff hε) ((Lp.memLp u).locallyIntegrable (by norm_num))

theorem mollify_eq_zero_off_cthickening (hε : 0 < ε) (u : ScalarL2 n) {K : Set E}
    (huK : ∀ᵐ y ∂volume, y ∉ K → u y = 0) {x : E} (hx : x ∉ cthickening ε K) :
    mollify hε u x = 0 := by
  rw [mollify_integral]
  apply integral_eq_zero_of_ae
  have hshift := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae huK
  filter_upwards [hshift] with y hy
  change mollifier hε y * u (x - y) = 0
  by_cases hρ : mollifier hε y = 0
  · rw [hρ, zero_mul]
  · have hnot : x - y ∉ K := by
      intro hK
      apply hx
      apply mem_cthickening_of_dist_le x (x - y) ε K hK
      have heq : x - (x - y) = y := by abel
      rw [dist_eq_norm, heq]
      exact norm_le_of_mollifier_ne_zero hε hρ
    rw [hy hnot, mul_zero]

theorem tsupport_mollify_subset (hε : 0 < ε) (u : ScalarL2 n) {K : Set E}
    (huK : ∀ᵐ y ∂volume, y ∉ K → u y = 0) :
    tsupport (mollify hε u) ⊆ cthickening ε K := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  by_contra hxK
  exact hx (mollify_eq_zero_off_cthickening hε u huK hxK)

theorem hasCompactSupport_mollify (hε : 0 < ε) (u : ScalarL2 n) {K : Set E}
    (hK : IsCompact K) (huK : ∀ᵐ y ∂volume, y ∉ K → u y = 0) :
    HasCompactSupport (mollify hε u) :=
  (hK.cthickening (r := ε)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_mollify_subset hε u huK)

def mollifySchwartz (hε : 0 < ε) (u : ScalarL2 n) {K : Set E}
    (hK : IsCompact K) (huK : ∀ᵐ y ∂volume, y ∉ K → u y = 0) : 𝓢(E, ℝ) :=
  (hasCompactSupport_mollify hε u hK huK).toSchwartzMap (contDiff_mollify hε u)

theorem mollifySchwartz_toLp (hε : 0 < ε) (u : ScalarL2 n) {K : Set E}
    (hK : IsCompact K) (huK : ∀ᵐ y ∂volume, y ∉ K → u y = 0) :
    (mollifySchwartz hε u hK huK).toLp 2 volume = mollifyL2 hε u := by
  apply Lp.ext
  exact ((mollifySchwartz hε u hK huK).coeFn_toLp 2 volume).trans
    (mollifyL2_ae_eq hε u).symm

theorem fderiv_mollify_of_weak_pairing (hε : 0 < ε) (u d : ScalarL2 n) (v : E)
    (hweak : ∀ φ : 𝓢(E, ℝ),
      inner ℝ d (φ.toLp 2 volume) = -(∫ y, u y * fderiv ℝ φ y v)) (x : E) :
    fderiv ℝ (mollify hε u) x v = mollify hε d x := by
  let φ : 𝓢(E, ℝ) := SchwartzMap.compSubConstCLM ℝ x
    ((mollifier_compactSupport hε).toSchwartzMap (mollifier_contDiff hε))
  have hφ (y : E) : φ y = mollifier hε (y - x) := rfl
  have hkernel : inner ℝ d (φ.toLp 2 volume) = mollify hε d x := by
    rw [inner_schwartz, mollify_kernel_integral]
    rfl
  have heq : (fun t : ℝ => ∫ y, u y * φ (y - t • v)) =
      (fun t : ℝ => mollify hε u (x + t • v)) := by
    funext t
    rw [mollify_kernel_integral]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    dsimp only
    rw [hφ]
    congr 2
    abel
  have hφcompact : HasCompactSupport φ :=
    (mollifier_compactSupport hε).comp_homeomorph (Homeomorph.subRight x)
  have hd := hasDerivAt_test_translation_pairing u v φ hφcompact
  rw [heq, ← hweak φ, hkernel] at hd
  have hc : HasDerivAt (fun t : ℝ => mollify hε u (x + t • v))
      (fderiv ℝ (mollify hε u) x v) 0 := by
    convert!
      (((contDiff_mollify hε u).differentiable (by simp))
        (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_segment x v 0)
      using 1 <;> first | rfl | simp only [zero_smul, add_zero]
  exact hc.unique hd

theorem fderiv_mollify_of_weak_derivative (hε : 0 < ε) (u d : ScalarL2 n)
    (hu : Integrable (u : E → ℝ) volume) (v : E)
    (hweak : ∀ φ : 𝓢(E, ℝ),
      inner ℝ d (φ.toLp 2 volume) = -(∫ y, u y * fderiv ℝ φ y v)) (x : E) :
    fderiv ℝ (mollify hε u) x v = mollify hε d x :=
  fderiv_mollify_of_weak_pairing hε u d v hweak x

theorem lineDeriv_mollifySchwartz_toLp (hε : 0 < ε) (u d : ScalarL2 n)
    {K : Set E} (hK : IsCompact K) (huK : ∀ᵐ y ∂volume, y ∉ K → u y = 0)
    (v : E) (hweak : ∀ φ : 𝓢(E, ℝ),
      inner ℝ d (φ.toLp 2 volume) = -(∫ y, u y * fderiv ℝ φ y v)) :
    (∂_{v} (mollifySchwartz hε u hK huK)).toLp 2 volume = mollifyL2 hε d := by
  apply Lp.ext
  filter_upwards [(∂_{v} (mollifySchwartz hε u hK huK)).coeFn_toLp 2 volume,
    mollifyL2_ae_eq hε d] with x hleft hright
  rw [hleft, hright, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (mollify hε u) x v = mollify hε d x
  exact fderiv_mollify_of_weak_derivative hε u d
    (integrable_of_ae_compact_support u hK huK) v hweak x

theorem exists_schwartz_approximation_of_weak_derivatives
    (u : ScalarL2 n) (d : Fin n → ScalarL2 n) {K : Set E}
    (hK : IsCompact K) (huK : ∀ᵐ y ∂volume, y ∉ K → u y = 0)
    (hweak : ∀ i (φ : 𝓢(E, ℝ)),
      inner ℝ (d i) (φ.toLp 2 volume) =
        -(∫ y, u y * fderiv ℝ φ y (EuclideanSpace.single i 1)))
    {r : ℝ} (hr : 0 < r) :
    ∃ S : ℕ → 𝓢(E, ℝ),
      (∀ j, HasCompactSupport (S j) ∧ tsupport (S j) ⊆ cthickening r K) ∧
      Tendsto (fun j => (S j).toLp 2 volume) atTop (𝓝 u) ∧
      ∀ i : Fin n, Tendsto (fun j => (∂_{EuclideanSpace.single i (1 : ℝ)} (S j)).toLp 2 volume)
        atTop (𝓝 (d i)) := by
  let eps : ℕ → ℝ := fun j => r / ((j : ℝ) + 1)
  have heps (j : ℕ) : 0 < eps j := div_pos hr (by positivity)
  have hepsr (j : ℕ) : eps j ≤ r := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps, mul_one_div, mul_zero] using
      (tendsto_const_nhds (x := r)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let S : ℕ → 𝓢(E, ℝ) := fun j => mollifySchwartz (heps j) u hK huK
  refine ⟨S, ?_, ?_, ?_⟩
  · intro j
    refine ⟨hasCompactSupport_mollify (heps j) u hK huK, ?_⟩
    exact (tsupport_mollify_subset (heps j) u huK).trans (cthickening_mono (hepsr j) K)
  · simpa only [S, mollifySchwartz_toLp] using tendsto_mollifyL2 eps heps heps0 u
  · intro i
    have heq : (fun j => (∂_{EuclideanSpace.single i (1 : ℝ)} (S j)).toLp 2 volume) =
        (fun j => mollifyL2 (heps j) (d i)) := by
      funext j
      exact lineDeriv_mollifySchwartz_toLp (heps j) u (d i) hK huK
        (EuclideanSpace.single i 1) (hweak i)
    rw [heq]
    exact tendsto_mollifyL2 eps heps heps0 (d i)

def orderedSchwartzDerivative : List (Fin n) → 𝓢(E, ℝ) → 𝓢(E, ℝ)
  | [], φ => φ
  | i :: w, φ => ∂_{EuclideanSpace.single i (1 : ℝ)} (orderedSchwartzDerivative w φ)

theorem orderedSchwartzDerivative_append (w v : List (Fin n)) (φ : 𝓢(E, ℝ)) :
    orderedSchwartzDerivative (w ++ v) φ =
      orderedSchwartzDerivative w (orderedSchwartzDerivative v φ) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, orderedSchwartzDerivative, ih]

theorem finite_weakJet_pairing (q : List (Fin n) → ScalarL2 n) (k : ℕ)
    (hweak : ∀ w : List (Fin n), w.length < k → ∀ i (φ : 𝓢(E, ℝ)),
      inner ℝ (q (i :: w)) (φ.toLp 2 volume) =
        -inner ℝ (q w) ((∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume))
    (w : List (Fin n)) (hw : w.length ≤ k) (φ : 𝓢(E, ℝ)) :
    inner ℝ (q w) (φ.toLp 2 volume) = (-1 : ℝ) ^ w.length *
      inner ℝ (q []) ((orderedSchwartzDerivative w.reverse φ).toLp 2 volume) := by
  induction w generalizing φ with
  | nil => simp only [List.length_nil, pow_zero, one_mul, List.reverse_nil,
      orderedSchwartzDerivative]
  | cons i w ih =>
    have hwk : w.length < k := by simp only [List.length_cons] at hw; omega
    rw [hweak w hwk i φ, ih (by omega)]
    simp only [List.length_cons, List.reverse_cons, orderedSchwartzDerivative_append,
      orderedSchwartzDerivative, pow_succ]
    ring

theorem orderedSchwartzDerivative_mollifySchwartz
    (hε : 0 < ε) (q : List (Fin n) → ScalarL2 n) (k : ℕ)
    {K : Set E} (hK : IsCompact K) (hqK : ∀ᵐ y ∂volume, y ∉ K → q [] y = 0)
    (hweak : ∀ w : List (Fin n), w.length < k → ∀ i (φ : 𝓢(E, ℝ)),
      inner ℝ (q (i :: w)) (φ.toLp 2 volume) =
        -(∫ y, q w y * fderiv ℝ φ y (EuclideanSpace.single i 1)))
    (w : List (Fin n)) (hw : w.length ≤ k) (x : E) :
    orderedSchwartzDerivative w (mollifySchwartz hε (q []) hK hqK) x =
      mollify hε (q w) x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    have hwk : w.length < k := by simp only [List.length_cons] at hw; omega
    have heq : (orderedSchwartzDerivative w (mollifySchwartz hε (q []) hK hqK) : E → ℝ) =
        mollify hε (q w) := funext (fun y => ih (by omega) y)
    change fderiv ℝ
      (orderedSchwartzDerivative w (mollifySchwartz hε (q []) hK hqK)) x
        (EuclideanSpace.single i (1 : ℝ)) = _
    rw [heq]
    exact fderiv_mollify_of_weak_pairing hε (q w) (q (i :: w))
      (EuclideanSpace.single i 1) (hweak w hwk i) x

theorem orderedSchwartzDerivative_mollifySchwartz_toLp
    (hε : 0 < ε) (q : List (Fin n) → ScalarL2 n) (k : ℕ)
    {K : Set E} (hK : IsCompact K) (hqK : ∀ᵐ y ∂volume, y ∉ K → q [] y = 0)
    (hweak : ∀ w : List (Fin n), w.length < k → ∀ i (φ : 𝓢(E, ℝ)),
      inner ℝ (q (i :: w)) (φ.toLp 2 volume) =
        -(∫ y, q w y * fderiv ℝ φ y (EuclideanSpace.single i 1)))
    (w : List (Fin n)) (hw : w.length ≤ k) :
    (orderedSchwartzDerivative w (mollifySchwartz hε (q []) hK hqK)).toLp 2 volume =
      mollifyL2 hε (q w) := by
  apply Lp.ext
  filter_upwards
    [(orderedSchwartzDerivative w (mollifySchwartz hε (q []) hK hqK)).coeFn_toLp 2 volume,
      mollifyL2_ae_eq hε (q w)] with x hleft hright
  rw [hleft, hright]
  exact orderedSchwartzDerivative_mollifySchwartz hε q k hK hqK hweak w hw x

theorem exists_schwartz_approximation_of_finite_weak_jets
    (q : List (Fin n) → ScalarL2 n) (k : ℕ)
    {K : Set E} (hK : IsCompact K) (hqK : ∀ᵐ y ∂volume, y ∉ K → q [] y = 0)
    (hweak : ∀ w : List (Fin n), w.length < k → ∀ i (φ : 𝓢(E, ℝ)),
      inner ℝ (q (i :: w)) (φ.toLp 2 volume) =
        -(∫ y, q w y * fderiv ℝ φ y (EuclideanSpace.single i 1)))
    {r : ℝ} (hr : 0 < r) :
    ∃ S : ℕ → 𝓢(E, ℝ),
      (∀ j, HasCompactSupport (S j) ∧ tsupport (S j) ⊆ cthickening r K) ∧
      ∀ w : List (Fin n), w.length ≤ k →
        Tendsto (fun j => (orderedSchwartzDerivative w (S j)).toLp 2 volume)
          atTop (𝓝 (q w)) := by
  let eps : ℕ → ℝ := fun j => r / ((j : ℝ) + 1)
  have heps (j : ℕ) : 0 < eps j := div_pos hr (by positivity)
  have hepsr (j : ℕ) : eps j ≤ r := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps, mul_one_div, mul_zero] using
      (tendsto_const_nhds (x := r)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let S : ℕ → 𝓢(E, ℝ) := fun j => mollifySchwartz (heps j) (q []) hK hqK
  refine ⟨S, ?_, ?_⟩
  · intro j
    refine ⟨hasCompactSupport_mollify (heps j) (q []) hK hqK, ?_⟩
    exact (tsupport_mollify_subset (heps j) (q []) hqK).trans (cthickening_mono (hepsr j) K)
  · intro w hw
    have heq : (fun j => (orderedSchwartzDerivative w (S j)).toLp 2 volume) =
        fun j => mollifyL2 (heps j) (q w) := by
      funext j
      exact orderedSchwartzDerivative_mollifySchwartz_toLp (heps j) q k hK hqK hweak w hw
    rw [heq]
    exact tendsto_mollifyL2 eps heps heps0 (q w)

end WeakApproximation

theorem exists_continuous_weakJet
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (U : X →L[ℝ] ScalarL2 n) (w : List (Fin n))
    (hex : ∀ z : X, ∃ d : ScalarL2 n, ∀ φ : 𝓢(E, ℝ),
      inner ℝ d (φ.toLp 2 volume) = (-1 : ℝ) ^ w.length *
        inner ℝ (U z) ((orderedSchwartzDerivative w.reverse φ).toLp 2 volume)) :
    ∃ D : X →L[ℝ] ScalarL2 n, ∀ z : X, ∀ φ : 𝓢(E, ℝ),
      inner ℝ (D z) (φ.toLp 2 volume) = (-1 : ℝ) ^ w.length *
        inner ℝ (U z) ((orderedSchwartzDerivative w.reverse φ).toLp 2 volume) := by
  classical
  choose d hd using hex
  have hext {a b : ScalarL2 n}
      (h : ∀ φ : 𝓢(E, ℝ), inner ℝ a (φ.toLp 2 volume) =
        inner ℝ b (φ.toLp 2 volume)) : a = b :=
    (SchwartzMap.denseRange_toLpCLM (F := ℝ) (μ := (volume : Measure E))
      (by norm_num : (2 : ENNReal) ≠ ⊤)).eq_of_inner_left ℝ h
  let D : X →ₗ[ℝ] ScalarL2 n := {
    toFun := d
    map_add' := by
      intro x y
      apply hext
      intro φ
      rw [hd, map_add, inner_add_left, inner_add_left, hd, hd, mul_add]
    map_smul' := by
      intro c x
      apply hext
      intro φ
      simp only [hd, map_smul, real_inner_smul_left, RingHom.id_apply]
      ring }
  have hD : Continuous D := by
    apply D.continuous_of_seq_closed_graph
    intro z x y hz hy
    apply hext
    intro φ
    have hleft : Tendsto (fun j => inner ℝ (D (z j)) (φ.toLp 2 volume))
        atTop (𝓝 (inner ℝ y (φ.toLp 2 volume))) :=
      hy.inner tendsto_const_nhds
    have hright : Tendsto (fun j => (-1 : ℝ) ^ w.length *
        inner ℝ (U (z j)) ((orderedSchwartzDerivative w.reverse φ).toLp 2 volume))
        atTop (𝓝 ((-1 : ℝ) ^ w.length *
          inner ℝ (U x) ((orderedSchwartzDerivative w.reverse φ).toLp 2 volume))) :=
      tendsto_const_nhds.mul (((U.continuous.tendsto x).comp hz).inner tendsto_const_nhds)
    have hpair : (fun j => inner ℝ (D (z j)) (φ.toLp 2 volume)) =
        fun j => (-1 : ℝ) ^ w.length *
          inner ℝ (U (z j)) ((orderedSchwartzDerivative w.reverse φ).toLp 2 volume) :=
      funext (fun j => hd (z j) φ)
    rw [← hpair] at hright
    exact (tendsto_nhds_unique hleft hright).trans (hd x φ).symm
  exact ⟨⟨D, hD⟩, hd⟩

theorem exists_continuous_finite_weakJets
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (U : X →L[ℝ] ScalarL2 n) (q : X → List (Fin n) → ScalarL2 n) (k : ℕ)
    (hzero : ∀ z : X, q z [] = U z)
    (hweak : ∀ (z : X) (w : List (Fin n)), w.length < k →
      ∀ i (φ : 𝓢(E, ℝ)),
        inner ℝ (q z (i :: w)) (φ.toLp 2 volume) =
          -inner ℝ (q z w) ((∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume)) :
    ∃ D : (w : List (Fin n)) → w.length ≤ k → X →L[ℝ] ScalarL2 n,
      ∀ (w : List (Fin n)) (hw : w.length ≤ k) (z : X), D w hw z = q z w := by
  classical
  have hpair (w : List (Fin n)) (hw : w.length ≤ k) (z : X) (φ : 𝓢(E, ℝ)) :
      inner ℝ (q z w) (φ.toLp 2 volume) = (-1 : ℝ) ^ w.length *
        inner ℝ (U z) ((orderedSchwartzDerivative w.reverse φ).toLp 2 volume) := by
    simpa only [hzero z] using finite_weakJet_pairing (q z) k (hweak z) w hw φ
  have hex (w : List (Fin n)) (hw : w.length ≤ k) :
      ∃ D : X →L[ℝ] ScalarL2 n, ∀ z : X, D z = q z w := by
    obtain ⟨D, hD⟩ := exists_continuous_weakJet U w
      (fun z => ⟨q z w, hpair w hw z⟩)
    refine ⟨D, fun z => ?_⟩
    apply (SchwartzMap.denseRange_toLpCLM (F := ℝ)
      (μ := (volume : Measure E)) (by norm_num : (2 : ENNReal) ≠ ⊤)).eq_of_inner_left ℝ
    intro φ
    exact (hD z φ).trans (hpair w hw z φ).symm
  choose D hD using hex
  exact ⟨D, hD⟩

theorem exists_finite_weakJet_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (U : X →L[ℝ] ScalarL2 n) (q : X → List (Fin n) → ScalarL2 n) (k : ℕ)
    (hzero : ∀ z : X, q z [] = U z)
    (hweak : ∀ (z : X) (w : List (Fin n)), w.length < k →
      ∀ i (φ : 𝓢(E, ℝ)),
        inner ℝ (q z (i :: w)) (φ.toLp 2 volume) =
          -inner ℝ (q z w) ((∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : X) (w : List (Fin n)), w.length ≤ k →
      ‖q z w‖ ≤ C * ‖z‖ := by
  classical
  obtain ⟨D, hD⟩ := exists_continuous_finite_weakJets U q k hzero hweak
  let W := {w : List (Fin n) // w.length ≤ k}
  letI : Fintype W := (List.finite_length_le (Fin n) k).fintype
  let C : ℝ := 1 + ∑ w : W, ‖D w.val w.property‖
  have hsum : 0 ≤ ∑ w : W, ‖D w.val w.property‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro z w hw
  have hbound : ‖D w hw‖ ≤ C := by
    have hterm := Finset.single_le_sum (s := Finset.univ)
      (f := fun v : W => ‖D v.val v.property‖)
      (fun v _ => norm_nonneg _) (Finset.mem_univ (⟨w, hw⟩ : W))
    dsimp [C]
    linarith
  rw [← hD w hw z]
  exact ((D w hw).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg z))

end PoincareConjecture.DeTurckDomainRegularityNative

end
