import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalCoefficients
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalAbsorption
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaVariationalComparison
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.SecondDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup ((E × E) →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ ((E × E) →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup ((E × E) →L[ℝ] (E × E) →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ ((E × E) →L[ℝ] (E × E) →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



theorem suGradientParameters_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    IsCompact {q : ℝ × E | 0 ≤ q.1 ∧ q.1 ^ 2 + ‖q.2‖ ^ 2 = 1} := by
  have hc : IsClosed {q : ℝ × E | 0 ≤ q.1 ∧ q.1 ^ 2 + ‖q.2‖ ^ 2 = 1} :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_eq ((continuous_fst.pow 2).add (continuous_snd.norm.pow 2)) continuous_const)
  apply ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
    (isCompact_closedBall (0 : E) 1)).of_isClosed_subset hc
  intro q hq
  refine ⟨⟨hq.1, ?_⟩, ?_⟩
  · nlinarith [hq.2, sq_nonneg ‖q.2‖]
  · rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [hq.2, sq_nonneg q.1, norm_nonneg q.2]



theorem suGradientParameters_coercive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {c kappa t : ℝ} {v : E}
    (hB : kappa * ‖v‖ ^ 2 ≤ B v v) (hunit : t ^ 2 + ‖v‖ ^ 2 = 1) :
    min c kappa ≤ t ^ 2 * c + B v v := by
  calc
    _ = min c kappa * t ^ 2 + min c kappa * ‖v‖ ^ 2 := by
      rw [← mul_add, hunit, mul_one]
    _ ≤ c * t ^ 2 + kappa * ‖v‖ ^ 2 := add_le_add
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
    _ ≤ _ := by linarith



theorem suAlphaFlux_gradient_scaling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v)
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (alpha : ℝ) (v : E) :
    suAlphaFlux B c alpha v =
      t ^ (1 - 2 * alpha) • suAlphaFlux B (t ^ 2 * c) alpha (t • v) := by
  have hbase : 0 ≤ c + B v v := add_nonneg hc.le (hB v)
  have hquad : t ^ 2 * c + B (t • v) (t • v) = t ^ 2 * (c + B v v) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hpow : (t ^ 2) ^ (alpha - 1) = t ^ (2 * (alpha - 1)) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    norm_num
  have hweight : (t ^ 2 * c + B (t • v) (t • v)) ^ (alpha - 1) =
      t ^ (2 * (alpha - 1)) * (c + B v v) ^ (alpha - 1) := by
    rw [hquad, Real.mul_rpow (sq_nonneg _) hbase, hpow]
  have htone : t ^ (1 - 2 * alpha) * t ^ (2 * (alpha - 1)) * t = 1 := by
    rw [← Real.rpow_add ht, show 1 - 2 * alpha + 2 * (alpha - 1) = -1 by ring,
      Real.rpow_neg_one, inv_mul_cancel₀ ht.ne']
  ext w
  change 2 * alpha * (c + B v v) ^ (alpha - 1) * B v w =
    t ^ (1 - 2 * alpha) *
      (2 * alpha * (t ^ 2 * c + B (t • v) (t • v)) ^ (alpha - 1) * B (t • v) w)
  rw [hweight]
  simp only [map_smul, smul_apply, smul_eq_mul]
  calc
    _ = (t ^ (1 - 2 * alpha) * t ^ (2 * (alpha - 1)) * t) *
        (2 * alpha * (c + B v v) ^ (alpha - 1) * B v w) := by rw [htone, one_mul]
    _ = _ := by ring



theorem suGradientParameters_normalize
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) :
    ∃ t : ℝ, 0 < t ∧ t ^ 2 + ‖t • v‖ ^ 2 = 1 ∧ t ≤ 1 := by
  let t := (Real.sqrt (1 + ‖v‖ ^ 2))⁻¹
  have hs : 0 < Real.sqrt (1 + ‖v‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have ht : 0 < t := inv_pos.mpr hs
  have hs2 := Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖v‖ ^ 2)
  have heq : t ^ 2 + ‖t • v‖ ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow]
    dsimp only [t]
    field_simp
    nlinarith
  refine ⟨t, ht, heq, ?_⟩
  nlinarith [sq_nonneg ‖t • v‖]



theorem suNormalizedCoefficient_derivative_bound
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set P} (hK : IsCompact K) (A : P × (ℝ × E) → F)
    (hA : ∀ z ∈ K ×ˢ {q : ℝ × E | 0 ≤ q.1 ∧ q.1 ^ 2 + ‖q.2‖ ^ 2 = 1},
      ContDiffAt ℝ 1 A z) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ t : ℝ, ∀ v : E,
      0 ≤ t → t ^ 2 + ‖v‖ ^ 2 = 1 → ‖fderiv ℝ A (x, t, v)‖ ≤ C := by
  have hc := hK.prod (suGradientParameters_compact (E := E))
  have hd : ContinuousOn (fderiv ℝ A)
      (K ×ˢ {q : ℝ × E | 0 ≤ q.1 ∧ q.1 ^ 2 + ‖q.2‖ ^ 2 = 1}) :=
    fun z hz => ((hA z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨C, hC⟩ := hc.bddAbove_image hd.norm
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro x hx t v ht hunit
  exact (hC (mem_image_of_mem _ ⟨hx, ht, hunit⟩)).trans
    ((le_max_left C 0).trans (by linarith))



theorem suNormalizedCoefficient_gradient_bound
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : P × (ℝ × E) → F) (x : P) (v : E) {t C : ℝ} (ht : 0 < t)
    (degree : ℝ) (hA : DifferentiableAt ℝ A (x, t, t • v))
    (hC : ‖fderiv ℝ A (x, t, t • v)‖ ≤ C) :
    DifferentiableAt ℝ (fun w => t ^ degree • A (x, t, t • w)) v ∧
      ‖fderiv ℝ (fun w => t ^ degree • A (x, t, t • w)) v‖ ≤
        C * t ^ (degree + 1) := by
  let L : E →L[ℝ] P × (ℝ × E) :=
    (0 : E →L[ℝ] P).prod ((0 : E →L[ℝ] ℝ).prod (t • ContinuousLinearMap.id ℝ E))
  have hL : ‖L‖ ≤ t := by
    apply L.opNorm_le_bound ht.le
    intro w
    simpa [L, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_of_pos ht] using
      mul_nonneg ht.le (norm_nonneg w)
  have harg : HasFDerivAt (fun w : E => (x, t, t • w)) L v :=
    (hasFDerivAt_const x v).prodMk
      ((hasFDerivAt_const t v).prodMk ((hasFDerivAt_id v).const_smul t))
  have hd := (hA.hasFDerivAt.comp v harg).const_smul (t ^ degree)
  change HasFDerivAt (fun w => t ^ degree • A (x, t, t • w))
    (t ^ degree • (fderiv ℝ A (x, t, t • v)).comp L) v at hd
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  have hpow := Real.rpow_pos_of_pos ht degree
  calc
    _ = t ^ degree * ‖(fderiv ℝ A (x, t, t • v)).comp L‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpow]
    _ ≤ t ^ degree * (‖fderiv ℝ A (x, t, t • v)‖ * ‖L‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hpow.le
    _ ≤ t ^ degree * (C * t) := mul_le_mul_of_nonneg_left
      (mul_le_mul hC hL (norm_nonneg L) ((norm_nonneg _).trans hC)) hpow.le
    _ = C * t ^ (degree + 1) := by rw [Real.rpow_add ht, Real.rpow_one]; ring



theorem suNormalizedCoefficient_base_bound
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set P} (hK : Convex ℝ K) (A : P × (ℝ × E) → F)
    (v : E) {t C : ℝ} (ht : 0 < t) (degree : ℝ)
    (hA : ∀ x ∈ K, DifferentiableAt ℝ A (x, t, v))
    (hC : ∀ x ∈ K, ‖fderiv ℝ A (x, t, v)‖ ≤ C)
    {x y : P} (hx : x ∈ K) (hy : y ∈ K) :
    ‖t ^ degree • A (y, t, v) - t ^ degree • A (x, t, v)‖ ≤
      C * t ^ degree * ‖y - x‖ := by
  let L : P →L[ℝ] P × (ℝ × E) := (ContinuousLinearMap.id ℝ P).prod 0
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro w
    simp [L, Prod.norm_def]
  have hd (z : P) (hz : z ∈ K) : HasFDerivAt (fun w => A (w, t, v))
      ((fderiv ℝ A (z, t, v)).comp L) z := by
    have harg : HasFDerivAt (fun w : P => (w, t, v)) L z :=
      (hasFDerivAt_id z).prodMk (hasFDerivAt_const (t, v) z)
    exact (hA z hz).hasFDerivAt.comp z harg
  have hb (z : P) (hz : z ∈ K) : ‖fderiv ℝ (fun w => A (w, t, v)) z‖ ≤ C := by
    rw [(hd z hz).fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left hL (norm_nonneg _)).trans (by simpa using hC z hz))
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hd z hz).differentiableAt) hb hK hx hy
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht degree)]
  exact (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ht.le degree)).trans_eq (by ring)



theorem suAlphaFlux_normalized_contDiffAt
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : P → E →L[ℝ] E →L[ℝ] ℝ) (c : P → ℝ) (alpha : ℝ)
    {x : P} {t : ℝ} {v : E} (hB : ContDiffAt ℝ 1 B x)
    (hc : ContDiffAt ℝ 1 c x) (hpos : 0 < t ^ 2 * c x + B x v v) :
    ContDiffAt ℝ 1
      (fun z : P × (ℝ × E) => suAlphaFlux (B z.1) (z.2.1 ^ 2 * c z.1) alpha z.2.2)
      (x, t, v) := by
  have hmetric : ContDiffAt ℝ 1 (fun z : P × (ℝ × E) => B z.1) (x, t, v) :=
    hB.comp _ contDiffAt_fst
  have hconstant : ContDiffAt ℝ 1 (fun z : P × (ℝ × E) => c z.1) (x, t, v) :=
    hc.comp _ contDiffAt_fst
  have hbase : ContDiffAt ℝ 1
      (fun z : P × (ℝ × E) => z.2.1 ^ 2 * c z.1 + B z.1 z.2.2 z.2.2)
      (x, t, v) := by fun_prop
  have hweight := hbase.rpow_const_of_ne (p := alpha - 1) hpos.ne'
  exact (contDiffAt_const.mul hweight).smul (hmetric.clm_apply (by fun_prop))



theorem suHomogeneousCoefficient_bounds
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set P} (hK : IsCompact K) (hconv : Convex ℝ K)
    (A : P → E → F) (N : P × (ℝ × E) → F) (degree : ℝ)
    (hN : ∀ z ∈ K ×ˢ {q : ℝ × E | 0 ≤ q.1 ∧ q.1 ^ 2 + ‖q.2‖ ^ 2 = 1},
      ContDiffAt ℝ 1 N z)
    (hscale : ∀ x ∈ K, ∀ t : ℝ, 0 < t → ∀ v : E,
      A x v = t ^ degree • N (x, t, t • v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : E, ∃ t : ℝ, 0 < t ∧ t ^ 2 + ‖t • v‖ ^ 2 = 1 ∧
      (∀ x ∈ K, DifferentiableAt ℝ (A x) v ∧
        ‖fderiv ℝ (A x) v‖ ≤ C * t ^ (degree + 1)) ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖A y v - A x v‖ ≤ C * t ^ degree * ‖y - x‖ := by
  obtain ⟨C, hC, hbound⟩ := suNormalizedCoefficient_derivative_bound hK N hN
  refine ⟨C, hC, fun v => ?_⟩
  obtain ⟨t, ht, hunit, _⟩ := suGradientParameters_normalize v
  refine ⟨t, ht, hunit, ?_, ?_⟩
  · intro x hx
    have heq : A x = fun w => t ^ degree • N (x, t, t • w) :=
      funext (hscale x hx t ht)
    rw [heq]
    exact suNormalizedCoefficient_gradient_bound N x v ht degree
      ((hN (x, t, t • v) ⟨hx, ht.le, hunit⟩).differentiableAt (by norm_num))
      (hbound x hx t (t • v) ht.le hunit)
  · intro x hx y hy
    rw [hscale x hx t ht v, hscale y hy t ht v]
    exact suNormalizedCoefficient_base_bound hconv N (t • v) ht degree
      (fun z hz => (hN (z, t, t • v) ⟨hz, ht.le, hunit⟩).differentiableAt (by norm_num))
      (fun z hz => hbound z hz t (t • v) ht.le hunit) hx hy



theorem suAlphaFlux_coefficient_bounds
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set P} (hK : IsCompact K) (hconv : Convex ℝ K)
    (B : P → E →L[ℝ] E →L[ℝ] ℝ) (c a : P → ℝ) (alpha : ℝ)
    {kappa : ℝ} (hk : 0 < kappa)
    (hB : ∀ x ∈ K, ContDiffAt ℝ 1 B x)
    (hc : ∀ x ∈ K, ContDiffAt ℝ 1 c x)
    (ha : ∀ x ∈ K, ContDiffAt ℝ 1 a x)
    (hpositive : ∀ x ∈ K, kappa ≤ c x ∧ ∀ v, kappa * ‖v‖ ^ 2 ≤ B x v v) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : E, ∃ t : ℝ, 0 < t ∧ t ^ 2 + ‖t • v‖ ^ 2 = 1 ∧
      (∀ x ∈ K, DifferentiableAt ℝ (fun w => a x • suAlphaFlux (B x) (c x) alpha w) v ∧
        ‖fderiv ℝ (fun w => a x • suAlphaFlux (B x) (c x) alpha w) v‖ ≤
          C * t ^ (1 - 2 * alpha + 1)) ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖a y • suAlphaFlux (B y) (c y) alpha v -
          a x • suAlphaFlux (B x) (c x) alpha v‖ ≤
            C * t ^ (1 - 2 * alpha) * ‖y - x‖ := by
  let N (z : P × (ℝ × E)) :=
    a z.1 • suAlphaFlux (B z.1) (z.2.1 ^ 2 * c z.1) alpha z.2.2
  apply suHomogeneousCoefficient_bounds hK hconv _ N (1 - 2 * alpha)
  · rintro ⟨x, t, v⟩ ⟨hx, _, hunit⟩
    have hcx := (hpositive x hx).1
    have hpos : 0 < t ^ 2 * c x + B x v v :=
      (lt_min (hk.trans_le hcx) hk).trans_le
        (suGradientParameters_coercive (B x) ((hpositive x hx).2 v) hunit)
    exact ((ha x hx).comp _ contDiffAt_fst).smul
      (suAlphaFlux_normalized_contDiffAt B c alpha (hB x hx) (hc x hx) hpos)
  · intro x hx t ht v
    have hnonneg (w : E) : 0 ≤ B x w w :=
      (mul_nonneg hk.le (sq_nonneg _)).trans ((hpositive x hx).2 w)
    rw [suAlphaFlux_gradient_scaling (B x) hnonneg
      (hk.trans_le (hpositive x hx).1) ht alpha v]
    simp only [N, smul_smul, mul_comm]



def suAlphaSource {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] E →L[ℝ] F) (c alpha : ℝ) (v : E) : F :=
  (-alpha * (c + B v v) ^ (alpha - 1)) • D v v

theorem suAlphaSource_gradient_scaling
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] E →L[ℝ] F)
    (hB : ∀ v, 0 ≤ B v v) {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (alpha : ℝ) (v : E) :
    suAlphaSource B D c alpha v =
      t ^ (-2 * alpha) • suAlphaSource B D (t ^ 2 * c) alpha (t • v) := by
  have hbase : 0 ≤ c + B v v := add_nonneg hc.le (hB v)
  have hquad : t ^ 2 * c + B (t • v) (t • v) = t ^ 2 * (c + B v v) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hpow : (t ^ 2) ^ (alpha - 1) = t ^ (2 * (alpha - 1)) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    norm_num
  have hweight : (t ^ 2 * c + B (t • v) (t • v)) ^ (alpha - 1) =
      t ^ (2 * (alpha - 1)) * (c + B v v) ^ (alpha - 1) := by
    rw [hquad, Real.mul_rpow (sq_nonneg _) hbase, hpow]
  have htone : t ^ (-2 * alpha) * t ^ (2 * (alpha - 1)) * t ^ 2 = 1 := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht, ← Real.rpow_add ht]
    convert Real.rpow_zero t using 1
    congr 1
    ring
  unfold suAlphaSource
  rw [hweight]
  simp only [map_smul, smul_apply, smul_smul]
  congr 1
  calc
    _ = (t ^ (-2 * alpha) * t ^ (2 * (alpha - 1)) * t ^ 2) *
        (-alpha * (c + B v v) ^ (alpha - 1)) := by rw [htone, one_mul]
    _ = _ := by ring

theorem suAlphaSource_normalized_contDiffAt
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : P → E →L[ℝ] E →L[ℝ] ℝ) (D : P → E →L[ℝ] E →L[ℝ] F)
    (c : P → ℝ) (alpha : ℝ) {x : P} {t : ℝ} {v : E}
    (hB : ContDiffAt ℝ 1 B x) (hD : ContDiffAt ℝ 1 D x)
    (hc : ContDiffAt ℝ 1 c x) (hpos : 0 < t ^ 2 * c x + B x v v) :
    ContDiffAt ℝ 1 (fun z : P × (ℝ × E) =>
      suAlphaSource (B z.1) (D z.1) (z.2.1 ^ 2 * c z.1) alpha z.2.2) (x, t, v) := by
  have hmetric : ContDiffAt ℝ 1 (fun z : P × (ℝ × E) => B z.1) (x, t, v) :=
    hB.comp _ contDiffAt_fst
  have hsource : ContDiffAt ℝ 1 (fun z : P × (ℝ × E) => D z.1) (x, t, v) :=
    hD.comp _ contDiffAt_fst
  have hconstant : ContDiffAt ℝ 1 (fun z : P × (ℝ × E) => c z.1) (x, t, v) :=
    hc.comp _ contDiffAt_fst
  have hbase : ContDiffAt ℝ 1
      (fun z : P × (ℝ × E) => z.2.1 ^ 2 * c z.1 + B z.1 z.2.2 z.2.2)
      (x, t, v) := by fun_prop
  have hweight := hbase.rpow_const_of_ne (p := alpha - 1) hpos.ne'
  exact (contDiffAt_const.mul hweight).smul
    ((hsource.clm_apply (by fun_prop)).clm_apply (by fun_prop))



theorem suAlphaSource_coefficient_bounds
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set P} (hK : IsCompact K) (hconv : Convex ℝ K)
    (B : P → E →L[ℝ] E →L[ℝ] ℝ) (D : P → E →L[ℝ] E →L[ℝ] F)
    (c a : P → ℝ) (alpha : ℝ) {kappa : ℝ} (hk : 0 < kappa)
    (hB : ∀ x ∈ K, ContDiffAt ℝ 1 B x)
    (hD : ∀ x ∈ K, ContDiffAt ℝ 1 D x)
    (hc : ∀ x ∈ K, ContDiffAt ℝ 1 c x)
    (ha : ∀ x ∈ K, ContDiffAt ℝ 1 a x)
    (hpositive : ∀ x ∈ K, kappa ≤ c x ∧ ∀ v, kappa * ‖v‖ ^ 2 ≤ B x v v) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : E, ∃ t : ℝ, 0 < t ∧ t ^ 2 + ‖t • v‖ ^ 2 = 1 ∧
      (∀ x ∈ K,
        DifferentiableAt ℝ (fun w => a x • suAlphaSource (B x) (D x) (c x) alpha w) v ∧
        ‖fderiv ℝ (fun w => a x • suAlphaSource (B x) (D x) (c x) alpha w) v‖ ≤
          C * t ^ (-2 * alpha + 1)) ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖a y • suAlphaSource (B y) (D y) (c y) alpha v -
          a x • suAlphaSource (B x) (D x) (c x) alpha v‖ ≤
            C * t ^ (-2 * alpha) * ‖y - x‖ := by
  let N (z : P × (ℝ × E)) :=
    a z.1 • suAlphaSource (B z.1) (D z.1) (z.2.1 ^ 2 * c z.1) alpha z.2.2
  apply suHomogeneousCoefficient_bounds hK hconv _ N (-2 * alpha)
  · rintro ⟨x, t, v⟩ ⟨hx, _, hunit⟩
    have hpos : 0 < t ^ 2 * c x + B x v v :=
      (lt_min (hk.trans_le (hpositive x hx).1) hk).trans_le
        (suGradientParameters_coercive (B x) ((hpositive x hx).2 v) hunit)
    exact ((ha x hx).comp _ contDiffAt_fst).smul
      (suAlphaSource_normalized_contDiffAt B D c alpha
        (hB x hx) (hD x hx) (hc x hx) hpos)
  · intro x hx t ht v
    have hnonneg (w : E) : 0 ≤ B x w w :=
      (mul_nonneg hk.le (sq_nonneg _)).trans ((hpositive x hx).2 w)
    rw [suAlphaSource_gradient_scaling (B x) (D x) hnonneg
      (hk.trans_le (hpositive x hx).1) ht alpha v]
    simp only [N, smul_smul, mul_comm]



theorem suGradientParameters_rpow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E} {t : ℝ} (ht : 0 < t) (hunit : t ^ 2 + ‖t • v‖ ^ 2 = 1) (degree : ℝ) :
    t ^ degree = (1 + ‖v‖ ^ 2) ^ (-degree / 2) := by
  have hbase : 0 < 1 + ‖v‖ ^ 2 := by positivity
  have heq : t ^ 2 * (1 + ‖v‖ ^ 2) = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow] at hunit
    nlinarith [hunit]
  have ht2 : t ^ 2 = (1 + ‖v‖ ^ 2)⁻¹ := by
    apply (mul_left_injective₀ hbase.ne')
    simpa only [mul_inv_cancel₀ hbase.ne', mul_comm] using heq
  calc
    _ = (t ^ 2) ^ (degree / 2) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
      congr 1
      ring
    _ = _ := by
      rw [ht2, Real.inv_rpow hbase.le, ← Real.rpow_neg hbase.le]
      congr 1
      ring



theorem suNaturalWeight_segment_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q r z : E} (hz : z ∈ segment ℝ q r) {p : ℝ} (hp : 0 ≤ p) :
    (1 + ‖z‖ ^ 2) ^ p ≤ (1 + ‖q‖ ^ 2) ^ p + (1 + ‖r‖ ^ 2) ^ p := by
  have hn : ‖z‖ ≤ max ‖q‖ ‖r‖ := mem_closedBall_zero_iff.mp
    ((convex_closedBall (0 : E) (max ‖q‖ ‖r‖)).segment_subset
      (mem_closedBall_zero_iff.mpr (le_max_left _ _))
      (mem_closedBall_zero_iff.mpr (le_max_right _ _)) hz)
  rcases le_total ‖q‖ ‖r‖ with hqr | hrq
  · rw [max_eq_right hqr] at hn
    exact (Real.rpow_le_rpow (by positivity)
      (by nlinarith [norm_nonneg z]) hp).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _))
  · rw [max_eq_left hrq] at hn
    exact (Real.rpow_le_rpow (by positivity)
      (by nlinarith [norm_nonneg z]) hp).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))



theorem suNaturalCoefficient_difference
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → F) (hA : Differentiable ℝ A) {C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hbound : ∀ z, ‖fderiv ℝ A z‖ ≤ C * (1 + ‖z‖ ^ 2) ^ p) (q r : E) :
    ‖A q - A r‖ ≤ C * ((1 + ‖q‖ ^ 2) ^ p + (1 + ‖r‖ ^ 2) ^ p) * ‖q - r‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hA z) _ (convex_segment r q)
    (left_mem_segment ℝ r q) (right_mem_segment ℝ r q)
  intro z hz
  apply (hbound z).trans
  apply mul_le_mul_of_nonneg_left _ hC
  simpa only [add_comm] using suNaturalWeight_segment_bound hz hp



theorem suAlphaFlux_canonical_monotone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {c alpha kappa : ℝ}
    (hk : 0 < kappa) (hc : kappa ≤ c) (ha : 1 ≤ alpha)
    (hB : ∀ v, kappa * ‖v‖ ^ 2 ≤ B v v)
    (hsymm : ∀ v w, B v w = B w v) (q r : E) :
    (alpha * kappa * kappa ^ (alpha - 1)) *
      ((1 + ‖q‖ ^ 2) ^ (alpha - 1) + (1 + ‖r‖ ^ 2) ^ (alpha - 1)) *
      ‖q - r‖ ^ 2 ≤ (suAlphaFlux B c alpha q - suAlphaFlux B c alpha r) (q - r) := by
  have hnonneg (v : E) : 0 ≤ B v v :=
    (mul_nonneg hk.le (sq_nonneg _)).trans (hB v)
  have hweight (v : E) : kappa ^ (alpha - 1) * (1 + ‖v‖ ^ 2) ^ (alpha - 1) ≤
      (c + B v v) ^ (alpha - 1) := by
    rw [← Real.mul_rpow hk.le (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [hB v]) (by linarith)
  have hw := add_le_add (hweight q) (hweight r)
  calc
    _ = (alpha * (kappa ^ (alpha - 1) * (1 + ‖q‖ ^ 2) ^ (alpha - 1) +
        kappa ^ (alpha - 1) * (1 + ‖r‖ ^ 2) ^ (alpha - 1))) *
        (kappa * ‖q - r‖ ^ 2) := by ring
    _ ≤ (alpha * ((c + B q q) ^ (alpha - 1) + (c + B r r) ^ (alpha - 1))) *
        B (q - r) (q - r) := mul_le_mul
          (mul_le_mul_of_nonneg_left hw (by linarith)) (hB _) (by positivity)
          (mul_nonneg (by linarith) (add_nonneg
            (Real.rpow_nonneg (add_nonneg (hk.le.trans hc) (hnonneg q)) _)
            (Real.rpow_nonneg (add_nonneg (hk.le.trans hc) (hnonneg r)) _)))
    _ ≤ _ := suAlphaFlux_weighted_monotone B hnonneg hsymm (hk.le.trans hc) ha q r




theorem suNaturalWeights_pair_square
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (alpha : ℝ) (q r : E) :
    let W := (1 + ‖q‖ ^ 2) ^ (alpha - 1) + (1 + ‖r‖ ^ 2) ^ (alpha - 1)
    let H := (1 + ‖q‖ ^ 2) ^ alpha + (1 + ‖r‖ ^ 2) ^ alpha
    ((1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) + (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2)) ^ 2 ≤
        2 * W * H ∧
      ((1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2)) ^ 2 ≤ W * H := by
  have hpower (t : ℝ) (ht : 0 < t) :
      (t ^ (alpha - 1 / 2)) ^ 2 = t ^ (alpha - 1) * t ^ alpha := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    congr 1
    ring
  have hq := hpower (1 + ‖q‖ ^ 2) (by positivity)
  have hr := hpower (1 + ‖r‖ ^ 2) (by positivity)
  have hqw : 0 ≤ (1 + ‖q‖ ^ 2) ^ (alpha - 1) := Real.rpow_nonneg (by positivity) _
  have hrw : 0 ≤ (1 + ‖r‖ ^ 2) ^ (alpha - 1) := Real.rpow_nonneg (by positivity) _
  have hqh : 0 ≤ (1 + ‖q‖ ^ 2) ^ alpha := Real.rpow_nonneg (by positivity) _
  have hrh : 0 ≤ (1 + ‖r‖ ^ 2) ^ alpha := Real.rpow_nonneg (by positivity) _
  dsimp only
  constructor
  · nlinarith [sq_nonneg ((1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) -
      (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2)), mul_nonneg hqw hrh, mul_nonneg hrw hqh]
  · rw [hr]
    exact mul_le_mul (le_add_of_nonneg_left hqw) (le_add_of_nonneg_left hqh) hrh
      (add_nonneg hqw hrw)

end PoincareConjecture.M60
