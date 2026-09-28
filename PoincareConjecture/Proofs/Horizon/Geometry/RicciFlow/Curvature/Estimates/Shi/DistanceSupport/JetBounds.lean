import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.JoinedVelocity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.IntegratedJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.RicciFlowAnalysis

private theorem shiJet_sq_sum_integral_le
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) (f : ι → ℝ → ℝ)
    (hab : ∀ i, a i ≤ b i) (hsize : ∑ i, (b i - a i) = 1)
    (hf : ∀ i, ContinuousOn (f i) (Icc (a i) (b i))) :
    (∑ i, ∫ t in a i..b i, f i t) ^ 2 ≤
      ∑ i, ∫ t in a i..b i, (f i t) ^ 2 := by
  classical
  let m : ℝ := ∑ i, ∫ t in a i..b i, f i t
  have hvariance (i : ι) :
      (∫ t in a i..b i, (f i t - m) ^ 2) =
        (∫ t in a i..b i, (f i t) ^ 2) -
          (2 * m) * (∫ t in a i..b i, f i t) + (b i - a i) * m ^ 2 := by
    have hiSq : IntervalIntegrable (fun t => (f i t) ^ 2) volume (a i) (b i) :=
      ContinuousOn.intervalIntegrable_of_Icc (hab i) ((hf i).pow 2)
    have hiMul : IntervalIntegrable (fun t => (2 * m) * f i t) volume (a i) (b i) :=
      ContinuousOn.intervalIntegrable_of_Icc (hab i) (continuousOn_const.mul (hf i))
    calc
      _ = ∫ t in a i..b i, (f i t) ^ 2 - (2 * m) * f i t + m ^ 2 :=
        intervalIntegral.integral_congr (fun t _ => by ring)
      _ = _ := by
        rw [intervalIntegral.integral_add (hiSq.sub hiMul)
          (continuous_const.intervalIntegrable _ _),
          intervalIntegral.integral_sub hiSq hiMul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
  have hnonneg : 0 ≤ ∑ i,
      ((∫ t in a i..b i, (f i t) ^ 2) -
        (2 * m) * (∫ t in a i..b i, f i t) + (b i - a i) * m ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    rw [← hvariance i]
    exact intervalIntegral.integral_nonneg (hab i) (fun t _ => sq_nonneg _)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hsize] at hnonneg
  change 0 ≤ (∑ i, ∫ t in a i..b i, (f i t) ^ 2) -
    (2 * m) * m + 1 * m ^ 2 at hnonneg
  change m ^ 2 ≤ _
  nlinarith only [hnonneg]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "V" => EuclideanSpace ℝ (Fin n)

noncomputable def shiActualJoinedDensity
    (D : LeviCivitaData g) (c : OpenPartialHomeomorph M V)
    (a b : ℝ) (x : ℝ → V) (P : ℝ → V →L[ℝ] V)
    (left right : V → V) (t : ℝ) (z : V) : ℝ :=
  let A : ℝ → V →L[ℝ] V := fun s => s • P s
  let B : ℝ → V →L[ℝ] V →L[ℝ] V := fun s =>
    -(shiChartChristoffel D c (x s)).bilinearComp (A s) (A s)
  let F := joinedCoordinateVariation a b x A B left right
  let W := derivWithin (fun s => F s z) (Icc a b) t
  shiChartMetric g c (F t z) W W

set_option backward.isDefEq.respectTransparency false in
private theorem shiJet_chartMetric_nonneg
    (g : RiemannianMetric n M) (c : OpenPartialHomeomorph M V) (x v : V) :
    0 ≤ shiChartMetric g c x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change 0 ≤ inner ℝ (mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm x v)
    (mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm x v)
  exact real_inner_self_nonneg

set_option backward.isDefEq.respectTransparency false in
private theorem shiJet_chartMetric_pairing_sq_le
    (g : RiemannianMetric n M) (c : OpenPartialHomeomorph M V) (x v w : V) :
    (shiChartMetric g c x v w) ^ 2 ≤
      shiChartMetric g c x v v * shiChartMetric g c x w w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let S : V →L[ℝ] TangentSpace (𝓡 n) (c.symm x) :=
    mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm x
  change (inner ℝ (S v) (S w)) ^ 2 ≤
    inner ℝ (S v) (S v) * inner ℝ (S w) (S w)
  simpa only [pow_two] using real_inner_mul_inner_self_le (S v) (S w)

set_option backward.isDefEq.respectTransparency false in
private theorem shiJet_abs_curvature_repeated_le
    (D : LeviCivitaData g) (p : M) (v w : TangentSpace (𝓡 n) p) :
    |D.curvatureTensor p v w v w| ≤
      D.curvatureTensorNorm p * g.inner p v v * g.inner p w w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hN : 0 ≤ D.curvatureTensorNorm p := Real.sqrt_nonneg _
  have hv : 0 ≤ g.inner p v v := real_inner_self_nonneg (x := v)
  have hw : 0 ≤ g.inner p w w := real_inner_self_nonneg (x := w)
  have hNorm : g.tensorNorm D.riemannEvaluation p = D.curvatureTensorNorm p :=
    D.horizon_curvatureDerivativeNorm_zero p
  have h := tensorEvaluation_sq_le_tensorNorm g
    (isSmoothCovariantTensor_riemannEvaluation D) p ![v, w, v, w]
  simp only [LeviCivitaData.riemannEvaluation, hNorm, Fin.prod_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  apply abs_le_of_sq_le_sq _ (mul_nonneg (mul_nonneg hN hv) hw)
  calc
    (D.curvatureTensor p v w v w) ^ 2 ≤
        (D.curvatureTensorNorm p) ^ 2 *
          (g.inner p v v * g.inner p w w * g.inner p v v * g.inner p w w) := h
    _ = (D.curvatureTensorNorm p * g.inner p v v * g.inner p w w) ^ 2 := by ring

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
theorem shiActualJoinedDensity_integrated_jet_bounds [T2Space M]
    {ι : Type*} [Fintype ι] (D : LeviCivitaData g)
    (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1)
    (hsize : ∑ i, (b i - a i) = 1)
    (c : ι → OpenPartialHomeomorph M V)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ (c i).symm (c i).target)
    (x : ι → ℝ → V) (P : ι → ℝ → V →L[ℝ] V)
    (hx : ∀ i, ContDiffOn ℝ 1 (x i) (Icc (a i) (b i)))
    (hxt : ∀ i, MapsTo (x i) (Icc (a i) (b i)) (c i).target)
    (hP : ∀ i, ContDiffOn ℝ 1 (P i) (Icc (a i) (b i)))
    (hPd : ∀ i t, t ∈ Icc (a i) (b i) →
      HasDerivWithinAt (P i)
        (-((shiChartChristoffel D (c i) (x i t)
          (derivWithin (x i) (Icc (a i) (b i)) t)).comp (P i t)))
        (Icc (a i) (b i)) t)
    (hiso : ∀ i t, t ∈ Icc (a i) (b i) → ∀ v w,
      shiChartMetric g (c i) (x i t) (P i t v) (P i t w) = inner ℝ v w)
    (left right : ι → V → V)
    (hl : ∀ i, ContDiffAt ℝ 2 (left i) 0)
    (hr : ∀ i, ContDiffAt ℝ 2 (right i) 0)
    (hl0 : ∀ i, left i 0 = x i (a i))
    (hr0 : ∀ i, right i 0 = x i (b i))
    (hl1 : ∀ i, fderiv ℝ (left i) 0 = a i • P i (a i))
    (hr1 : ∀ i, fderiv ℝ (right i) 0 = b i • P i (b i))
    (hl2 : ∀ i v, (fderiv ℝ (fderiv ℝ (left i)) 0 v) v =
      -shiChartChristoffel D (c i) (x i (a i))
        (a i • P i (a i) v) (a i • P i (a i) v))
    (hr2 : ∀ i v, (fderiv ℝ (fderiv ℝ (right i)) 0 v) v =
      -shiChartChristoffel D (c i) (x i (b i))
        (b i • P i (b i) v) (b i • P i (b i) v))
    (K : ℝ) (hK : 0 ≤ K)
    (hRm : ∀ i t, t ∈ Icc (a i) (b i) →
      D.curvatureTensorNorm ((c i).symm (x i t)) ≤ K) :
    let e : ι → ℝ → V → ℝ := fun i =>
      shiActualJoinedDensity D (c i) (a i) (b i) (x i) (P i) (left i) (right i)
    (∀ i, ContinuousOn (fun t => fderiv ℝ (e i t) 0) (Icc (a i) (b i))) →
    (∀ i, ContinuousOn (fun t => fderiv ℝ (fderiv ℝ (e i t)) 0)
      (Icc (a i) (b i))) →
    0 ≤ shiIntegratedEnergy a b e 0 ∧
      ‖shiIntegratedLinearJet a b e‖ ≤
        2 * Real.sqrt (shiIntegratedEnergy a b e 0) ∧
      (∑ j : Fin n, shiIntegratedQuadraticJet a b e
        (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) ≤
        2 * (n : ℝ) + 2 * (n : ℝ) * K * shiIntegratedEnergy a b e 0 := by
  classical
  dsimp only
  let e : ι → ℝ → V → ℝ := fun i =>
    shiActualJoinedDensity D (c i) (a i) (b i) (x i) (P i) (left i) (right i)
  change (∀ i, ContinuousOn (fun t => fderiv ℝ (e i t) 0) (Icc (a i) (b i))) →
    (∀ i, ContinuousOn (fun t => fderiv ℝ (fderiv ℝ (e i t)) 0)
      (Icc (a i) (b i))) → _
  intro hL hQ
  let T : ι → ℝ → V := fun i => derivWithin (x i) (Icc (a i) (b i))
  let G : ι → ℝ → V →L[ℝ] V →L[ℝ] ℝ :=
    fun i t => shiChartMetric g (c i) (x i t)
  let U : ι → ℝ → ℝ := fun i t => G i t (T i t) (T i t)
  let E0 : ℝ := shiIntegratedEnergy a b e 0
  let S (i : ι) (t : ℝ) : V →L[ℝ] TangentSpace (𝓡 n) ((c i).symm (x i t)) :=
    mfderiv 𝓘(ℝ, V) (𝓡 n) (c i).symm (x i t)
  have hjet (i : ι) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
      e i t 0 = U i t ∧
        (∀ v, fderiv ℝ (e i t) 0 v = 2 * G i t (P i t v) (T i t)) ∧
        ∀ v, (fderiv ℝ (fderiv ℝ (e i t)) 0 v) v =
          2 * (G i t (P i t v) (P i t v) -
            D.curvatureTensor ((c i).symm (x i t)) (S i t (T i t))
              (S i t (t • P i t v)) (S i t (T i t)) (S i t (t • P i t v))) := by
    have hxd : HasDerivWithinAt (x i) (T i t) (Icc (a i) (b i)) t :=
      ((hx i).differentiableOn (by norm_num) t ht).hasDerivWithinAt
    have hj := shiChart_joined_density_second_jet D (hc i) (hi i) (hab i) ht
      (x i) (P i) (hxt i ⟨le_rfl, (hab i).le⟩)
      (hxt i ⟨(hab i).le, le_rfl⟩) (hxt i ht) hxd (hPd i t ht)
      (hl i) (hr i) (hl0 i) (hr0 i) (hl1 i) (hr1 i) (hl2 i) (hr2 i)
    exact ⟨hj.2.1, hj.2.2.1, hj.2.2.2⟩
  have hT (i : ι) : ContinuousOn (T i) (Icc (a i) (b i)) :=
    (hx i).continuousOn_derivWithin (uniqueDiffOn_Icc (hab i)) le_rfl
  have hG (i : ι) : ContinuousOn (G i) (Icc (a i) (b i)) :=
    (shiChartMetric_smooth g (hc i) (hi i)).continuousOn.comp
      (hx i).continuousOn (hxt i)
  have hU (i : ι) : ContinuousOn (U i) (Icc (a i) (b i)) :=
    ((hG i).clm_apply (hT i)).clm_apply (hT i)
  have hU0 (i : ι) (t : ℝ) : 0 ≤ U i t :=
    shiJet_chartMetric_nonneg g (c i) (x i t) (T i t)
  have hE0 : E0 = ∑ i, ∫ t in a i..b i, U i t := by
    apply Finset.sum_congr rfl
    intro i _
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hjet i t (by simpa only [uIcc_of_le (hab i).le] using ht)).1
  have hE0nonneg : 0 ≤ E0 := by
    rw [hE0]
    exact Finset.sum_nonneg fun i _ =>
      intervalIntegral.integral_nonneg (hab i).le (fun t _ => hU0 i t)
  refine ⟨hE0nonneg, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    let f : ι → ℝ → ℝ := fun i t => G i t (P i t v) (T i t)
    have hf (i : ι) : ContinuousOn (f i) (Icc (a i) (b i)) :=
      ((hG i).clm_apply ((hP i).continuousOn.clm_apply continuousOn_const)).clm_apply
        (hT i)
    have hfSq (i : ι) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
        (f i t) ^ 2 ≤ ‖v‖ ^ 2 * U i t := by
      have hh := shiJet_chartMetric_pairing_sq_le g (c i) (x i t) (P i t v) (T i t)
      rw [hiso i t ht v v, real_inner_self_eq_norm_sq] at hh
      exact hh
    let m : ℝ := ∑ i, ∫ t in a i..b i, f i t
    have hmSq : m ^ 2 ≤ ‖v‖ ^ 2 * E0 := by
      calc
        m ^ 2 ≤ ∑ i, ∫ t in a i..b i, (f i t) ^ 2 :=
          shiJet_sq_sum_integral_le a b f (fun i => (hab i).le) hsize hf
        _ ≤ ∑ i, ∫ t in a i..b i, ‖v‖ ^ 2 * U i t := by
          apply Finset.sum_le_sum
          intro i _
          exact intervalIntegral.integral_mono_on (hab i).le
            (ContinuousOn.intervalIntegrable_of_Icc (hab i).le ((hf i).pow 2))
            (ContinuousOn.intervalIntegrable_of_Icc (hab i).le
              (continuousOn_const.mul (hU i))) (hfSq i)
        _ = ‖v‖ ^ 2 * E0 := by
          simp only [intervalIntegral.integral_const_mul]
          rw [← Finset.mul_sum, ← hE0]
    have hLin : shiIntegratedLinearJet a b e v = 2 * m := by
      rw [shiIntegratedLinearJet_apply a b e (fun i => (hab i).le) hL]
      calc
        _ = ∑ i, ∫ t in a i..b i, 2 * f i t := by
          apply Finset.sum_congr rfl
          intro i _
          apply intervalIntegral.integral_congr
          intro t ht
          exact (hjet i t (by simpa only [uIcc_of_le (hab i).le] using ht)).2.1 v
        _ = 2 * m := by simp only [intervalIntegral.integral_const_mul, ← Finset.mul_sum, m]
    rw [Real.norm_eq_abs, hLin]
    apply abs_le_of_sq_le_sq _ (by positivity)
    calc
      (2 * m) ^ 2 ≤ 4 * (‖v‖ ^ 2 * E0) := by nlinarith only [hmSq]
      _ = (2 * Real.sqrt E0 * ‖v‖) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hE0nonneg]
        ring
  · let basis := EuclideanSpace.basisFun (Fin n) ℝ
    have hdiag (i : ι) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) (j : Fin n) :
        (fderiv ℝ (fderiv ℝ (e i t)) 0 (basis j)) (basis j) ≤
          2 + 2 * K * U i t := by
      have hunit : G i t (P i t (basis j)) (P i t (basis j)) = 1 := by
        rw [hiso i t ht, real_inner_self_eq_norm_sq, basis.orthonormal.norm_eq_one,
          one_pow]
      have ht0 : 0 ≤ t := (ha i).trans ht.1
      have ht1 : t ≤ 1 := ht.2.trans (hb i)
      have htsq : t ^ 2 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ ht0 ht1 2
      have hcurv : |D.curvatureTensor ((c i).symm (x i t)) (S i t (T i t))
          (S i t (t • P i t (basis j))) (S i t (T i t))
          (S i t (t • P i t (basis j)))| ≤ K * U i t := by
        have heval := shiJet_abs_curvature_repeated_le D ((c i).symm (x i t))
          (S i t (T i t)) (S i t (t • P i t (basis j)))
        have hscaled : g.inner ((c i).symm (x i t))
            (S i t (t • P i t (basis j))) (S i t (t • P i t (basis j))) = t ^ 2 := by
          change G i t (t • P i t (basis j)) (t • P i t (basis j)) = t ^ 2
          simp only [map_smul, smul_apply, smul_eq_mul, hunit, mul_one, pow_two]
        change |D.curvatureTensor ((c i).symm (x i t)) (S i t (T i t))
          (S i t (t • P i t (basis j))) (S i t (T i t))
          (S i t (t • P i t (basis j)))| ≤
            D.curvatureTensorNorm ((c i).symm (x i t)) * U i t *
              g.inner ((c i).symm (x i t))
                (S i t (t • P i t (basis j))) (S i t (t • P i t (basis j))) at heval
        rw [hscaled] at heval
        calc
          _ ≤ D.curvatureTensorNorm ((c i).symm (x i t)) * U i t * t ^ 2 := heval
          _ ≤ K * U i t * t ^ 2 := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hRm i t ht) (hU0 i t)) (sq_nonneg t)
          _ ≤ K * U i t := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left htsq (mul_nonneg hK (hU0 i t))
      rw [(hjet i t ht).2.2 (basis j), hunit]
      have hlow := (abs_le.mp hcurv).1
      linarith only [hlow]
    rw [shiIntegratedQuadraticJet_trace a b e (fun i => (hab i).le) hQ]
    calc
      _ ≤ ∑ i, ∫ t in a i..b i, 2 * (n : ℝ) + 2 * (n : ℝ) * K * U i t := by
        apply Finset.sum_le_sum
        intro i _
        have htrace : ContinuousOn
            (fun t => ∑ j : Fin n, (fderiv ℝ (fderiv ℝ (e i t)) 0 (basis j)) (basis j))
            (Icc (a i) (b i)) :=
          continuousOn_finsetSum _ (fun j _ =>
            ((hQ i).clm_apply continuousOn_const).clm_apply continuousOn_const)
        exact intervalIntegral.integral_mono_on (hab i).le
          (ContinuousOn.intervalIntegrable_of_Icc (hab i).le htrace)
          (ContinuousOn.intervalIntegrable_of_Icc (hab i).le
            (continuousOn_const.add (continuousOn_const.mul (hU i))))
          (fun t ht => calc
            _ ≤ ∑ _j : Fin n, (2 + 2 * K * U i t) :=
              Finset.sum_le_sum fun j _ => hdiag i t ht j
            _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]; ring)
      _ = 2 * (n : ℝ) + 2 * (n : ℝ) * K * E0 := by
        have hsplit' (i : ι) :
            (fun t : ℝ => 2 * (n : ℝ) + 2 * (n : ℝ) * K * U i t) =
              (fun _ : ℝ => 2 * (n : ℝ)) +
                (fun t : ℝ => (2 * (n : ℝ) * K) * U i t) := by
          funext t
          simp only [Pi.add_apply]
        have hint (i : ι) :
            (∫ t in a i..b i, 2 * (n : ℝ) + 2 * (n : ℝ) * K * U i t) =
              (b i - a i) * (2 * (n : ℝ)) +
                (2 * (n : ℝ) * K) * (∫ t in a i..b i, U i t) := by
          have hconst :
              IntervalIntegrable (fun _ : ℝ => 2 * (n : ℝ)) volume (a i) (b i) :=
            continuous_const.intervalIntegrable _ _
          have hU' :
              IntervalIntegrable
                (fun t : ℝ => (2 * (n : ℝ) * K) * U i t) volume (a i) (b i) :=
            ContinuousOn.intervalIntegrable_of_Icc (hab i).le
              (continuousOn_const.mul (hU i))
          calc
            (∫ t in a i..b i, 2 * (n : ℝ) + 2 * (n : ℝ) * K * U i t) =
                ∫ t in a i..b i,
                  (fun _ : ℝ => 2 * (n : ℝ)) t +
                    (fun t : ℝ => (2 * (n : ℝ) * K) * U i t) t := by
              apply intervalIntegral.integral_congr
              intro t ht
              ring
            _ = (∫ t in a i..b i, (fun _ : ℝ => 2 * (n : ℝ)) t) +
                  ∫ t in a i..b i, (fun t : ℝ => (2 * (n : ℝ) * K) * U i t) t :=
              intervalIntegral.integral_add hconst hU'
            _ = (b i - a i) * (2 * (n : ℝ)) +
                  (2 * (n : ℝ) * K) * (∫ t in a i..b i, U i t) := by
              rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
              simp only [smul_eq_mul]
        simp_rw [hint]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsize, ← hE0,
          one_mul]

end PoincareConjecture.RicciFlowAnalysis
