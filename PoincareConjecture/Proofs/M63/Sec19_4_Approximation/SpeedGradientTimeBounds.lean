import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.NonconstantSpeedGradient
import Mathlib.Analysis.Calculus.MeanValue











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem curveSpeed_spatial_derivative_time_lipschitz [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R J m V G J1 : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J) (hm : 0 < m)
    (hV : 0 ≤ V) (hG : 0 ≤ G) (hJ1 : 0 ≤ J1)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hCurv : ∀ r ∈ Ioo a b, ∀ x, m62CurvatureSquared F c r x ≤ R)
    (hJet : ∀ r ∈ Ioo a b, ∀ x,
      (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) ≤
        J / Real.sqrt (r - a))
    (hSpeed : ∀ r ∈ Icc a b, ∀ x,
      m ≤ curveSpeed F c r x ∧ curveSpeed F c r x ≤ V)
    (hGradient : ∀ r ∈ Icc a b, ∀ x, |deriv (curveSpeed F c r) x| ≤ G)
    {sigma tau : ℝ} (has : a ≤ sigma) (hst : sigma ≤ tau) (htb : tau ≤ b)
    (hFirst : ∀ r ∈ Ioo sigma tau, ∀ x,
      (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) ≤ J1) :
    let C := (K + R) * V * (G / m) +
      V ^ 2 * (K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * J1)
    ∀ s ∈ Icc sigma tau, ∀ t ∈ Icc sigma tau, ∀ x : ℝ,
      |deriv (curveSpeed F c s) x - deriv (curveSpeed F c t) x| ≤ C * |s - t| := by
  dsimp only
  intro s hs t ht x
  let v : ℝ → ℝ := fun r => curveSpeed F c r x
  let g : ℝ → ℝ := fun r => deriv (curveSpeed F c r) x
  let u : ℝ → ℝ := fun r => g r / v r
  let Ax : ℝ → ℝ := fun r => deriv (fun y =>
    m62TangentRicci F c r y + m62CurvatureSquared F c r y) x
  let Q := K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * J1
  let Cu := V * Q
  let Cv := (K + R) * V
  have hCv : 0 ≤ Cv := mul_nonneg (add_nonneg hK hR) hV
  have hclosed (r : ℝ) (hr : r ∈ Icc sigma tau) : r ∈ Icc a b :=
    ⟨has.trans hr.1, hr.2.trans htb⟩
  have hinter (r : ℝ) (hr : r ∈ Ioo sigma tau) : r ∈ Ioo a b :=
    ⟨has.trans_lt hr.1, hr.2.trans_le htb⟩
  have hvpos (r : ℝ) (hr : r ∈ Icc sigma tau) : 0 < v r :=
    speed_pos F c hc (hclosed r hr) x
  have hprimitive (r : ℝ) (hr : r ∈ Icc sigma tau) :
      IntervalIntegrable Ax volume a r ∧
        u r = u a - ∫ z in a..r, Ax z := by
    have h := curveSpeed_spatial_ratio_integral_of_speed_le F c hc hK hR hJ hV hBounds
      (fun z hz y => (hSpeed z (Ioo_subset_Icc_self hz) y).2) hCurv hJet
      (hclosed r hr) x
    exact ⟨h.1, h.2.1⟩
  have hAx (r : ℝ) (hr : r ∈ Ioo sigma tau) : |Ax r| ≤ Cu := by
    have hr' := hinter r hr
    have hk0 := curvature_nonneg F c r x
    have hk : m62Curvature F c r x ≤ Real.sqrt R := by
      nlinarith only [curvature_sq F c r x, hCurv r hr' x,
        Real.sq_sqrt hR, Real.sqrt_nonneg R]
    have hj0 : 0 ≤ (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) :=
      Real.sqrt_nonneg _
    have hco : K + 2 * K * m62Curvature F c r x +
        2 * m62Curvature F c r x *
          (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) ≤ Q := by
      apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hk (by positivity))
      · exact (mul_le_mul_of_nonneg_left (hFirst r hr x) (by positivity)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) hJ1)
    have hco0 : 0 ≤ K + 2 * K * m62Curvature F c r x +
        2 * m62Curvature F c r x *
          (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) := by positivity
    exact (normalizationCoefficient_spatial_abs_bound F c hc hBounds hr' x).trans
      (mul_le_mul (hSpeed r (Ioo_subset_Icc_self hr') x).2 hco hco0 hV)
  have huLip : |u s - u t| ≤ Cu * |s - t| := by
    have hi := intervalIntegral.integral_interval_sub_left
      (hprimitive t ht).1 (hprimitive s hs).1
    have heq : u s - u t = ∫ r in s..t, Ax r := by
      rw [(hprimitive s hs).2, (hprimitive t ht).2]
      linarith only [hi]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := s) (b := t) (f := Ax) (C := Cu) (by
        filter_upwards [volume.ae_ne (max s t)] with r hrmax
        intro hr
        have hr' : r ∈ Ioo sigma tau :=
          ⟨(le_min hs.1 ht.1).trans_lt hr.1,
            (lt_of_le_of_ne hr.2 hrmax).trans_le (max_le hs.2 ht.2)⟩
        simpa only [Real.norm_eq_abs] using hAx r hr')
    rw [heq]
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hb
  have hvLip : |v s - v t| ≤ Cv * |s - t| := by
    by_cases hlt : sigma < tau
    · have hd (r : ℝ) (hr : r ∈ Ioo sigma tau) :
          DifferentiableAt ℝ v r ∧ ‖deriv v r‖ ≤ Cv := by
        have hr' := hinter r hr
        have hrc := Ioo_subset_Icc_self hr'
        have hder := hasDerivAt_speed F c hc hr' x
        have hunit := (unitTangent_norm F c hc hrc x).le
        have hric : |m62TangentRicci F c r x| ≤ K :=
          hBounds.ricci r hrc (c x r) (spatialUnitTangent F c r x)
            (spatialUnitTangent F c r x) hunit hunit
        have hco : |m62TangentRicci F c r x + m62CurvatureSquared F c r x| ≤ K + R := by
          calc
            _ ≤ |m62TangentRicci F c r x| + |m62CurvatureSquared F c r x| :=
              abs_add_le _ _
            _ ≤ K + R := add_le_add hric (by
              rw [abs_of_nonneg (curvatureSquared_nonneg F c r x)]
              exact hCurv r hr' x)
        refine ⟨hder.differentiableAt, ?_⟩
        rw [hder.deriv, Real.norm_eq_abs, abs_mul, abs_neg,
          abs_of_nonneg (speed_nonneg F c r x)]
        exact mul_le_mul hco (hSpeed r hrc x).2 (speed_nonneg F c r x) (add_nonneg hK hR)
      have hcV : ContinuousOn v (Icc sigma tau) :=
        (speed_continuousOn F c hc).comp
          (continuous_const.prodMk continuous_id).continuousOn
          (fun r hr => ⟨mem_univ _, hclosed r hr⟩)
      have hopen : LipschitzOnWith ⟨Cv, hCv⟩ v (Ioo sigma tau) :=
        (convex_Ioo sigma tau).lipschitzOnWith_of_nnnorm_deriv_le
          (fun r hr => (hd r hr).1) (fun r hr => (hd r hr).2)
      have hcont : ContinuousOn v (closure (Ioo sigma tau)) := by
        simpa only [closure_Ioo hlt.ne] using hcV
      have hclosure : LipschitzOnWith ⟨Cv, hCv⟩ v (Icc sigma tau) := by
        simpa only [closure_Ioo hlt.ne] using LipschitzOnWith.closure hcont hopen
      simpa only [Real.dist_eq] using! hclosure.dist_le_mul s hs t ht
    · have heq : sigma = tau := le_antisymm hst (le_of_not_gt hlt)
      have hsame : s = t := by
        rw [heq] at hs ht
        exact (le_antisymm hs.2 hs.1).trans (le_antisymm ht.2 ht.1).symm
      subst t
      simp
  have huBound : |u s| ≤ G / m := by
    change |g s / v s| ≤ G / m
    rw [abs_div, abs_of_pos (hvpos s hs)]
    exact (div_le_div_of_nonneg_right (hGradient s (hclosed s hs) x) (hvpos s hs).le).trans
      (div_le_div_of_nonneg_left hG hm (hSpeed s (hclosed s hs) x).1)
  have hprod (r : ℝ) (hr : r ∈ Icc sigma tau) : v r * u r = g r := by
    dsimp only [u]
    field_simp [(hvpos r hr).ne']
  have heq : g s - g t = (v s - v t) * u s + v t * (u s - u t) := by
    rw [← hprod s hs, ← hprod t ht]
    ring
  calc
    _ = |(v s - v t) * u s + v t * (u s - u t)| := congrArg abs heq
    _ ≤ |(v s - v t) * u s| + |v t * (u s - u t)| := abs_add_le _ _
    _ = |v s - v t| * |u s| + v t * |u s - u t| := by
      rw [abs_mul, abs_mul, abs_of_pos (hvpos t ht)]
    _ ≤ Cv * |s - t| * (G / m) + V * (Cu * |s - t|) :=
      add_le_add (mul_le_mul hvLip huBound (abs_nonneg _) (mul_nonneg hCv (abs_nonneg _)))
        (mul_le_mul (hSpeed t (hclosed t ht) x).2 huLip (abs_nonneg _) hV)
    _ = ((K + R) * V * (G / m) +
        V ^ 2 * (K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * J1)) * |s - t| := by
      dsimp only [Cv, Cu, Q]
      ring

end PoincareConjecture.M63
