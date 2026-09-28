import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurveLength
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem toReal_edist_le_exp_of_linear_speed_unit
    (g : RiemannianMetric n M) (p : M) {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hsub : Icc (0 : ℝ) 1 ⊆ I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    {A : ℝ} (hA : 0 ≤ A)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) ≤
        A * (1 + (g.edist p (γ t)).toReal)) :
    (g.edist p (γ 1)).toReal ≤ (1 + (g.edist p (γ 0)).toReal) * Real.exp A := by
  let v := fun t => g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
  let q := fun t => 1 + (g.edist p (γ 0)).toReal + ∫ r in (0 : ℝ)..t, v r
  have hv : ContinuousOn v I := g.continuousOn_speed_of_contMDiffOn hI hγ
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt q (v t) t := by
    have hint : IntervalIntegrable v volume 0 t :=
      ((hv.mono hsub).mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hi := intervalIntegral.integral_hasDerivAt_right hint
      (ContinuousOn.stronglyMeasurableAtFilter hI hv t (hsub ht))
      (hv.continuousAt (hI.mem_nhds (hsub ht)))
    simpa only [zero_add] using hi.const_add (1 + (g.edist p (γ 0)).toReal)
  have hmajor (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      1 + (g.edist p (γ t)).toReal ≤ q t := by
    have hlength := g.toReal_edist_le_integral_speed ht.1 hI
      (fun r hr => hsub ⟨hr.1, hr.2.trans ht.2⟩) hγ
    have htri := g.toReal_edist_triangle p (γ 0) (γ t)
    dsimp only [q, v]
    linarith
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ q t :=
    (by positivity : 0 ≤ 1 + (g.edist p (γ t)).toReal).trans (hmajor t ht)
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖v t‖ ≤ A * ‖q t‖ + 0 := by
    have hv0 : 0 ≤ v t := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0,
      abs_of_nonneg (hq t (Ico_subset_Icc_self ht)), add_zero]
    exact (hspeed t (Ico_subset_Icc_self ht)).trans
      (mul_le_mul_of_nonneg_left (hmajor t (Ico_subset_Icc_self ht)) hA)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (δ := 1 + (g.edist p (γ 0)).toReal) (K := A) (ε := 0)
    (by simp only [q, intervalIntegral.integral_same, add_zero, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 + (g.edist p (γ 0)).toReal)]; exact le_rfl)
    hbound 1 (by simp)
  rw [Real.norm_eq_abs, abs_of_nonneg (hq 1 (by simp)), gronwallBound_ε0,
    sub_zero, mul_one] at hg
  linarith [hmajor 1 (by simp)]

theorem toReal_edist_le_exp_of_linear_speed
    (g : RiemannianMetric n M) (p : M) {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hcI : Convex ℝ I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    {A : ℝ} (hA : 0 ≤ A)
    (hspeed : ∀ r ∈ uIcc s t,
      g.tangentNorm (γ r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ r 1) ≤
        A * (1 + (g.edist p (γ r)).toReal)) :
    (g.edist p (γ t)).toReal ≤
      (1 + (g.edist p (γ s)).toReal) * Real.exp (A * |t - s|) := by
  let l : ℝ → ℝ := fun r => (t - s) * r + s
  let J := l ⁻¹' I
  let δ := γ ∘ l
  have hl : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ l :=
    ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff
  have hJ : IsOpen J := hI.preimage hl.continuous
  have h01 : Icc (0 : ℝ) 1 ⊆ J := by
    intro r hr
    have h := hcI.add_smul_mem hs (show s + (t - s) ∈ I by simpa using ht) hr
    simpa only [smul_eq_mul, add_comm, mul_comm, J, mem_preimage, l] using h
  have hδ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ δ J :=
    hγ.comp hl.contMDiffOn (fun _ h => h)
  have hδspeed (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (δ r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) δ r 1) ≤
        (A * |t - s|) * (1 + (g.edist p (δ r)).toReal) := by
    have hqr := hγ.contMDiffAt (hI.mem_nhds (h01 hr))
    have hd : HasDerivAt l (t - s) r := by
      simpa only [l, mul_one, id_eq] using ((hasDerivAt_id r).const_mul (t - s)).add_const s
    have hderiv := congrArg (fun L => L (1 : ℝ))
      (mfderiv_comp r (hqr.mdifferentiableAt (by simp)) hd.differentiableAt.mdifferentiableAt)
    have hlin : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) l r 1 = t - s := by
      have he : fderiv ℝ l r 1 = t - s := by
        rw [fderiv_eq_smul_deriv, one_smul, hd.deriv]
      simpa only [mfderiv_eq_fderiv] using! he
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) δ r 1 =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (l r)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) l r 1) at hderiv
    rw [hlin] at hderiv
    have hscale : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) δ r 1 =
        (t - s) • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (l r) 1 := by
      rw [hderiv]
      simpa only [smul_eq_mul, mul_one] using
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (l r)).map_smul (t - s) (1 : ℝ)
    rw [hscale]
    have hnorm : g.tangentNorm (δ r)
        ((t - s) • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (l r) 1) =
        |t - s| * g.tangentNorm (δ r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (l r) 1) := by
      simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    rw [hnorm]
    have hsegment : l r ∈ uIcc s t := by
      have h := (convex_uIcc s t).add_smul_mem left_mem_uIcc
        (show s + (t - s) ∈ uIcc s t by simp) hr
      simpa only [l, smul_eq_mul, add_comm, mul_comm] using h
    exact (mul_le_mul_of_nonneg_left (hspeed (l r) hsegment) (abs_nonneg _)).trans_eq
      (by dsimp [δ]; ring)
  have h := g.toReal_edist_le_exp_of_linear_speed_unit p hJ h01 hδ
    (mul_nonneg hA (abs_nonneg _)) hδspeed
  simpa only [δ, Function.comp_apply, l, mul_one, sub_add_cancel, mul_zero, zero_add] using h

theorem exists_compact_confinement_of_linear_growth
    (g : RiemannianMetric n M) (hg : MetricComplete g) (p x : M)
    {X : ℝ → (y : M) → TangentSpace (𝓡 n) y}
    {a b s A : ℝ} (hs : s ∈ Icc a b) (hA : 0 ≤ A)
    (hgrowth : ∀ t ∈ Icc a b, ∀ y : M,
      g.tangentNorm y (X t y) ≤ A * (1 + (g.edist p y).toReal)) :
    ∃ K : Set M, IsCompact K ∧ ∀ (I : Set ℝ), IsOpen I → Convex ℝ I → s ∈ I →
      ∀ (γ : ℝ → M), γ s = x →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I →
        (∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) →
        ∀ t ∈ I ∩ Icc a b, γ t ∈ K := by
  let R := (1 + (g.edist p x).toReal) * Real.exp (A * (b - a))
  refine ⟨{y | g.edist p y ≤ ENNReal.ofReal R},
    g.isCompact_closedBall_of_metricComplete hg p R, ?_⟩
  intro I hI hcI hsI γ hinit hγ hODE t ht
  have hsegmentI : uIcc s t ⊆ I := hcI.ordConnected.uIcc_subset hsI ht.1
  have hsegment : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht.2
  have hspeed (r : ℝ) (hr : r ∈ uIcc s t) :
      g.tangentNorm (γ r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ r 1) ≤
        A * (1 + (g.edist p (γ r)).toReal) := by
    rw [(hODE r (hsegmentI hr)).mfderiv]
    change g.tangentNorm (γ r) ((1 : ℝ) • X r (γ r)) ≤ _
    simpa only [one_smul] using hgrowth r (hsegment hr) (γ r)
  have hbound := g.toReal_edist_le_exp_of_linear_speed p hI hcI hγ hsI ht.1 hA hspeed
  rw [hinit] at hbound
  have htime : |t - s| ≤ b - a :=
    abs_le.mpr ⟨by linarith [hs.2, ht.2.1], by linarith [hs.1, ht.2.2]⟩
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime hA)
  have hR : (g.edist p (γ t)).toReal ≤ R := hbound.trans
    (mul_le_mul_of_nonneg_left hexp (by positivity))
  exact (ENNReal.le_ofReal_iff_toReal_le (g.edist_ne_top p (γ t)) (by
    dsimp [R]; positivity)).mpr hR

end PoincareConjecture.RiemannianMetric
