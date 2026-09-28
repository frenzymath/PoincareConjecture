import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationPeriodic
import Mathlib.Algebra.Field.Periodic










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Bundle MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65Perturbation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] {a b : ℝ} {J : Set ℝ}

omit [NormedSpace ℝ P] [T2Space M] in



theorem residual_zero_at_original (F : RicciFlow 3 M (Icc a b)) (hJ : IsOpen J)
    (C : M65SmoothFilledLoopFamily F J)
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M))
    (hbase : ∀ q ∈ J, ∀ x, periodicFreeLoop (Gamma 0 q) x = periodicFreeLoop (C.loops q) x)
    (hCSF : ∀ q ∈ J, ∀ x,
      curveVelocity (n := 3) (fun t => periodicFreeLoop (C.loops t) x) q =
        m62CurvatureVector F (fun y t => periodicFreeLoop (C.loops t) y) q x)
    (q : ℝ) (hq : q ∈ J) (x : ℝ) :
    (F.metric q).tangentNorm (periodicFreeLoop (Gamma 0 q) x)
      (curveVelocity (n := 3) (fun t => periodicFreeLoop (Gamma 0 t) x) q -
        m62CurvatureVector F (fun y t => periodicFreeLoop (Gamma 0 t) y) q x) = 0 := by
  have he : (fun t => periodicFreeLoop (Gamma 0 t) x) =ᶠ[𝓝 q]
      (fun t => periodicFreeLoop (C.loops t) x) := by
    filter_upwards [hJ.mem_nhds hq] with t ht
    exact hbase t ht x
  have hv : (curveVelocity (n := 3) (fun t => periodicFreeLoop (Gamma 0 t) x) q :
      LoopAmbient) = curveVelocity (n := 3) (fun t => periodicFreeLoop (C.loops t) x) q :=
    congrArg (fun A : ℝ →L[ℝ] LoopAmbient => A 1)
      (he.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
  have hs : periodicFreeLoop (Gamma 0 q) = periodicFreeLoop (C.loops q) :=
    funext (hbase q hq)
  have hH : (m62CurvatureVector F (fun y t => periodicFreeLoop (Gamma 0 t) y) q x :
      LoopAmbient) = m62CurvatureVector F (fun y t => periodicFreeLoop (C.loops t) y) q x := by
    let H (c : ℝ → M) : LoopAmbient :=
      ((F.metric q).tangentNorm (c x) (curveVelocity (n := 3) c x))⁻¹ •
        rampHorizontalCovariantDerivative (F.connection q) c
          (fun y => ((F.metric q).tangentNorm (c y) (curveVelocity (n := 3) c y))⁻¹ •
            curveVelocity (n := 3) c y) x
    change H (periodicFreeLoop (Gamma 0 q)) = H (periodicFreeLoop (C.loops q))
    exact congrArg H hs
  have hzero : (curveVelocity (n := 3) (fun t => periodicFreeLoop (Gamma 0 t) x) q -
      m62CurvatureVector F (fun y t => periodicFreeLoop (Gamma 0 t) y) q x : LoopAmbient) = 0 := by
    rw [hv, hH, hCSF q hq x, sub_self]
  simp only [RiemannianMetric.tangentNorm, hzero, map_zero, Real.sqrt_zero]





theorem exists_uniform_residual_radius (F : RicciFlow 3 M (Icc a b))
    (hJ : IsOpen J) (hJF : J ⊆ Ioo a b) (C : M65SmoothFilledLoopFamily F J)
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M)) (delta : ℝ) (hdelta : 0 < delta)
    (hGamma : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1) (ball 0 delta ×ˢ (univ ×ˢ J)))
    (himm : ∀ p ∈ ball 0 delta, ∀ q ∈ J, ∀ x,
      curveVelocity (n := 3) (periodicFreeLoop (Gamma p q)) x ≠ 0)
    (hbase : ∀ q ∈ J, ∀ x, periodicFreeLoop (Gamma 0 q) x = periodicFreeLoop (C.loops q) x)
    (hCSF : ∀ q ∈ J, ∀ x,
      curveVelocity (n := 3) (fun t => periodicFreeLoop (C.loops t) x) q =
        m62CurvatureVector F (fun y t => periodicFreeLoop (C.loops t) y) q x)
    (K : Set ℝ) (hK : IsCompact K) (hKJ : K ⊆ J)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ delta ∧
      ∀ p ∈ ball 0 eta, ∀ q ∈ K, ∀ x,
        (F.metric q).tangentNorm (periodicFreeLoop (Gamma p q) x)
          (curveVelocity (n := 3) (fun t => periodicFreeLoop (Gamma p t) x) q -
            m62CurvatureVector F (fun y t => periodicFreeLoop (Gamma p t) y) q x) ≤ epsilon := by
  let U : Set (P × (ℝ × ℝ)) := ball 0 delta ×ˢ (univ ×ˢ J)
  let R : P × (ℝ × ℝ) → ℝ := fun z =>
    (F.metric z.2.2).tangentNorm (periodicFreeLoop (Gamma z.1 z.2.2) z.2.1)
      (curveVelocity (n := 3) (fun t => periodicFreeLoop (Gamma z.1 t) z.2.1) z.2.2 -
        m62CurvatureVector F (fun y t => periodicFreeLoop (Gamma z.1 t) y) z.2.2 z.2.1)
  have hU : IsOpen U := isOpen_ball.prod (isOpen_univ.prod hJ)
  have hR : ContinuousOn R U := residual_continuousOn F _ U hU
    (fun z hz => Ioo_subset_Icc_self (hJF hz.2.2)) hGamma
      (fun z hz => himm z.1 hz.1 z.2.2 hz.2.2 z.2.1)
  have hperiod : 0 < rampPeriod := by unfold rampPeriod; positivity
  have hevent : ∀ z ∈ Icc 0 rampPeriod ×ˢ K,
      ∀ᶠ w in 𝓝 ((0 : P), z), R w < epsilon := by
    intro z hz
    have hmem : ((0 : P), z) ∈ U :=
      ⟨mem_ball_self hdelta, mem_univ _, hKJ hz.2⟩
    have hzero : R (0, z) = 0 := residual_zero_at_original F hJ C Gamma hbase hCSF
      z.2 (hKJ hz.2) z.1
    exact (hR.continuousAt (hU.mem_nhds hmem)).eventually_lt_const (hzero ▸ hepsilon)
  have hall : ∀ᶠ p in 𝓝 (0 : P), ∀ z ∈ Icc 0 rampPeriod ×ˢ K, R (p, z) < epsilon :=
    (isCompact_Icc.prod hK).eventually_forall_of_forall_eventually
      (x₀ := (0 : P)) (P := fun p z => R (p, z) < epsilon) hevent
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨min eta delta, lt_min heta hdelta, min_le_right _ _, ?_⟩
  intro p hp q hq x
  obtain ⟨y, hy, hxy⟩ := (residual_periodic F (Gamma p) q).exists_mem_Ico₀ hperiod x
  rw [hxy]
  exact (hball (ball_subset_ball (min_le_left _ _) hp) (y, q)
    ⟨Ico_subset_Icc_self hy, hq⟩).le

omit [T2Space M] in



theorem exists_uniform_length_bound {N : ℕ} (F : RicciFlow 3 M (Icc a b))
    (hJ : IsOpen J) (hJF : J ⊆ Ioo a b)
    (Gamma : (Fin N → ℝ) → ℝ → C1FreeLoopSpace (M := M))
    (delta : ℝ) (hdelta : 0 < delta)
    (hGamma : ContMDiffOn 𝓘(ℝ, (Fin N → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1) (ball 0 delta ×ˢ (univ ×ˢ J)))
    (himm : ∀ p ∈ ball 0 delta, ∀ q ∈ J, ∀ x,
      curveVelocity (n := 3) (periodicFreeLoop (Gamma p q)) x ≠ 0)
    (K : Set ℝ) (hK : IsCompact K) (hKJ : K ⊆ J) :
    ∃ eta L : ℝ, 0 < eta ∧ eta ≤ delta ∧ 0 ≤ L ∧
      ∀ p ∈ ball 0 eta, ∀ q ∈ K, freeLoopLength (F.metric q) (Gamma p q) ≤ L := by
  let V : (Fin N → ℝ) × (ℝ × ℝ) → ℝ := fun z =>
    curveSpeed F (fun x t => periodicFreeLoop (Gamma z.1 t) x) z.2.2 z.2.1
  have hV : ContinuousOn V (ball 0 delta ×ˢ (univ ×ˢ J)) :=
    (speed_contDiffOn F _ _ (isOpen_ball.prod (isOpen_univ.prod hJ))
      (fun z hz => Ioo_subset_Icc_self (hJF hz.2.2)) hGamma
        (fun z hz => himm z.1 hz.1 z.2.2 hz.2.2 z.2.1)).continuousOn
  have hsub : closedBall (0 : Fin N → ℝ) (delta / 2) ×ˢ (Icc 0 rampPeriod ×ˢ K) ⊆
      ball 0 delta ×ˢ (univ ×ˢ J) := by
    intro z hz
    refine ⟨?_, mem_univ _, hKJ hz.2.2⟩
    exact mem_ball.mpr ((mem_closedBall.mp hz.1).trans_lt (by linarith))
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : Fin N → ℝ) (delta / 2)).prod
    (isCompact_Icc.prod hK)).exists_bound_of_continuousOn (hV.mono hsub)
  have hperiod : 0 ≤ rampPeriod := by unfold rampPeriod; positivity
  refine ⟨delta / 2, rampPeriod * max B 0, by positivity, by linarith,
    mul_nonneg hperiod (le_max_right _ _), ?_⟩
  intro p hp q hq
  have hi := (Proofs.M58.continuous_freeLoopSpeed (F.metric q) (Gamma p q)).intervalIntegrable
    (μ := volume) (0 : ℝ) rampPeriod
  have hbound : ∀ x ∈ Icc 0 rampPeriod,
      (F.metric q).tangentNorm (periodicFreeLoop (Gamma p q) x)
        (curveVelocity (n := 3) (periodicFreeLoop (Gamma p q)) x) ≤ max B 0 := by
    intro x hx
    exact (le_abs_self (V (p, (x, q)))).trans (by
      simpa only [Real.norm_eq_abs] using
        (hB (p, (x, q)) ⟨ball_subset_closedBall hp, hx, hq⟩).trans (le_max_left B 0))
  have h := intervalIntegral.integral_mono_on hperiod hi
    (intervalIntegrable_const (c := max B 0)) hbound
  simpa only [freeLoopLength, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

end PoincareConjecture.M65Perturbation
