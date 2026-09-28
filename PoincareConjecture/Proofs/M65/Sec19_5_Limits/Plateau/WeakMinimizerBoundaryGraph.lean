import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerSmoothGraph
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryMeasure
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerTraceBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff InnerProductSpace intervalIntegral

namespace PoincareConjecture

private theorem m65Class_norm_sq_of_ae {X : Type*} [MeasurableSpace X]
    {mu : Measure X} (u : Lp ℝ 2 mu) (f : X → ℝ) (h : u =ᵐ[mu] f) :
    ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂mu := by
  rw [ChartLpNative.scalarL2_norm_sq]
  exact integral_congr_ae (h.mono fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)

private theorem m65Continuous_boundary_memLp (f : LoopPlane → ℝ) (hf : Continuous f) :
    MemLp f 2 m65CircleBoundaryMeasure := by
  have hA := Proofs.M58.contDiff_angularPoint.continuous
  apply (memLp_map_measure_iff hf.aestronglyMeasurable
    hA.measurable.aemeasurable).mpr
  exact (memLp_two_iff_integrable_sq (hf.comp hA).aestronglyMeasurable).mpr
    (((hf.comp hA).pow 2).continuousOn.integrableOn_compact isCompact_Icc)

private theorem m65C1_trace_class_bound (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (A : Lp ℝ 2 (volume.restrict loopDiskSet))
    (B : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
    (C : Lp ℝ 2 m65CircleBoundaryMeasure)
    (hA : A =ᵐ[volume.restrict loopDiskSet] f)
    (hB : ∀ i, B i =ᵐ[volume.restrict loopDiskSet]
      fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (hC : C =ᵐ[m65CircleBoundaryMeasure] f) :
    ‖C‖ ^ 2 ≤ 3 * ‖A‖ ^ 2 + ∑ i : Fin 2, ‖B i‖ ^ 2 := by
  have hPC : m65CircleBoundaryPullback C =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => f (Proofs.M58.angularPoint t) :=
    (m65CircleBoundaryPullback_coe C).trans
      (ae_of_ae_map Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable hC)
  have hCnorm : ‖C‖ ^ 2 =
      ∫ t in (-Real.pi)..Real.pi, f (Proofs.M58.angularPoint t) ^ 2 := by
    rw [← m65CircleBoundaryPullback.norm_map C,
      m65Class_norm_sq_of_ae _ _ hPC,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
  rw [hCnorm, m65Class_norm_sq_of_ae _ _ hA]
  simp_rw [m65Class_norm_sq_of_ae _ _ (hB _)]
  exact m65C1_disk_trace_bound f hf

private theorem m65Smooth_boundary_cauchy
    (f : ℕ → LoopPlane → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    (A : ℕ → Lp ℝ 2 (volume.restrict loopDiskSet))
    (B : ℕ → Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
    (C : ℕ → Lp ℝ 2 m65CircleBoundaryMeasure)
    (hA : ∀ n, A n =ᵐ[volume.restrict loopDiskSet] f n)
    (hB : ∀ n i, B n i =ᵐ[volume.restrict loopDiskSet]
      fun z => fderiv ℝ (f n) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (hC : ∀ n, C n =ᵐ[m65CircleBoundaryMeasure] f n)
    (hAc : CauchySeq A) (hBc : ∀ i, CauchySeq (fun n => B n i)) :
    CauchySeq C := by
  have hbound (n m : ℕ) :
      dist (C n) (C m) ^ 2 ≤ 3 * dist (A n) (A m) ^ 2 +
        dist (B n 0) (B m 0) ^ 2 + dist (B n 1) (B m 1) ^ 2 := by
    have hAs : A n - A m =ᵐ[volume.restrict loopDiskSet] fun z => f n z - f m z := by
      filter_upwards [Lp.coeFn_sub (A n) (A m), hA n, hA m] with z hz hn hm
      simp only [hz, Pi.sub_apply, hn, hm]
    have hBs (i : Fin 2) : B n i - B m i =ᵐ[volume.restrict loopDiskSet]
        fun z => fderiv ℝ (fun w => f n w - f m w) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      filter_upwards [Lp.coeFn_sub (B n i) (B m i), hB n i, hB m i] with z hz hn hm
      rw [hz, Pi.sub_apply, hn, hm,
        fderiv_fun_sub ((hf n).differentiable one_ne_zero z)
          ((hf m).differentiable one_ne_zero z), sub_apply]
    have hCs : C n - C m =ᵐ[m65CircleBoundaryMeasure] fun z => f n z - f m z := by
      filter_upwards [Lp.coeFn_sub (C n) (C m), hC n, hC m] with z hz hn hm
      simp only [hz, Pi.sub_apply, hn, hm]
    have hb := m65C1_trace_class_bound _ ((hf n).sub (hf m))
      (A n - A m) (fun i => B n i - B m i) (C n - C m) hAs hBs hCs
    simpa only [← dist_eq_norm, Fin.sum_univ_two, add_assoc] using hb
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  have heps3 : 0 < eps / 3 := by positivity
  obtain ⟨NA, hNA⟩ := Metric.cauchySeq_iff.mp hAc (eps / 3) heps3
  obtain ⟨N0, hN0⟩ := Metric.cauchySeq_iff.mp (hBc 0) (eps / 3) heps3
  obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.mp (hBc 1) (eps / 3) heps3
  refine ⟨max NA (max N0 N1), ?_⟩
  intro n hn m hm
  have hna := le_trans (le_max_left _ _) hn
  have hma := le_trans (le_max_left _ _) hm
  have hn0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hm0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hn1 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hm1 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have ha := (sq_lt_sq₀ dist_nonneg heps3.le).mpr (hNA n hna m hma)
  have h0 := (sq_lt_sq₀ dist_nonneg heps3.le).mpr (hN0 n hn0 m hm0)
  have h1 := (sq_lt_sq₀ dist_nonneg heps3.le).mpr (hN1 n hn1 m hm1)
  nlinarith [hbound n m, dist_nonneg (x := C n) (y := C m)]

theorem m65WeakTrace_exists_smooth_boundary_graph
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 m65CircleBoundaryMeasure}
    (htrace : M65DiskWeakTrace u d (m65CircleBoundaryPullback b)) :
    ∃ (f : ℕ → LoopPlane → ℝ)
      (A : ℕ → Lp ℝ 2 (volume.restrict loopDiskSet))
      (B : ℕ → Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
      (C : ℕ → Lp ℝ 2 m65CircleBoundaryMeasure),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧
      (∀ n, A n =ᵐ[volume.restrict loopDiskSet] f n) ∧
      (∀ n i, B n i =ᵐ[volume.restrict loopDiskSet]
        fun z => fderiv ℝ (f n) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) ∧
      (∀ n, C n =ᵐ[m65CircleBoundaryMeasure] f n) ∧
      Tendsto A atTop (𝓝 u) ∧
      (∀ i, Tendsto (fun n => B n i) atTop (𝓝 (d i))) ∧
      Tendsto C atTop (𝓝 b) := by
  obtain ⟨f, A, B, hf, hA, hB, hAlim, hBlim⟩ :=
    m65WeakTrace_exists_smooth_graph htrace
  have hcL2 (n : ℕ) := m65Continuous_boundary_memLp (f n) (hf n).continuous
  let C (n : ℕ) : Lp ℝ 2 m65CircleBoundaryMeasure := (hcL2 n).toLp (f n)
  have hC (n : ℕ) : C n =ᵐ[m65CircleBoundaryMeasure] f n := (hcL2 n).coeFn_toLp
  have hPC (n : ℕ) : m65CircleBoundaryPullback (C n)
      =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
        fun t => f n (Proofs.M58.angularPoint t) :=
    (m65CircleBoundaryPullback_coe (C n)).trans
      (ae_of_ae_map Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable (hC n))
  have hCc := m65Smooth_boundary_cauchy f (fun n => (hf n).of_le (by simp))
    A B C hA hB hC hAlim.cauchySeq (fun i => (hBlim i).cauchySeq)
  obtain ⟨c, hclim⟩ := cauchySeq_tendsto_of_complete hCc
  have htraces (n : ℕ) : M65DiskWeakTrace (A n) (B n)
      (m65CircleBoundaryPullback (C n)) := by
    have hfa : MemLp (f n) 2 (volume.restrict loopDiskSet) :=
      (Lp.memLp (A n)).ae_eq (hA n)
    have hfb (i : Fin 2) : MemLp
        (fun z => fderiv ℝ (f n) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2
          (volume.restrict loopDiskSet) := (Lp.memLp (B n i)).ae_eq (hB n i)
    have hfc : MemLp (fun t => f n (Proofs.M58.angularPoint t)) 2
        (volume.restrict (Icc (-Real.pi) Real.pi)) :=
      (Lp.memLp (m65CircleBoundaryPullback (C n))).ae_eq (hPC n)
    have haeq : hfa.toLp (f n) = A n := Lp.ext (hfa.coeFn_toLp.trans (hA n).symm)
    have hbeq : (fun i => (hfb i).toLp
        (fun z => fderiv ℝ (f n) z (EuclideanSpace.basisFun (Fin 2) ℝ i))) = B n := by
      funext i
      exact Lp.ext ((hfb i).coeFn_toLp.trans (hB n i).symm)
    have hceq : hfc.toLp (fun t => f n (Proofs.M58.angularPoint t)) =
        m65CircleBoundaryPullback (C n) := Lp.ext (hfc.coeFn_toLp.trans (hPC n).symm)
    have hh := m65DiskWeakTrace_of_C1 (f n) ((hf n).of_le (by simp)) hfa hfb hfc
    rwa [haeq, hbeq, hceq] at hh
  have hctrace : M65DiskWeakTrace u d (m65CircleBoundaryPullback c) :=
    m65DiskWeakTrace_of_limit htraces hAlim
      (fun i v => (hBlim i).inner tendsto_const_nhds)
      ((m65CircleBoundaryPullback.continuous.tendsto c).comp hclim)
  have hcb : c = b := m65CircleBoundary_trace_unique hctrace htrace
  exact ⟨f, A, B, C, hf, hA, hB, hC, hAlim, hBlim, hcb ▸ hclim⟩

end PoincareConjecture
