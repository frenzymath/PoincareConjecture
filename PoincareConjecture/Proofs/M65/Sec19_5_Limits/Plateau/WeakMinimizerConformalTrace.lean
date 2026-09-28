import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformalPullback
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

private theorem m65SmoothDisk_chain_operator (φ : LoopPlane → LoopPlane)
    (hφ : ContDiff ℝ 1 φ)
    (T : Lp ℝ 2 (volume.restrict loopDiskSet) →L[ℝ] Lp ℝ 2 (volume.restrict loopDiskSet))
    (hT : ∀ u, T u =ᵐ[volume.restrict loopDiskSet] fun z => u (φ z)) :
    ∃ R : Fin 2 → (Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)) →L[ℝ]
        Lp ℝ 2 (volume.restrict loopDiskSet),
      ∀ i d, R i d =ᵐ[volume.restrict loopDiskSet] fun z =>
        ∑ j : Fin 2, (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d j (φ z) := by
  let a (i j : Fin 2) (z : LoopPlane) :=
    (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j
  have ha (i j : Fin 2) : Continuous (a i j) :=
    (EuclideanSpace.proj j).continuous.comp
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hex (i j : Fin 2) : ∃ C : ℝ, ∀ z ∈ loopDiskSet, ‖a i j z‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : LoopPlane) 1).bddAbove_image
      (ha i j).norm.continuousOn
    exact ⟨C, fun z hz => hC ⟨z, hz, rfl⟩⟩
  choose C hC using hex
  let A (i j : Fin 2) (z : LoopPlane) := a i j z • ContinuousLinearMap.id ℝ ℝ
  have hA (i j : Fin 2) : AEStronglyMeasurable (A i j) (volume.restrict loopDiskSet) :=
    ((ha i j).smul continuous_const).aestronglyMeasurable
  have hbound (i j : Fin 2) : ∀ᵐ z ∂volume.restrict loopDiskSet, ‖A i j z‖ ≤ C i j := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    simpa only [A, norm_smul, ContinuousLinearMap.norm_id, mul_one] using hC i j z hz
  let L (i j : Fin 2) := Lp.coefficientL2 (A i j) (hA i j) (C i j) (hbound i j)
  let R (i : Fin 2) : (Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)) →L[ℝ]
      Lp ℝ 2 (volume.restrict loopDiskSet) :=
    ((L i 0).comp T).comp (ContinuousLinearMap.proj 0) +
      ((L i 1).comp T).comp (ContinuousLinearMap.proj 1)
  refine ⟨R, ?_⟩
  intro i d
  filter_upwards [Lp.coeFn_add (L i 0 (T (d 0))) (L i 1 (T (d 1))),
    Lp.coefficientL2_ae (A i 0) (hA i 0) (C i 0) (hbound i 0) (T (d 0)),
    Lp.coefficientL2_ae (A i 1) (hA i 1) (C i 1) (hbound i 1) (T (d 1)),
    hT (d 0), hT (d 1)] with z hz h0 h1 ht0 ht1
  change (L i 0 (T (d 0)) + L i 1 (T (d 1)) : Lp ℝ 2 _) z = _
  rw [hz]
  change L i 0 (T (d 0)) z + L i 1 (T (d 1)) z = _
  rw [h0, h1]
  simp only [A, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, ht0, ht1, Fin.sum_univ_two, a]

private theorem m65SmoothDisk_true_chain (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (φ : LoopPlane → LoopPlane) (hφ : ContDiff ℝ 1 φ) (z : LoopPlane) (i : Fin 2) :
    fderiv ℝ (f ∘ φ) z (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      ∑ j : Fin 2, (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j *
        fderiv ℝ f (φ z) (EuclideanSpace.basisFun (Fin 2) ℝ j) := by
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  let v := fderiv ℝ φ z (B i)
  have hv : v = v 0 • B 0 + v 1 • B 1 := by
    ext j
    fin_cases j <;> simp [B, EuclideanSpace.basisFun_apply]
  rw [fderiv_comp z (hf.differentiable one_ne_zero (φ z))
    (hφ.differentiable one_ne_zero z)]
  change fderiv ℝ f (φ z) v = _
  rw [hv, map_add, map_smul, map_smul]
  simp only [Fin.sum_univ_two, smul_eq_mul, v, B]

private theorem m65SmoothDisk_C1_trace (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
    (u : Lp ℝ 2 (volume.restrict loopDiskSet))
    (d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
    (b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hu : u =ᵐ[volume.restrict loopDiskSet] f)
    (hd : ∀ i, d i =ᵐ[volume.restrict loopDiskSet]
      fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (hb : b =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => f (Proofs.M58.angularPoint t)) : M65DiskWeakTrace u d b := by
  have hfa := (Lp.memLp u).ae_eq hu
  have hfd (i : Fin 2) := (Lp.memLp (d i)).ae_eq (hd i)
  have hfb := (Lp.memLp b).ae_eq hb
  have hu' : hfa.toLp f = u := Lp.ext (hfa.coeFn_toLp.trans hu.symm)
  have hd' : (fun i => (hfd i).toLp
      (fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i))) = d := by
    funext i
    exact Lp.ext ((hfd i).coeFn_toLp.trans (hd i).symm)
  have hb' : hfb.toLp (fun t => f (Proofs.M58.angularPoint t)) = b :=
    Lp.ext (hfb.coeFn_toLp.trans hb.symm)
  have h := m65DiskWeakTrace_of_C1 f hf hfa hfd hfb
  rwa [hu', hd', hb'] at h






theorem m65WeakTrace_smooth_change (φ ψ : LoopPlane → LoopPlane)
    (hφ : ContDiff ℝ 1 φ) (hψ : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 ψ z)
    (hφdisk : MapsTo φ loopDiskSet loopDiskSet)
    (hψdisk : MapsTo ψ loopDiskSet loopDiskSet)
    (hφcircle : ∀ z, ‖z‖ = 1 → ‖φ z‖ = 1)
    (hψcircle : ∀ z, ‖z‖ = 1 → ‖ψ z‖ = 1)
    (hleft : ∀ z ∈ loopDiskSet, ψ (φ z) = z)
    (hright : ∀ z ∈ loopDiskSet, φ (ψ z) = z)
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 m65CircleBoundaryMeasure}
    (htrace : M65DiskWeakTrace u d (m65CircleBoundaryPullback b)) :
    ∃ (U : Lp ℝ 2 (volume.restrict loopDiskSet))
      (D : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
      (B : Lp ℝ 2 m65CircleBoundaryMeasure),
      U =ᵐ[volume.restrict loopDiskSet] (fun z => u (φ z)) ∧
      (∀ i, D i =ᵐ[volume.restrict loopDiskSet] fun z =>
        ∑ j : Fin 2, (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d j (φ z)) ∧
      B =ᵐ[m65CircleBoundaryMeasure] (fun z => b (φ z)) ∧
      M65DiskWeakTrace U D (m65CircleBoundaryPullback B) := by
  obtain ⟨Cd, hCd, hdom⟩ := m65SmoothDisk_map_bound φ ψ (fun _ _ => hφ.contDiffAt)
    hψ hφdisk hψdisk hleft hright
  obtain ⟨Cb, hCb, hbdom⟩ := m65SmoothCircle_map_bound φ ψ hφ.continuous hψ
    hφcircle hψcircle hleft hright
  let T : Lp ℝ 2 (volume.restrict loopDiskSet) →L[ℝ]
      Lp ℝ 2 (volume.restrict loopDiskSet) :=
    ChartLpNative.dominatedPullbackL2 φ hφ.continuous.measurable.aemeasurable hCd hdom
  let S : Lp ℝ 2 m65CircleBoundaryMeasure →L[ℝ] Lp ℝ 2 m65CircleBoundaryMeasure :=
    ChartLpNative.dominatedPullbackL2 φ hφ.continuous.measurable.aemeasurable hCb hbdom
  have hT (v : Lp ℝ 2 (volume.restrict loopDiskSet)) :
      T v =ᵐ[volume.restrict loopDiskSet] fun z => v (φ z) :=
    ChartLpNative.dominatedPullbackL2_coe _ _ _ _ v
  have hS (v : Lp ℝ 2 m65CircleBoundaryMeasure) :
      S v =ᵐ[m65CircleBoundaryMeasure] fun z => v (φ z) :=
    ChartLpNative.dominatedPullbackL2_coe _ _ _ _ v
  have hpull {P : LoopPlane → Prop} (hP : ∀ᵐ z ∂volume.restrict loopDiskSet, P z) :
      ∀ᵐ z ∂volume.restrict loopDiskSet, P (φ z) :=
    ae_of_ae_map hφ.continuous.measurable.aemeasurable
      (ae_mono hdom (Measure.ae_smul_measure hP Cd))
  have hbpull {P : LoopPlane → Prop} (hP : ∀ᵐ z ∂m65CircleBoundaryMeasure, P z) :
      ∀ᵐ z ∂m65CircleBoundaryMeasure, P (φ z) :=
    ae_of_ae_map hφ.continuous.measurable.aemeasurable
      (ae_mono hbdom (Measure.ae_smul_measure hP Cb))
  obtain ⟨R, hR⟩ := m65SmoothDisk_chain_operator φ hφ T hT
  refine ⟨T u, fun i => R i d, S b, hT u, fun i => hR i d, hS b, ?_⟩
  obtain ⟨f, A, B, C, hf, hA, hB, hC, hAlim, hBlim, hClim⟩ :=
    m65WeakTrace_exists_smooth_boundary_graph htrace
  have hTA (n : ℕ) : T (A n) =ᵐ[volume.restrict loopDiskSet] f n ∘ φ :=
    (hT (A n)).trans (hpull (hA n))
  have hRB (n : ℕ) (i : Fin 2) : R i (B n) =ᵐ[volume.restrict loopDiskSet]
      fun z => fderiv ℝ (f n ∘ φ) z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    filter_upwards [hR i (B n), hpull (hB n 0), hpull (hB n 1)] with z hz h0 h1
    rw [hz, m65SmoothDisk_true_chain (f n) ((hf n).of_le (by simp)) φ hφ z i]
    simp only [Fin.sum_univ_two, h0, h1]
  have hSC (n : ℕ) : S (C n) =ᵐ[m65CircleBoundaryMeasure] f n ∘ φ :=
    (hS (C n)).trans (hbpull (hC n))
  have hPC (n : ℕ) : m65CircleBoundaryPullback (S (C n)) =ᵐ[
      volume.restrict (Icc (-Real.pi) Real.pi)]
        fun t => f n (φ (Proofs.M58.angularPoint t)) :=
    (m65CircleBoundaryPullback_coe (S (C n))).trans
      (ae_of_ae_map Proofs.M58.contDiff_angularPoint.continuous.measurable.aemeasurable (hSC n))
  have htraces (n : ℕ) : M65DiskWeakTrace (T (A n)) (fun i => R i (B n))
      (m65CircleBoundaryPullback (S (C n))) :=
    m65SmoothDisk_C1_trace (f n ∘ φ) (((hf n).of_le (by simp)).comp hφ)
      _ _ _ (hTA n) (hRB n) (hPC n)
  have hBpi : Tendsto B atTop (𝓝 d) := tendsto_pi_nhds.mpr hBlim
  have hRlim (i : Fin 2) : Tendsto (fun n => R i (B n)) atTop (𝓝 (R i d)) :=
    ((R i).continuous.tendsto d).comp hBpi
  exact m65DiskWeakTrace_of_limit htraces ((T.continuous.tendsto u).comp hAlim)
    (fun i v => (hRlim i).inner tendsto_const_nhds)
    ((m65CircleBoundaryPullback.continuous.tendsto (S b)).comp
      ((S.continuous.tendsto b).comp hClim))

end PoincareConjecture
