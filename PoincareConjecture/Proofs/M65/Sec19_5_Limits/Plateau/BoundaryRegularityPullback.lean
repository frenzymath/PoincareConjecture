import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceCoordinates
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryGraph
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture.M65Boundary

open M65StrictTrace

def diskBoundaryCoordinate (p : ℂ) (z : LoopPlane) : LoopPlane :=
  orthonormalBasisOneI.repr (boundaryCoordinate p (orthonormalBasisOneI.repr.symm z))

def diskBoundaryInverse (p : ℂ) (w : LoopPlane) : LoopPlane :=
  orthonormalBasisOneI.repr (boundaryInverse p (orthonormalBasisOneI.repr.symm w))

theorem contDiff_diskBoundaryCoordinate (p : ℂ) : ContDiff ℝ ∞ (diskBoundaryCoordinate p) :=
  orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.comp
    (((contDiff_boundaryCoordinate p).restrict_scalars ℝ).comp
      orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.contDiff)

theorem norm_diskBoundaryCoordinate {p : ℂ} (hp : ‖p‖ = 1) (z : LoopPlane) :
    ‖diskBoundaryCoordinate p z‖ = Real.exp (-z 1) := by
  rw [diskBoundaryCoordinate, orthonormalBasisOneI.repr.norm_map,
    norm_boundaryCoordinate hp]
  simp [orthonormalBasisOneI_repr_symm_apply]

private theorem compact_inverse_map_bound (K : Set LoopPlane) (hK : IsCompact K)
    (φ ψ : LoopPlane → LoopPlane) (hφ : Continuous φ)
    (hcap : MapsTo φ K loopDiskSet)
    (hψ : ∀ w ∈ φ '' K, ContDiffAt ℝ 1 ψ w)
    (hleft : ∀ z ∈ K, ψ (φ z) = z) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (volume.restrict K).map φ ≤ C • volume.restrict loopDiskSet := by
  let L := φ '' K
  have hL : IsCompact L := hK.image hφ
  have hJ : ContinuousOn (fun z => |(fderiv ℝ ψ z).det|) L := by
    intro z hz
    exact ((ContinuousLinearMap.continuous_det.continuousAt.comp
      ((hψ z hz).continuousAt_fderiv one_ne_zero)).abs).continuousWithinAt
  obtain ⟨B, hB⟩ := hL.bddAbove_image hJ
  refine ⟨ENNReal.ofReal B, ENNReal.ofReal_ne_top, Measure.le_iff.mpr ?_⟩
  intro A hA
  have heq : φ ⁻¹' A ∩ K = ψ '' (A ∩ L) := by
    ext z
    constructor
    · rintro ⟨hzA, hz⟩
      exact ⟨φ z, ⟨hzA, mem_image_of_mem φ hz⟩, hleft z hz⟩
    · rintro ⟨w, ⟨hwA, v, hv, rfl⟩, rfl⟩
      rw [hleft v hv]
      exact ⟨hwA, hv⟩
  rw [Measure.map_apply hφ.measurable hA, Measure.restrict_apply' hK.measurableSet,
    heq, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  calc
    _ ≤ ∫⁻ z in A ∩ L, ENNReal.ofReal |(fderiv ℝ ψ z).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume (hA.inter hL.measurableSet)
        (fun z hz => ((hψ z hz.2).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt)
    _ ≤ ∫⁻ _z in A ∩ L, ENNReal.ofReal B := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hA.inter hL.measurableSet)] with z hz
      exact ENNReal.ofReal_le_ofReal (hB ⟨z, hz.2, rfl⟩)
    _ = ENNReal.ofReal B * volume (A ∩ L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (measure_mono (inter_subset_inter_right A hcap.image_subset)) bot_le

theorem exists_boundary_halfDisk_pullback {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ closedBall (0 : LoopPlane) R,
        diskBoundaryInverse p (diskBoundaryCoordinate p z) = z) ∧
      let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
      MapsTo (diskBoundaryCoordinate p) K loopDiskSet ∧
        (∀ w ∈ diskBoundaryCoordinate p '' K, ContDiffAt ℝ 1 (diskBoundaryInverse p) w) ∧
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
          (volume.restrict K).map (diskBoundaryCoordinate p) ≤ C • volume.restrict loopDiskSet := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  have hP := contDiff_diskBoundaryCoordinate p
  have hP0 : P 0 = e p := by simp [P, e, diskBoundaryCoordinate, boundaryCoordinate]
  have hQ : ContDiffAt ℝ 1 Q (e p) := by
    have hc : ContDiffAt ℝ 1 (boundaryInverse p) p :=
      ((contDiffAt_boundaryInverse hp0).restrict_scalars ℝ).of_le (by simp)
    have hcomp := e.contDiff.contDiffAt.comp p hc
    have hinv : ContDiffAt ℝ 1 e.symm (e p) := e.symm.contDiff.contDiffAt
    have hcomp' : ContDiffAt ℝ 1 (e ∘ boundaryInverse p) (e.symm (e p)) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hcomp
    exact hcomp'.comp (e p) hinv
  have hregular : ∀ᶠ z in 𝓝 (0 : LoopPlane), ContDiffAt ℝ 1 Q (P z) := by
    have hconv : Tendsto P (𝓝 0) (𝓝 (e p)) := by
      have hh : Tendsto P (𝓝 0) (𝓝 (P 0)) := hP.continuous.tendsto 0
      rwa [hP0] at hh
    exact hconv.eventually (hQ.eventually (by simp))
  have hleft : ∀ᶠ z in 𝓝 (0 : LoopPlane), Q (P z) = z := by
    have hconv : Tendsto e.symm (𝓝 (0 : LoopPlane)) (𝓝 (0 : ℂ)) := by
      simpa only [map_zero] using e.symm.continuous.tendsto 0
    filter_upwards [hconv.eventually (boundaryInverse_coordinate_eventually hp0)] with z hz
    change boundaryInverse p (boundaryCoordinate p (orthonormalBasisOneI.repr.symm z)) =
      orthonormalBasisOneI.repr.symm z at hz
    change orthonormalBasisOneI.repr
      (boundaryInverse p (orthonormalBasisOneI.repr.symm
        (orthonormalBasisOneI.repr (boundaryCoordinate p (orthonormalBasisOneI.repr.symm z))))) = z
    rw [LinearIsometryEquiv.symm_apply_apply, hz, LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨δ, hδ, hδall⟩ := Metric.mem_nhds_iff.mp (inter_mem hleft hregular)
  let R := δ / 2
  have hr : 0 < R := half_pos hδ
  have hball (z : LoopPlane) (hz : z ∈ closedBall (0 : LoopPlane) R) :
      Q (P z) = z ∧ ContDiffAt ℝ 1 Q (P z) :=
    hδall ((closedBall_subset_ball (by dsimp only [R]; linarith)) hz)
  let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hcap : MapsTo P K loopDiskSet := by
    intro z hz
    rw [loopDiskSet, mem_closedBall_zero_iff, norm_diskBoundaryCoordinate hp,
      Real.exp_le_one_iff]
    exact neg_nonpos.mpr hz.2
  have hQr : ∀ w ∈ P '' K, ContDiffAt ℝ 1 Q w := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hball z hz.1).2
  exact ⟨R, hr, fun z hz => (hball z hz).1, hcap, hQr,
    compact_inverse_map_bound K hK P Q hP.continuous hcap hQr (fun z hz => (hball z hz.1).1)⟩

theorem exists_uniform_boundary_halfDisk_pullback :
    ∃ R : ℝ, 0 < R ∧ ∀ (p : ℂ), ‖p‖ = 1 →
      (∀ z ∈ closedBall (0 : LoopPlane) R,
        diskBoundaryInverse p (diskBoundaryCoordinate p z) = z) ∧
      let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
      MapsTo (diskBoundaryCoordinate p) K loopDiskSet ∧
        (∀ w ∈ diskBoundaryCoordinate p '' K, ContDiffAt ℝ 1 (diskBoundaryInverse p) w) ∧
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
          (volume.restrict K).map (diskBoundaryCoordinate p) ≤ C • volume.restrict loopDiskSet := by
  obtain ⟨R, hR, hleft1, _hcap1, hreg1, _C1, _hC1, _hmap1⟩ :=
    exists_boundary_halfDisk_pullback (p := (1 : ℂ)) norm_one
  refine ⟨R, hR, ?_⟩
  intro p hp
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let T : LoopPlane → LoopPlane := fun w => e (e.symm w / p)
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  have hT : ContDiff ℝ 1 T :=
    e.contDiff.comp ((contDiff_id.div_const p).comp e.symm.contDiff)
  have hTP (z : LoopPlane) :
      T (diskBoundaryCoordinate p z) = diskBoundaryCoordinate 1 z := by
    change orthonormalBasisOneI.repr
      (orthonormalBasisOneI.repr.symm
        (orthonormalBasisOneI.repr (p * exp (I * orthonormalBasisOneI.repr.symm z))) / p) =
      orthonormalBasisOneI.repr (1 * exp (I * orthonormalBasisOneI.repr.symm z))
    rw [LinearIsometryEquiv.symm_apply_apply, one_mul]
    congr 1
    field_simp
  have hQ : diskBoundaryInverse p = diskBoundaryInverse 1 ∘ T := by
    funext w
    change orthonormalBasisOneI.repr (-I * log (orthonormalBasisOneI.repr.symm w / p)) =
      orthonormalBasisOneI.repr (-I * log (orthonormalBasisOneI.repr.symm
        (orthonormalBasisOneI.repr (orthonormalBasisOneI.repr.symm w / p)) / 1))
    rw [LinearIsometryEquiv.symm_apply_apply, div_one]
  have hleft (z : LoopPlane) (hz : z ∈ closedBall (0 : LoopPlane) R) :
      diskBoundaryInverse p (diskBoundaryCoordinate p z) = z := by
    rw [hQ, Function.comp_apply, hTP]
    exact hleft1 z hz
  let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hcap : MapsTo (diskBoundaryCoordinate p) K loopDiskSet := by
    intro z hz
    rw [loopDiskSet, mem_closedBall_zero_iff, norm_diskBoundaryCoordinate hp, Real.exp_le_one_iff]
    exact neg_nonpos.mpr hz.2
  have hreg : ∀ w ∈ diskBoundaryCoordinate p '' K, ContDiffAt ℝ 1 (diskBoundaryInverse p) w := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hQ]
    apply ContDiffAt.comp _ _ hT.contDiffAt
    rw [hTP]
    exact hreg1 _ (mem_image_of_mem _ hz)
  exact ⟨hleft, hcap, hreg,
    compact_inverse_map_bound K hK _ _ (contDiff_diskBoundaryCoordinate p).continuous
      hcap hreg (fun z hz => hleft z hz.1)⟩

private theorem compact_chain_operator (K : Set LoopPlane) (hK : IsCompact K)
    (φ : LoopPlane → LoopPlane) (hφ : ContDiff ℝ 1 φ)
    (T : Lp ℝ 2 (volume.restrict loopDiskSet) →L[ℝ] Lp ℝ 2 (volume.restrict K))
    (hT : ∀ u, T u =ᵐ[volume.restrict K] fun z => u (φ z)) :
    ∃ D : Fin 2 → (Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)) →L[ℝ]
        Lp ℝ 2 (volume.restrict K),
      ∀ i d, D i d =ᵐ[volume.restrict K] fun z =>
        ∑ j : Fin 2, (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d j (φ z) := by
  let a (i j : Fin 2) (z : LoopPlane) :=
    (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j
  have ha (i j : Fin 2) : Continuous (a i j) :=
    (EuclideanSpace.proj j).continuous.comp
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hex (i j : Fin 2) : ∃ C : ℝ, ∀ z ∈ K, ‖a i j z‖ ≤ C :=
    hK.exists_bound_of_continuousOn (ha i j).continuousOn
  choose C hC using hex
  let A (i j : Fin 2) (z : LoopPlane) := a i j z • ContinuousLinearMap.id ℝ ℝ
  have hA (i j : Fin 2) : AEStronglyMeasurable (A i j) (volume.restrict K) :=
    ((ha i j).smul continuous_const).aestronglyMeasurable
  have hb (i j : Fin 2) : ∀ᵐ z ∂volume.restrict K, ‖A i j z‖ ≤ C i j := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    simpa only [A, norm_smul, ContinuousLinearMap.norm_id, mul_one] using hC i j z hz
  let L (i j : Fin 2) := Lp.coefficientL2 (A i j) (hA i j) (C i j) (hb i j)
  let D (i : Fin 2) : (Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)) →L[ℝ]
      Lp ℝ 2 (volume.restrict K) :=
    ((L i 0).comp T).comp (ContinuousLinearMap.proj 0) +
      ((L i 1).comp T).comp (ContinuousLinearMap.proj 1)
  refine ⟨D, ?_⟩
  intro i d
  filter_upwards [Lp.coeFn_add (L i 0 (T (d 0))) (L i 1 (T (d 1))),
    Lp.coefficientL2_ae (A i 0) (hA i 0) (C i 0) (hb i 0) (T (d 0)),
    Lp.coefficientL2_ae (A i 1) (hA i 1) (C i 1) (hb i 1) (T (d 1)),
    hT (d 0), hT (d 1)] with z hz h0 h1 ht0 ht1
  change (L i 0 (T (d 0)) + L i 1 (T (d 1)) : Lp ℝ 2 _) z = _
  rw [hz]
  change L i 0 (T (d 0)) z + L i 1 (T (d 1)) z = _
  rw [h0, h1]
  simp only [A, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, ht0, ht1, Fin.sum_univ_two, a]

private theorem smooth_chain (f : LoopPlane → ℝ) (hf : ContDiff ℝ 1 f)
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

theorem boundary_smooth_graph_uniform :
    ∃ R : ℝ, 0 < R ∧ ∀ (p : ℂ), ‖p‖ = 1 →
      ∀ (u : Lp ℝ 2 (volume.restrict loopDiskSet))
        (d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
        (b : Lp ℝ 2 m65CircleBoundaryMeasure),
      M65DiskWeakTrace u d (m65CircleBoundaryPullback b) →
      let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      ∃ (f : ℕ → LoopPlane → ℝ)
        (A : ℕ → Lp ℝ 2 (volume.restrict K))
        (B : ℕ → Fin 2 → Lp ℝ 2 (volume.restrict K))
        (C : ℕ → Lp ℝ 2 m65CircleBoundaryMeasure)
        (U : Lp ℝ 2 (volume.restrict K))
        (D : Fin 2 → Lp ℝ 2 (volume.restrict K)),
        (∀ n, ContDiff ℝ ∞ (f n)) ∧
        (∀ n, A n =ᵐ[volume.restrict K] fun z => f n (P z)) ∧
        (∀ n i, B n i =ᵐ[volume.restrict K]
          fun z => fderiv ℝ (f n ∘ P) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) ∧
        (∀ n, C n =ᵐ[m65CircleBoundaryMeasure] f n) ∧
        U =ᵐ[volume.restrict K] (fun z => u (P z)) ∧
        (∀ i, D i =ᵐ[volume.restrict K] fun z =>
          ∑ j : Fin 2, (fderiv ℝ P z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d j (P z)) ∧
        Tendsto A atTop (𝓝 U) ∧ (∀ i, Tendsto (fun n => B n i) atTop (𝓝 (D i))) ∧
        Tendsto C atTop (𝓝 b) := by
  obtain ⟨R, hR, hgeometry⟩ := exists_uniform_boundary_halfDisk_pullback
  refine ⟨R, hR, ?_⟩
  intro p hp u d b htrace
  obtain ⟨_hleft, _hcap, _hreg, C, hC, hdom⟩ := hgeometry p hp
  let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  let P := diskBoundaryCoordinate p
  have hP := contDiff_diskBoundaryCoordinate p
  let T : Lp ℝ 2 (volume.restrict loopDiskSet) →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
    ChartLpNative.dominatedPullbackL2 P hP.continuous.measurable.aemeasurable hC hdom
  have hT (v : Lp ℝ 2 (volume.restrict loopDiskSet)) :
      T v =ᵐ[volume.restrict K] fun z => v (P z) :=
    ChartLpNative.dominatedPullbackL2_coe _ _ _ _ v
  have hpull {f g : LoopPlane → ℝ} (hfg : f =ᵐ[volume.restrict loopDiskSet] g) :
      (fun z => f (P z)) =ᵐ[volume.restrict K] fun z => g (P z) :=
    ae_of_ae_map hP.continuous.measurable.aemeasurable
      (ae_mono hdom (Measure.ae_smul_measure hfg C))
  obtain ⟨Q, hQ⟩ := compact_chain_operator K hK P (hP.of_le (by simp)) T hT
  obtain ⟨f, A, B, Cseq, hf, hA, hB, hBnd, hAlim, hBlim, hClim⟩ :=
    m65WeakTrace_exists_smooth_boundary_graph htrace
  refine ⟨f, fun n => T (A n), fun n i => Q i (B n), Cseq,
    T u, fun i => Q i d, hf, ?_, ?_, hBnd, hT u, fun i => hQ i d,
      (T.continuous.tendsto u).comp hAlim, ?_, hClim⟩
  · intro n
    exact (hT (A n)).trans (hpull (hA n))
  · intro n i
    filter_upwards [hQ i (B n), hpull (hB n 0), hpull (hB n 1)] with z hz h0 h1
    rw [hz, smooth_chain (f n) ((hf n).of_le (by simp)) P (hP.of_le (by simp)) z i]
    simp only [Fin.sum_univ_two, h0, h1]
  · intro i
    exact ((Q i).continuous.tendsto d).comp (tendsto_pi_nhds.mpr hBlim)

theorem boundary_smooth_graph {p : ℂ} (hp : ‖p‖ = 1)
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 m65CircleBoundaryMeasure}
    (htrace : M65DiskWeakTrace u d (m65CircleBoundaryPullback b)) :
    ∃ R : ℝ, 0 < R ∧
      let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      ∃ (f : ℕ → LoopPlane → ℝ)
        (A : ℕ → Lp ℝ 2 (volume.restrict K))
        (B : ℕ → Fin 2 → Lp ℝ 2 (volume.restrict K))
        (C : ℕ → Lp ℝ 2 m65CircleBoundaryMeasure)
        (U : Lp ℝ 2 (volume.restrict K))
        (D : Fin 2 → Lp ℝ 2 (volume.restrict K)),
        (∀ n, ContDiff ℝ ∞ (f n)) ∧
        (∀ n, A n =ᵐ[volume.restrict K] fun z => f n (P z)) ∧
        (∀ n i, B n i =ᵐ[volume.restrict K]
          fun z => fderiv ℝ (f n ∘ P) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) ∧
        (∀ n, C n =ᵐ[m65CircleBoundaryMeasure] f n) ∧
        U =ᵐ[volume.restrict K] (fun z => u (P z)) ∧
        (∀ i, D i =ᵐ[volume.restrict K] fun z =>
          ∑ j : Fin 2, (fderiv ℝ P z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d j (P z)) ∧
        Tendsto A atTop (𝓝 U) ∧ (∀ i, Tendsto (fun n => B n i) atTop (𝓝 (D i))) ∧
        Tendsto C atTop (𝓝 b) := by
  obtain ⟨R, hR, hgraph⟩ := boundary_smooth_graph_uniform
  exact ⟨R, hR, hgraph p hp u d b htrace⟩

end PoincareConjecture.M65Boundary
