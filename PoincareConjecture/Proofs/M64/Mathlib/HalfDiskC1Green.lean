import PoincareConjecture.Proofs.M64.Mathlib.C1SchwartzApproximation
import PoincareConjecture.Proofs.M64.Mathlib.CompactUniformPairing
import PoincareConjecture.Proofs.M64.Mathlib.HalfDiskStrongGraph

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture

open Proofs.M58

local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ

theorem m64HalfDisk_green_contDiff {r : ℝ} (hr : 0 < r)
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b v : ℝ → ℝ)
    (hu : IntegrableOn u (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}))
    (hV : ∀ i, IntegrableOn (V i) (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}))
    (hb : IntegrableOn b (Icc (-r) r)) (hv : IntegrableOn v (Icc (0 : ℝ) Real.pi))
    (hgreen : ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        V i z * test z + u z * fderiv ℝ test z (basis i)) =
        r * (∫ theta in (0 : ℝ)..Real.pi,
          v theta * test (r • angularPoint theta) * angularPoint theta i) -
        (basis 1) i * ∫ s in (-r)..r, b s * test (s • basis 0))
    (test : LoopPlane → ℝ) (htest : ContDiff ℝ 1 test) (i : Fin 2) :
    (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
      V i z * test z + u z * fderiv ℝ test z (basis i)) =
      r * (∫ theta in (0 : ℝ)..Real.pi,
        v theta * test (r • angularPoint theta) * angularPoint theta i) -
      (basis 1) i * ∫ s in (-r)..r, b s * test (s • basis 0) := by
  let K := closedBall (0 : LoopPlane) r
  let L := K ∩ {z | 0 ≤ z 1}
  have hK : IsCompact K := isCompact_closedBall _ _
  have hL : IsCompact L := hK.inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have happrox (j : ℕ) := m64C1_schwartz_approximation hK htest
    (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j)
  choose g hg using happrox
  have hmem : ∀ᵐ z ∂volume.restrict L, z ∈ K :=
    (ae_restrict_mem hL.measurableSet).mono fun _ h => h.1
  have htestD : Continuous (fun z => fderiv ℝ test z (basis i)) :=
    (htest.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgD (j : ℕ) : Continuous (fun z => fderiv ℝ (g j) z (basis i)) :=
    ((g j).smooth 1).continuous_fderiv one_ne_zero |>.clm_apply continuous_const
  have hcloseD (j : ℕ) (z : LoopPlane) (hz : z ∈ K) :
      dist (fderiv ℝ (g j) z (basis i)) (fderiv ℝ test z (basis i)) ≤ (1 / 2 : ℝ) ^ j := by
    rw [dist_eq_norm]
    calc
      _ = ‖(fderiv ℝ (g j) z - fderiv ℝ test z) (basis i)‖ := rfl
      _ ≤ ‖fderiv ℝ (g j) z - fderiv ℝ test z‖ * ‖basis i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 / 2 : ℝ) ^ j := by
        simpa only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one, mul_one,
          ← dist_eq_norm] using (hg j z hz).2.le
  have hval := m64CompactUniform_integral_pairing_tendsto hK measurable_id hmem
    (hV i) (fun j => (g j).continuous) htest.continuous (fun j z hz => (hg j z hz).1.le)
  have hder := m64CompactUniform_integral_pairing_tendsto hK measurable_id hmem
    hu hgD htestD hcloseD
  have hleft_eq (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) :
      (∫ z in L, phi z * V i z) + (∫ z in L, fderiv ℝ phi z (basis i) * u z) =
      ∫ z in L, V i z * phi z + u z * fderiv ℝ phi z (basis i) := by
    have hc := (hphi.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous (fun _ : LoopPlane => basis i))
    rw [← integral_add ((hV i).continuousOn_mul hphi.continuous.continuousOn hL)
      (hu.continuousOn_mul hc.continuousOn hL)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by ring
  have hleft := hval.add hder
  change Tendsto (fun j => (∫ z in L, g j z * V i z) +
    ∫ z in L, fderiv ℝ (g j) z (basis i) * u z) atTop
      (𝓝 ((∫ z in L, test z * V i z) +
        ∫ z in L, fderiv ℝ test z (basis i) * u z)) at hleft
  simp only [hleft_eq test htest, hleft_eq _ ((g _).smooth 1)] at hleft
  let q := fun theta => r • angularPoint theta
  have hqc : Continuous q :=
    (continuous_const : Continuous (fun _ : ℝ => r)).smul contDiff_angularPoint.continuous
  have hqK : ∀ᵐ theta ∂volume.restrict (Icc (0 : ℝ) Real.pi), q theta ∈ K :=
    Eventually.of_forall fun theta => by
      simp [K, q, norm_smul, norm_angularPoint, abs_of_pos hr]
  have hweight : IntegrableOn (fun theta => v theta * angularPoint theta i)
      (Icc (0 : ℝ) Real.pi) := hv.mul_continuousOn
    (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      contDiff_angularPoint.continuous).continuousOn) isCompact_Icc
  have harc := m64CompactUniform_integral_pairing_tendsto hK hqc.measurable hqK
    hweight (fun j => (g j).continuous) htest.continuous (fun j z hz => (hg j z hz).1.le)
  have harc_eq (phi : LoopPlane → ℝ) :
      (∫ theta in Icc (0 : ℝ) Real.pi, phi (q theta) * (v theta * angularPoint theta i)) =
      ∫ theta in (0 : ℝ)..Real.pi,
        v theta * phi (r • angularPoint theta) * angularPoint theta i := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    exact Eventually.of_forall fun theta => by dsimp only [q]; ring
  change Tendsto (fun j => ∫ theta in Icc (0 : ℝ) Real.pi,
    g j (q theta) * (v theta * angularPoint theta i)) atTop
      (𝓝 (∫ theta in Icc (0 : ℝ) Real.pi,
        test (q theta) * (v theta * angularPoint theta i))) at harc
  simp only [harc_eq] at harc
  let l := fun s : ℝ => s • basis 0
  have hlc : Continuous l := continuous_id.smul continuous_const
  have hlK : ∀ᵐ s ∂volume.restrict (Icc (-r) r), l s ∈ K := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa only [K, l, mem_closedBall_zero_iff, norm_smul, EuclideanSpace.basisFun_apply,
      PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] using abs_le.mpr hs
  have hdiam := m64CompactUniform_integral_pairing_tendsto hK hlc.measurable hlK
    hb (fun j => (g j).continuous) htest.continuous (fun j z hz => (hg j z hz).1.le)
  have hdiam_eq (phi : LoopPlane → ℝ) :
      (∫ s in Icc (-r) r, phi (l s) * b s) =
      ∫ s in (-r)..r, b s * phi (s • basis 0) := by
    rw [intervalIntegral.integral_of_le (by linarith : -r ≤ r), ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae (Eventually.of_forall fun s => mul_comm _ _)
  change Tendsto (fun j => ∫ s in Icc (-r) r, g j (l s) * b s) atTop
    (𝓝 (∫ s in Icc (-r) r, test (l s) * b s)) at hdiam
  simp only [hdiam_eq] at hdiam
  have hright := (harc.const_mul r).sub (hdiam.const_mul ((basis 1) i))
  exact tendsto_nhds_unique hleft (hright.congr fun j => (hgreen (g j) i).symm)

end PoincareConjecture
