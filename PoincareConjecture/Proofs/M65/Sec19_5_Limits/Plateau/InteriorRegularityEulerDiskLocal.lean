import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerClass
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerLocalization
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEulerFields
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCutoff












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap LineDeriv

universe u

namespace PoincareConjecture.M65WeakDisk




def localMap {M : Type u} {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
    {γ : LoopCircle → M} (F : M65WeakDisk e γ) :
    M65LocalWeakMap e (ball (0 : LoopPlane) 1) where
  value := F.value
  derivative i z := F.derivative i z
  value_memLp K _hK hKU :=
    ((Lp.memLp F.embeddedValue).ae_eq F.embeddedValue_ae).mono_measure
      (Measure.restrict_mono_set volume (hKU.trans ball_subset_closedBall))
  derivative_memLp i K _hK hKU := (Lp.memLp (F.derivative i)).mono_measure
    (Measure.restrict_mono_set volume (hKU.trans ball_subset_closedBall))
  weak_derivative test _hc hs i j := by
    let b := EuclideanSpace.basisFun (Fin 2) ℝ i
    have hw := m65WeakTrace_interior_integral (F.weak_trace j) test hs i
    have hleft : (∫ z in loopDiskSet, m65DiskCoordinateL2 (F.derivative i) j z * test z) =
        ∫ z in loopDiskSet, test z * F.derivative i z j := by
      apply integral_congr_ae
      filter_upwards [m65DiskCoordinateL2_coe (F.derivative i) j] with z hz
      rw [hz, mul_comm]
    have hright : (∫ z in loopDiskSet, m65DiskCoordinateL2 F.embeddedValue j z *
        fderiv ℝ test z b) = ∫ z in loopDiskSet, fderiv ℝ test z b * e (F.value z) j := by
      apply integral_congr_ae
      filter_upwards [m65DiskCoordinateL2_coe F.embeddedValue j, F.embeddedValue_ae]
        with z hz hv
      rw [hz, hv, mul_comm]
    change (∫ z in loopDiskSet, m65DiskCoordinateL2 (F.derivative i) j z * test z) =
      -(∫ z in loopDiskSet, m65DiskCoordinateL2 F.embeddedValue j z * fderiv ℝ test z b) at hw
    rw [hleft, hright] at hw
    have hL (S : Set LoopPlane) (hS : tsupport test ⊆ S) :
        (∫ z in S, test z * F.derivative i z j) = ∫ z, test z * F.derivative i z j :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (hS hm)), zero_mul])
    have hV (S : Set LoopPlane) (hS : tsupport test ⊆ S) :
        (∫ z in S, fderiv ℝ test z b * e (F.value z) j) =
          ∫ z, fderiv ℝ test z b * e (F.value z) j :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [fderiv_of_notMem_tsupport ℝ (fun hm => hz (hS hm)), zero_apply, zero_mul])
    rw [hL loopDiskSet (hs.trans ball_subset_closedBall),
      hV loopDiskSet (hs.trans ball_subset_closedBall)] at hw
    rw [hL _ hs, hV _ hs]
    exact hw

end PoincareConjecture.M65WeakDisk

namespace PoincareConjecture.M65Euler

set_option maxHeartbeats 1200000 in





theorem compact_disk_green_difference {M : Type u} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (hU : IsOpen U) (F G : M65LocalWeakMap e U)
    (x : LoopPlane) {R : ℝ} (hR : 0 ≤ R) (hRU : closedBall x R ⊆ U)
    (hmatch : G.value =ᵐ[volume.restrict (U \ closedBall x R)] F.value)
    (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N) :
    (∫ z in closedBall x R, (G.derivative i z j - F.derivative i z j) * test z +
      (e (G.value z) j - e (F.value z) j) *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
  let Z := closedBall x R
  let b := EuclideanSpace.basisFun (Fin 2) ℝ i
  have houtside : IsOpen (U \ Z) := hU.sdiff isClosed_closedBall
  have hfields : G.derivative i =ᵐ[volume.restrict (U \ Z)] F.derivative i := by
    apply derivative_unique houtside (restrict_map G sdiff_subset) (restrict_map F sdiff_subset)
    filter_upwards [hmatch] with z hz
    exact congrArg e hz
  obtain ⟨θ, hc, hs, hθ⟩ := M65Interior.exists_disk_cutoff hU x hR hRU
  let p := SchwartzMap.smulLeftCLM ℝ θ test
  have hp : (p : LoopPlane → ℝ) = fun z => θ z * test z :=
    SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth test
  have hps : tsupport p ⊆ tsupport θ :=
    (SchwartzMap.tsupport_smulLeftCLM_subset θ test).trans inter_subset_right
  have hpc : HasCompactSupport p := hc.of_isClosed_subset isClosed_closure hps
  have hpU := hps.trans hs
  have hpd (z : LoopPlane) : fderiv ℝ p z b =
      θ z * fderiv ℝ test z b + fderiv ℝ θ z b * test z := by
    rw [hp, fderiv_fun_mul θ.differentiableAt test.differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  let diff (φ : 𝓢(LoopPlane, ℝ)) (z : LoopPlane) :=
    (G.derivative i z j - F.derivative i z j) * φ z +
      (e (G.value z) j - e (F.value z) j) * fderiv ℝ φ z b
  have hzero : (∫ z in U, diff p z) = 0 := by
    have hDG := G.test_derivative_integrable p hpc hpU i j
    have hDF := F.test_derivative_integrable p hpc hpU i j
    have hVG := G.test_value_integrable p hpc hpU i j
    have hVF := F.test_value_integrable p hpc hpU i j
    have heq : diff p = fun z =>
        (p z * G.derivative i z j - p z * F.derivative i z j) +
          (fderiv ℝ p z b * e (G.value z) j - fderiv ℝ p z b * e (F.value z) j) := by
      funext z
      dsimp only [diff]
      ring
    dsimp only [b] at heq ⊢
    have hsum := integral_add (hDG.sub hDF) (hVG.sub hVF)
    simp only [Pi.sub_apply] at hsum
    rw [heq, hsum, integral_sub hDG hDF,
      integral_sub hVG hVF, G.weak_derivative p hpc hpU i j,
      F.weak_derivative p hpc hpU i j]
    ring
  have hdiff0 : diff p =ᵐ[volume.restrict (U \ Z)] 0 := by
    filter_upwards [hfields, hmatch] with z hd hv
    simp only [diff, hd, hv, sub_self, zero_mul, add_zero, Pi.zero_apply]
  have hint : (∫ z in Z, diff p z) = ∫ z in U, diff p z :=
    (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hU.measurableSet.nullMeasurableSet hRU
      ((ae_restrict_iff' houtside.measurableSet).mp hdiff0)).symm
  calc
    _ = ∫ z in Z, diff p z := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro z hz
      dsimp only [diff]
      rw [hpd, congrFun hp z, (hθ z hz).2.1, (hθ z hz).2.2]
      simp only [one_mul, zero_apply, zero_mul, add_zero]
      rfl
    _ = 0 := hint.trans hzero

end PoincareConjecture.M65Euler
