import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityWeakMap
import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ContDiff

universe u

namespace PoincareConjecture.M65LocalWeakMap

private theorem test_mul_memLp (θ : 𝓢(LoopPlane, ℝ)) {f : LoopPlane → ℝ}
    {K : Set LoopPlane} (hf : MemLp f 2 (volume.restrict K)) :
    MemLp (fun z => θ z * f z) 2 (volume.restrict K) := by
  apply hf.of_le_mul (c := SchwartzMap.seminorm ℝ 0 0 θ)
    (θ.continuous.aestronglyMeasurable.mul hf.1)
  exact ae_of_all _ (fun z => by
    change ‖θ z * f z‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (θ.norm_le_seminorm ℝ z) (norm_nonneg _))

theorem cutoff_global {M : Type u} {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
    {U : Set LoopPlane} (F : M65LocalWeakMap e U) (j : Fin N)
    (θ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ U) :
    ∃ (u : Lp ℝ 2 (volume : Measure LoopPlane))
      (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane)),
      (u =ᵐ[volume] fun z => θ z * e (F.value z) j) ∧
      (∀ i, d i =ᵐ[volume] fun z => θ z * F.derivative i z j +
        fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (F.value z) j) ∧
      ∀ i (φ : 𝓢(LoopPlane, ℝ)),
        ⟪d i, φ.toLp 2 volume⟫_ℝ =
          -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  let K := tsupport θ
  let W := fun z => θ z * e (F.value z) j
  let G := fun i z => θ z * F.derivative i z j +
    fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (F.value z) j
  have hK : MeasurableSet K := isClosed_closure.measurableSet
  have hW : MemLp W 2 (volume.restrict K) :=
    test_mul_memLp θ ((F.value_memLp K hc hs).eval_piLp j)
  have hG (i : Fin 2) : MemLp (G i) 2 (volume.restrict K) :=
    (test_mul_memLp θ ((F.derivative_memLp i K hc hs).eval_piLp j)).add
      (test_mul_memLp (∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} θ)
        ((F.value_memLp K hc hs).eval_piLp j))
  have hWzero (z : LoopPlane) (hz : z ∉ K) : W z = 0 := by
    dsimp only [W]
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hGzero (i : Fin 2) (z : LoopPlane) (hz : z ∉ K) : G i z = 0 := by
    dsimp only [G]
    rw [image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz]
    simp only [zero_mul, zero_apply, add_zero]
  have hglobal {f : LoopPlane → ℝ} (hf : MemLp f 2 (volume.restrict K))
      (hz : ∀ z, z ∉ K → f z = 0) : MemLp f 2 volume := by
    have hi := (memLp_indicator_iff_restrict hK).mpr hf
    have heq : K.indicator f = f := by
      funext z
      by_cases hzk : z ∈ K
      · rw [indicator_of_mem hzk]
      · rw [indicator_of_notMem hzk, hz z hzk]
    simpa only [heq] using hi
  have hWG := hglobal hW hWzero
  have hGG (i : Fin 2) := hglobal (hG i) (hGzero i)
  let u := hWG.toLp W
  let d (i : Fin 2) := (hGG i).toLp (G i)
  refine ⟨u, d, hWG.coeFn_toLp, fun i => (hGG i).coeFn_toLp, ?_⟩
  intro i φ
  let b := EuclideanSpace.basisFun (Fin 2) ℝ i
  let p := SchwartzMap.smulLeftCLM ℝ θ φ
  have hp : (p : LoopPlane → ℝ) = fun z => θ z * φ z :=
    SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth φ
  have hpK : tsupport p ⊆ K :=
    (SchwartzMap.tsupport_smulLeftCLM_subset θ φ).trans inter_subset_right
  have hpc : HasCompactSupport p := hc.of_isClosed_subset isClosed_closure hpK
  have hpU : tsupport p ⊆ U := hpK.trans hs
  have hpD (z : LoopPlane) : fderiv ℝ p z b =
      θ z * fderiv ℝ φ z b + fderiv ℝ θ z b * φ z := by
    rw [hp]
    change fderiv ℝ ((θ : LoopPlane → ℝ) * (φ : LoopPlane → ℝ)) z b = _
    rw [fderiv_mul θ.differentiableAt φ.differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hsum : (∫ z in U, G i z * φ z) + (∫ z in U, W z * fderiv ℝ φ z b) =
      (∫ z in U, p z * F.derivative i z j) +
        (∫ z in U, fderiv ℝ p z b * e (F.value z) j) := by
    have hl := integral_add (μ := volume.restrict U)
      ((hGG i).integrable_mul (φ.memLp 2 volume)).integrableOn
      (hWG.integrable_mul ((∂_{b} φ).memLp 2 volume)).integrableOn
    have hr := integral_add (F.test_derivative_integrable p hpc hpU i j)
      (F.test_value_integrable p hpc hpU i j)
    simp only [Pi.mul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] at hl
    rw [← hl, ← hr]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      change G i z * φ z + W z * fderiv ℝ φ z b =
        p z * F.derivative i z j + fderiv ℝ p z b * e (F.value z) j
      rw [hpD, hp]
      dsimp only [W, G, b]
      ring)
  have hweak := F.weak_derivative p hpc hpU i j
  have hzero : (∫ z in U, G i z * φ z) = -(∫ z in U, W z * fderiv ℝ φ z b) := by
    linarith only [hsum, hweak]
  have hleft : (∫ z in U, G i z * φ z) = ∫ z, G i z * φ z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [hGzero i z (fun hk => hz (hs hk)), zero_mul])
  have hright : (∫ z in U, W z * fderiv ℝ φ z b) = ∫ z, W z * fderiv ℝ φ z b :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [hWzero z (fun hk => hz (hs hk)), zero_mul])
  rw [hleft, hright] at hzero
  rw [DeTurckDomainRegularityNative.inner_schwartz]
  have hdEq : (∫ z, d i z * φ z) = ∫ z, G i z * φ z :=
    integral_congr_ae (by
      filter_upwards [(hGG i).coeFn_toLp] with z hz
      rw [hz])
  have huEq : (∫ z, u z * fderiv ℝ φ z b) = ∫ z, W z * fderiv ℝ φ z b :=
    integral_congr_ae (by
      filter_upwards [hWG.coeFn_toLp] with z hz
      rw [hz])
  rw [hdEq, huEq]
  exact hzero

end PoincareConjecture.M65LocalWeakMap
