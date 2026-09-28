import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformalBeltrami
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformal
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Complex Metric
open scoped Topology Manifold ContDiff InnerProductSpace

universe u v

namespace PoincareConjecture

private theorem m65Beltrami_scalar_deriv (E P q t : ℝ) (hd : 1 - t ^ 2 * q ≠ 0) :
    HasDerivAt (fun s : ℝ => ((1 + s ^ 2 * q) * E - s * P) / (1 - s ^ 2 * q))
      ((4 * t * q * E - (1 + t ^ 2 * q) * P) / (1 - t ^ 2 * q) ^ 2) t := by
  have hsq := ((hasDerivAt_id t).pow 2).mul_const q
  convert! ((((hasDerivAt_const t 1).add hsq).mul_const E).sub
    ((hasDerivAt_id t).mul_const P)).div ((hasDerivAt_const t 1).sub hsq) hd using 1
  dsimp
  ring

private theorem m65Beltrami_derivative_bound (E P q t C : ℝ)
    (hq : 0 ≤ q) (hC : q ≤ C) (ht : |t| < 1) (htq : t ^ 2 * q < 1 / 2) :
    ‖(4 * t * q * E - (1 + t ^ 2 * q) * P) / (1 - t ^ 2 * q) ^ 2‖ ≤
      16 * C * ‖E‖ + 8 * ‖P‖ := by
  have hC0 := hq.trans hC
  have hqt : 0 ≤ t ^ 2 * q := mul_nonneg (sq_nonneg t) hq
  have hd : 0 < 1 - t ^ 2 * q := by linarith
  have hdsq : 0 < (1 - t ^ 2 * q) ^ 2 := sq_pos_of_pos hd
  have hlo : (1 / 4 : ℝ) ≤ (1 - t ^ 2 * q) ^ 2 := by nlinarith
  have hfirst : ‖4 * t * q * E‖ ≤ 4 * C * ‖E‖ := by
    simp only [norm_mul, Real.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg hq]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg E)
    nlinarith [mul_le_mul_of_nonneg_right ht.le hq]
  have hsecond : ‖(1 + t ^ 2 * q) * P‖ ≤ 2 * ‖P‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + t ^ 2 * q)]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg P)
  have hnum := (norm_sub_le (4 * t * q * E) ((1 + t ^ 2 * q) * P)).trans
    (add_le_add hfirst hsecond)
  rw [norm_div, Real.norm_of_nonneg (sq_nonneg _)]
  apply (div_le_iff₀ hdsq).mpr
  have hb : 0 ≤ 16 * C * ‖E‖ + 8 * ‖P‖ := by positivity
  have hh := mul_le_mul_of_nonneg_left hlo hb
  nlinarith only [hnum, hh]

private theorem m65Beltrami_integral_derivative {X : Type v} [MeasurableSpace X]
    (mu : Measure X) (E P q : X → ℝ) (hE : Integrable E mu) (hP : Integrable P mu)
    (hq : AEStronglyMeasurable q mu) {C : ℝ} (hbound : ∀ z, 0 ≤ q z ∧ q z ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ z,
      ((1 + t ^ 2 * q z) * E z - t * P z) / (1 - t ^ 2 * q z) ∂mu)
      (-(∫ z, P z ∂mu)) 0 := by
  let S : Set ℝ := {t | |t| < 1 ∧ t ^ 2 * C < 1 / 2}
  have hS : S ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt continuous_abs continuous_const).inter
        (isOpen_lt ((continuous_id.pow 2).mul continuous_const) continuous_const)
    · norm_num [S]
  let V := fun t z => ((1 + t ^ 2 * q z) * E z - t * P z) / (1 - t ^ 2 * q z)
  let W := fun t z => (4 * t * q z * E z - (1 + t ^ 2 * q z) * P z) /
    (1 - t ^ 2 * q z) ^ 2
  have hsmall (t : ℝ) (ht : t ∈ S) (z : X) : t ^ 2 * q z < 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hbound z).2 (sq_nonneg t)).trans_lt ht.2
  have hmeas (t : ℝ) : AEStronglyMeasurable (V t) mu :=
    (((aestronglyMeasurable_const.add (hq.const_mul _)).mul hE.1).sub
      (hP.1.const_mul t)).div₀ (aestronglyMeasurable_const.sub (hq.const_mul _))
  have hV0 : V 0 = E := by funext z; simp [V]
  have hW0 : W 0 = fun z => -P z := by funext z; simp [W]
  obtain ⟨_hint, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := V) (F' := W) (bound := fun z => 16 * C * ‖E z‖ + 8 * ‖P z‖) hS
    (Eventually.of_forall hmeas) (hV0 ▸ hE) (hW0 ▸ hP.1.neg)
    (ae_of_all _ fun z t ht => m65Beltrami_derivative_bound _ _ _ _ _
      (hbound z).1 (hbound z).2 ht.1 (hsmall t ht z))
    ((hE.norm.const_mul (16 * C)).add (hP.norm.const_mul 8))
    (ae_of_all _ fun z t ht => m65Beltrami_scalar_deriv _ _ _ _
      (by linarith [hsmall t ht z]))
  simpa only [hW0, integral_neg] using hderiv

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
  {gamma : LoopCircle → M}

private theorem m65Hopf_pair_integrable (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (F : M65WeakDisk e gamma) (i j : Fin 2) :
    Integrable (fun z => m65EmbeddingMetric g e (F.value z)
      (F.derivative i z) (F.derivative j z)) (volume.restrict loopDiskSet) := by
  let V := EuclideanSpace ℝ (Fin N)
  let mu := volume.restrict loopDiskSet
  let : TopologicalSpace.PseudoMetrizableSpace M := hemb.toIsInducing.pseudoMetrizableSpace
  let J : StrongDual ℝ V →L[ℝ] V :=
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let A (p : M) : V →L[ℝ] V := J.comp (m65EmbeddingMetric g e p)
  have hA : Continuous A :=
    continuous_const.clm_comp (m65EmbeddingMetric_contMDiff g e he hinj).continuous
  have hAinner (p : M) (v w : V) : ⟪A p v, w⟫_ℝ = m65EmbeddingMetric g e p v w :=
    InnerProductSpace.toDual_symm_apply
  obtain ⟨C, hC⟩ := compact.exists_bound_of_continuousOn hA.continuousOn
  have hmeas : AEStronglyMeasurable (fun z => A (F.value z)) mu :=
    hA.comp_aestronglyMeasurable (hemb.aestronglyMeasurable_comp_iff.mp
      ((Lp.memLp F.embeddedValue).1.congr F.embeddedValue_ae))
  let T := Lp.coefficientL2 (fun z => A (F.value z)) hmeas C
    (ae_of_all _ fun z => hC _ (mem_univ _))
  apply (L2.integrable_inner (𝕜 := ℝ) (T (F.derivative i)) (F.derivative j)).congr
  filter_upwards [Lp.coefficientL2_ae _ hmeas C
    (ae_of_all _ fun z => hC _ (mem_univ _)) (F.derivative i)] with z hz
  change ⟪T (F.derivative i) z, F.derivative j z⟫_ℝ = _
  rw [hz, hAinner]

set_option maxHeartbeats 1600000 in

theorem m65WeakDisk_hopf_test (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hgamma : Continuous gamma) (F : M65WeakDisk e gamma) (hmin : F.MinimizesEnergy g)
    (nu : LoopPlane → ℂ) (hnu : ContDiff ℝ ∞ nu) (hsupp : HasCompactSupport nu)
    (hinside : tsupport nu ⊆ ball (0 : LoopPlane) 1 \ {0}) :
    (∫ z in loopDiskSet,
      (nu z).re * (m65EmbeddingMetric g e (F.value z) (F.derivative 0 z) (F.derivative 0 z) -
        m65EmbeddingMetric g e (F.value z) (F.derivative 1 z) (F.derivative 1 z)) +
      2 * (nu z).im * m65EmbeddingMetric g e (F.value z)
        (F.derivative 0 z) (F.derivative 1 z)) = 0 := by
  let mu := volume.restrict loopDiskSet
  let a := fun z => m65EmbeddingMetric g e (F.value z) (F.derivative 0 z) (F.derivative 0 z)
  let b := fun z => m65EmbeddingMetric g e (F.value z) (F.derivative 0 z) (F.derivative 1 z)
  let c := fun z => m65EmbeddingMetric g e (F.value z) (F.derivative 1 z) (F.derivative 1 z)
  let E := fun z => (a z + c z) / 2
  let P := fun z => (nu z).re * (a z - c z) + 2 * (nu z).im * b z
  let q := fun z => ‖nu z‖ ^ 2
  have ha : Integrable a mu := m65Hopf_pair_integrable g he hinj hemb compact F 0 0
  have hb : Integrable b mu := m65Hopf_pair_integrable g he hinj hemb compact F 0 1
  have hc : Integrable c mu := m65Hopf_pair_integrable g he hinj hemb compact F 1 1
  have hE : Integrable E mu := (ha.add hc).div_const 2
  obtain ⟨C0, hC0⟩ := hsupp.exists_bound_of_continuous hnu.continuous
  let C := max C0 1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC (z : LoopPlane) : ‖nu z‖ ≤ C := (hC0 z).trans (le_max_left _ _)
  have hr (z : LoopPlane) : ‖(nu z).re‖ ≤ C := (Complex.abs_re_le_norm _).trans (hC z)
  have hi (z : LoopPlane) : ‖(nu z).im‖ ≤ C := (Complex.abs_im_le_norm _).trans (hC z)
  have hP : Integrable P mu := by
    have h1 := (ha.sub hc).bdd_mul
      (Complex.continuous_re.comp hnu.continuous).aestronglyMeasurable (ae_of_all _ hr)
    have h2 := hb.bdd_mul
      (Complex.continuous_im.comp hnu.continuous).aestronglyMeasurable (ae_of_all _ hi)
    convert! h1.add (h2.const_mul 2) using 1
    funext z
    dsimp only [P, Function.comp_apply, Pi.add_apply, Pi.sub_apply]
    ring
  have hq : AEStronglyMeasurable q mu := (hnu.continuous.norm.pow 2).aestronglyMeasurable
  have hqbound (z : LoopPlane) : 0 ≤ q z ∧ q z ≤ C ^ 2 :=
    ⟨sq_nonneg _, (sq_le_sq₀ (norm_nonneg _) hCpos.le).mpr (hC z)⟩
  let V := fun t : ℝ => ∫ z, ((1 + t ^ 2 * q z) * E z - t * P z) /
    (1 - t ^ 2 * q z) ∂mu
  have hderiv : HasDerivAt V (-(∫ z, P z ∂mu)) 0 :=
    m65Beltrami_integral_derivative mu E P q hE hP hq hqbound
  have hnuZero : ∀ᶠ z in 𝓝 (0 : LoopPlane), nu z = 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hz
    exact (hinside hz).2 (mem_singleton _)
  have hnuOut (z : LoopPlane) (hz : 1 ≤ ‖z‖) : nu z = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    have hn := mem_ball_zero_iff.mp (hinside hh).1
    exact hz.not_gt hn
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| * C < 1 := by
    exact (isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds
      (by norm_num)
  have hlocal : IsLocalMin V 0 := by
    filter_upwards [hnear] with t ht
    have hsub (z : LoopPlane) : ‖t • nu z‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hC z) (abs_nonneg t)).trans_lt ht
    obtain ⟨G, hG⟩ := m65WeakDisk_beltrami_change g he.continuous hgamma F
      (fun z => t • nu z) (hnu.const_smul t)
      (hnuZero.mono fun z hz => by simp only [hz, smul_zero])
      (fun z hz => by simp only [hnuOut z hz, smul_zero]) hsub
    have hG' : G.energy g = V t := by
      rw [hG]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        dsimp only [M65WeakDisk.beltramiEnergyDensity, E, P, q, a, b, c]
        simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
          smul_re, smul_im, smul_eq_mul]
        ring
    have hF : F.energy g = V 0 := by
      change (∫ z, m65EmbeddedEnergyDensity g e F.value
        (fun i z => F.derivative i z) z ∂mu) = _
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero,
          sub_zero, div_one]
        dsimp only [m65EmbeddedEnergyDensity, E, a, c]
        rw [Fin.sum_univ_two]
        ring
    rw [← hF, ← hG']
    exact hmin G
  have hz := hlocal.hasDerivAt_eq_zero hderiv
  exact neg_eq_zero.mp hz

theorem m65WeakDisk_conformal_of_minimum (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hgamma : Continuous gamma) (F : M65WeakDisk e gamma) (hmin : F.MinimizesEnergy g) :
    F.Conformal g := by
  let mu := volume.restrict loopDiskSet
  let U : Set LoopPlane := ball (0 : LoopPlane) 1 \ {0}
  let a := fun z => m65EmbeddingMetric g e (F.value z) (F.derivative 0 z) (F.derivative 0 z)
  let b := fun z => m65EmbeddingMetric g e (F.value z) (F.derivative 0 z) (F.derivative 1 z)
  let c := fun z => m65EmbeddingMetric g e (F.value z) (F.derivative 1 z) (F.derivative 1 z)
  have ha : Integrable a mu := m65Hopf_pair_integrable g he hinj hemb compact F 0 0
  have hb : Integrable b mu := m65Hopf_pair_integrable g he hinj hemb compact F 0 1
  have hc : Integrable c mu := m65Hopf_pair_integrable g he hinj hemb compact F 1 1
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have htest (k : ℂ) (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ ∞ phi)
      (hsupp : HasCompactSupport phi) (hin : tsupport phi ⊆ U) :
      (∫ z, phi z * (k.re * (a z - c z) + 2 * k.im * b z) ∂mu) = 0 := by
    have hts : tsupport (fun z => phi z • k) ⊆ tsupport phi :=
      tsupport_smul_subset_left phi (fun _ => k)
    have ht := m65WeakDisk_hopf_test g he hinj hemb compact hgamma F hmin
      (fun z => phi z • k) (hphi.smul contDiff_const) hsupp.smul_right (hts.trans hin)
    convert! ht using 1
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      dsimp only [a, b, c]
      simp only [smul_re, smul_im, smul_eq_mul]
      ring
  have hdiag : ∀ᵐ z ∂mu, z ∈ U → a z - c z = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((ha.sub hc).locallyIntegrable.locallyIntegrableOn U)
    intro phi hphi hsupp hin
    simpa only [one_re, one_im, one_mul, mul_zero, zero_mul, add_zero, smul_eq_mul, Pi.sub_apply]
      using htest 1 phi hphi hsupp hin
  have hmixed : ∀ᵐ z ∂mu, z ∈ U → 2 * b z = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hb.const_mul 2).locallyIntegrable.locallyIntegrableOn U)
    intro phi hphi hsupp hin
    simpa only [I_re, I_im, zero_mul, mul_one, zero_add, smul_eq_mul]
      using htest I phi hphi hsupp hin
  have hsphere : ∀ᵐ z ∂(volume : Measure LoopPlane), z ∉ sphere (0 : LoopPlane) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : LoopPlane) 1)
  have hcenter : ∀ᵐ z ∂mu, z ∉ ({0} : Set LoopPlane) :=
    (countable_singleton (0 : LoopPlane)).ae_notMem mu
  filter_upwards [hdiag, hmixed, hcenter, ae_restrict_of_ae hsphere,
    ae_restrict_mem measurableSet_closedBall] with z hdiag hmixed hcenter hsphere hz
  have hin : z ∈ U := by
    refine ⟨?_, hcenter⟩
    apply mem_ball_zero_iff.mpr
    have hle := mem_closedBall_zero_iff.mp hz
    have hne : ‖z‖ ≠ 1 := by
      intro hh
      apply hsphere
      simpa only [mem_sphere, dist_zero_right] using hh
    exact lt_of_le_of_ne hle hne
  change a z = c z ∧ b z = 0
  exact ⟨sub_eq_zero.mp (hdiag hin), by linarith [hmixed hin]⟩

theorem m65WeakDisk_conformal_of_normalized_minimum (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hgamma : Continuous gamma) (F : M65WeakDisk e gamma)
    {a b c : LoopCircle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmin : F.MinimizesNormalizedEnergy g a b c) : F.Conformal g :=
  m65WeakDisk_conformal_of_minimum g he hinj hemb compact hgamma F
    (F.normalized_minimum_is_minimum g he.continuous hgamma hab hac hbc hmin)

end PoincareConjecture
