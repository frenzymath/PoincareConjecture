import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Approximation
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamWeakExtension
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.LipschitzDerivatives

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness

theorem m64L2_pairing_tendsto_of_eLpNorm
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : ℕ → X → ℝ} {u v : X → ℝ}
    (hf : ∀ j, MemLp (f j) 2 mu) (hu : MemLp u 2 mu) (hv : MemLp v 2 mu)
    (hlim : Tendsto (fun j => eLpNorm (fun x => f j x - u x) 2 mu) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, v x * f j x ∂mu) atTop (𝓝 (∫ x, v x * u x ∂mu)) := by
  have hL := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hlim
  have h := ((testIntegral v hv).continuous.tendsto (hu.toLp u)).comp hL
  simpa only [Function.comp_def, testIntegral_toLp, smul_eq_mul] using h

theorem m64WeakPartial_compact_sobolev_test
    {u W psi : LoopPlane → ℝ} {i : Fin 2}
    (hu : MemLp u 2 volume) (hW : MemLp W 2 volume)
    (hw : HasWeakPartialDeriv i W u univ)
    (hpsi : MemW1pWitness 2 psi univ) (hc : HasCompactSupport psi) :
    (∫ p, u p * hpsi.weakGrad p i) = -(∫ p, W p * psi p) := by
  let hpsi' : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) psi univ := {
    memLp := by simpa only [ENNReal.ofReal_ofNat] using hpsi.memLp
    weakGrad := hpsi.weakGrad
    weakGrad_component_memLp := fun j => by
      simpa only [ENNReal.ofReal_ofNat] using hpsi.weakGrad_component_memLp j
    isWeakGrad := hpsi.isWeakGrad }
  obtain ⟨f, hf, hfc, -, hval, hder⟩ :=
    exists_smooth_compactSupport_W1p_approx_univ (p := (2 : ℝ)) (by norm_num)
      hpsi' hc
  have hfl (j : ℕ) : MemLp (f j) 2 volume :=
    (hf j).continuous.memLp_of_hasCompactSupport (hfc j)
  have hDl (j : ℕ) : MemLp (fun p => fderiv ℝ (f j) p (EuclideanSpace.single i 1)) 2 volume :=
    (((hf j).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hfc j).fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hpsil : MemLp psi 2 volume := by simpa only [Measure.restrict_univ] using hpsi.memLp
  have hgrad : MemLp (fun p => hpsi.weakGrad p i) 2 volume := by
    simpa only [Measure.restrict_univ] using hpsi.weakGrad_component_memLp i
  have hl := m64L2_pairing_tendsto_of_eLpNorm hDl hgrad hu
    (by simpa only [hpsi', ENNReal.ofReal_ofNat] using hder i)
  have hr := (m64L2_pairing_tendsto_of_eLpNorm hfl hpsil hW
    (by simpa only [ENNReal.ofReal_ofNat] using hval)).neg
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [] with j
  simpa only [Measure.restrict_univ] using (hw (f j) (hf j) (hfc j) (subset_univ _)).symm

theorem m64CompactLipschitz_fderiv_memLp
    {psi : LoopPlane → ℝ} {K : ℝ≥0}
    (hpsi : LipschitzWith K psi) (hc : HasCompactSupport psi) (j : Fin 2) :
    MemLp (fun p => fderiv ℝ psi p (EuclideanSpace.single j 1)) 2 volume := by
  classical
  let D := fun p => fderiv ℝ psi p (EuclideanSpace.single j 1)
  let : IsFiniteMeasure (volume.restrict (tsupport psi)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hc.measure_lt_top (μ := volume)⟩
  have ht : MemLp D ⊤ volume := by
    simpa only [Measure.restrict_univ] using
      memLp_top_fderiv_apply_of_lipschitzOn isOpen_univ hpsi.lipschitzOnWith
        (EuclideanSpace.single j 1)
  have hlocal : MemLp D 2 (volume.restrict (tsupport psi)) :=
    (ht.mono_measure Measure.restrict_le_self).mono_exponent le_top
  have heq : (tsupport psi).indicator D = D := by
    funext p
    by_cases hp : p ∈ tsupport psi
    · exact indicator_of_mem hp D
    · rw [indicator_of_notMem hp]
      change 0 = fderiv ℝ psi p (EuclideanSpace.single j 1)
      rw [fderiv_of_notMem_tsupport ℝ hp, zero_apply]
  change MemLp D 2 volume
  rw [← heq]
  exact (memLp_indicator_iff_restrict (isClosed_tsupport psi).measurableSet).mpr hlocal

theorem m64WeakPartial_compact_lipschitz_test
    {u W psi : LoopPlane → ℝ} {i : Fin 2} {K : ℝ≥0}
    (hu : MemLp u 2 volume) (hW : MemLp W 2 volume)
    (hw : HasWeakPartialDeriv i W u univ)
    (hpsi : LipschitzWith K psi) (hc : HasCompactSupport psi) :
    (∫ p, u p * fderiv ℝ psi p (EuclideanSpace.single i 1)) = -(∫ p, W p * psi p) := by
  let D := fun j p => fderiv ℝ psi p (EuclideanSpace.single j 1)
  have hD := m64CompactLipschitz_fderiv_memLp hpsi hc
  have hweak (j : Fin 2) : HasWeakPartialDeriv j (D j) psi univ := by
    apply m64WeakPartialDeriv_ae_congr EventuallyEq.rfl ?_
      (hasWeakPartialDeriv_lineDeriv_of_lipschitz hpsi j)
    rw [Measure.restrict_univ]
    filter_upwards [hpsi.ae_differentiableAt (μ := volume)] with p hp
    exact hp.lineDeriv_eq_fderiv
  let H : MemW1pWitness 2 psi univ := {
    memLp := by simpa only [Measure.restrict_univ] using
      hpsi.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc
    weakGrad := fun p => WithLp.toLp 2 (fun j => D j p)
    weakGrad_component_memLp := fun j => by simpa only [Measure.restrict_univ] using hD j
    isWeakGrad := hweak }
  exact m64WeakPartial_compact_sobolev_test hu hW hw H hc

theorem m64WeakColumns_compact_lipschitz_test
    {m : ℕ} {u W : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {psi : LoopPlane → ℝ} {i : Fin 2} {K : ℝ≥0}
    (hu : MemLp u 2 volume) (hW : MemLp W 2 volume)
    (hw : ∀ b, HasWeakPartialDeriv i (fun p => W p b) (fun p => u p b) univ)
    (hpsi : LipschitzWith K psi) (hc : HasCompactSupport psi) :
    (∫ p, psi p • W p) + (∫ p, fderiv ℝ psi p (EuclideanSpace.single i 1) • u p) = 0 := by
  have hp : MemLp psi 2 volume := hpsi.continuous.memLp_of_hasCompactSupport hc
  have hd := m64CompactLipschitz_fderiv_memLp hpsi hc i
  have hiW := m64L2_test_integrable hW hp
  have hiu := m64L2_test_integrable hu hd
  ext b
  let L := EuclideanSpace.proj (𝕜 := ℝ) b
  have h := m64WeakPartial_compact_lipschitz_test
    (L.comp_memLp' hu) (L.comp_memLp' hW) (hw b) hpsi hc
  change L ((∫ p, psi p • W p) + ∫ p, fderiv ℝ psi p (EuclideanSpace.single i 1) • u p) = L 0
  rw [map_add, map_zero, ← L.integral_comp_comm hiW, ← L.integral_comp_comm hiu]
  simp only [L, EuclideanSpace.coe_proj, Function.comp_def, PiLp.smul_apply,
    smul_eq_mul, mul_comm] at h ⊢
  linarith

end PoincareConjecture
