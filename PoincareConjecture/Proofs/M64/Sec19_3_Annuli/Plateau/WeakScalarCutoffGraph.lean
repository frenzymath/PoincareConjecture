import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakSobolevExtension
import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth













noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak





theorem m64WeakScalar_cutoff_strong_graph
    {O : Set LoopPlane} (hO : IsOpen O) (u : LoopPlane → ℝ)
    (V : Fin 2 → LoopPlane → ℝ) (hu : MemLp u 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hweak : ∀ i, HasWeakPartialDeriv i (V i) u O)
    (chi : LoopPlane → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hs : tsupport chi ⊆ O) :
    let F := fun p => chi p * u p
    let W := fun i => O.indicator (fun p => chi p * V i p +
      fderiv ℝ chi p (EuclideanSpace.single i 1) * u p)
    MemLp F 2 volume ∧ (∀ i, MemLp (W i) 2 volume) ∧
      (∀ i, HasWeakPartialDeriv i (W i) F univ) ∧
      ∃ f : ℕ → LoopPlane → ℝ, (∀ j, ContDiff ℝ ∞ (f j)) ∧
        Tendsto (fun j => eLpNorm (f j - F) 2 volume) atTop (𝓝 0) ∧
        ∀ i : Fin 2, Tendsto (fun j => eLpNorm
          (fun p => fderiv ℝ (f j) p (EuclideanSpace.single i 1) - W i p)
            2 volume) atTop (𝓝 0) := by
  let hw : MemW1pWitness 2 u O := {
    memLp := hu
    weakGrad := fun p => WithLp.toLp 2 (fun i => V i p)
    weakGrad_component_memLp := hV
    isWeakGrad := hweak }
  obtain ⟨P, hP⟩ := (hc.isCompact_range hchi.continuous).isBounded.exists_norm_le
  obtain ⟨Q, hQ⟩ := ((hc.fderiv ℝ).isCompact_range
    (hchi.continuous_fderiv (by simp))).isBounded.exists_norm_le
  have hP0 : 0 ≤ P := (norm_nonneg (chi 0)).trans (hP _ (mem_range_self _))
  have hQ0 : 0 ≤ Q := (norm_nonneg (fderiv ℝ chi 0)).trans (hQ _ (mem_range_self _))
  let hwc := hw.mulSmoothBoundedP (by norm_num : (1 : ENNReal) ≤ 2)
    hO hchi hP0 hQ0 (fun p => hP _ (mem_range_self p)) (fun p => hQ _ (mem_range_self p))
  obtain ⟨H, hH⟩ := m64WeakSobolev_extend_supported hO hwc hc.mul_right
    (tsupport_mul_subset_left.trans hs)
  have hformula (p : LoopPlane) (i : Fin 2) : H.weakGrad p i =
      O.indicator (fun q => chi q * V i q +
        fderiv ℝ chi q (EuclideanSpace.single i 1) * u q) p := by
    simpa only [hwc, hw, MemW1pWitness.mulSmoothBoundedP, PiLp.toLp_apply,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      using hH p i
  let H2 : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) (fun p => chi p * u p) univ := {
    memLp := by simpa using H.memLp
    weakGrad := H.weakGrad
    weakGrad_component_memLp := fun i => by simpa using H.weakGrad_component_memLp i
    isWeakGrad := H.isWeakGrad }
  obtain ⟨f, hf, _, _, hval, hcol⟩ := exists_smooth_compactSupport_W1p_approx_univ
    (by norm_num : (1 : ℝ) < 2) H2 hc.mul_right
  refine ⟨by simpa using H.memLp, ?_, ?_, f, hf, ?_, ?_⟩
  · intro i
    simpa only [Measure.restrict_univ, hformula] using H.weakGrad_component_memLp i
  · intro i
    simpa only [hformula] using H.isWeakGrad i
  · simpa only [ENNReal.ofReal_ofNat, Pi.sub_def] using hval
  · intro i
    simpa only [H2, hformula, ENNReal.ofReal_ofNat] using hcol i

end PoincareConjecture
