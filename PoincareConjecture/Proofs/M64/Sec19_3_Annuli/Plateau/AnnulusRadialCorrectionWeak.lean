import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialReflectionColumns
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LipschitzObservedColumns

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

private theorem scalar_weak_partial_on_open
    {f : LoopPlane → ℝ} {O : Set LoopPlane} (hO : IsOpen O)
    {K : ℝ≥0} (hf : LipschitzOnWith K f O) (i : Fin 2) :
    HasWeakPartialDeriv i (fun p => fderiv ℝ f p (EuclideanSpace.single i 1)) f O := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hv : F =ᵐ[volume.restrict O] f := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with p hp
    exact (heq hp).symm
  have hd : (fun p => lineDeriv ℝ F p (EuclideanSpace.single i 1)) =ᵐ[volume.restrict O]
      (fun p => fderiv ℝ f p (EuclideanSpace.single i 1)) := by
    filter_upwards [ae_restrict_mem hO.measurableSet,
      ae_restrict_of_ae (hF.ae_differentiableAt (μ := volume))] with p hp hdp
    have hnear : f =ᶠ[𝓝 p] F := by
      filter_upwards [hO.mem_nhds hp] with q hq
      exact heq hq
    rw [hdp.lineDeriv_eq_fderiv, hnear.fderiv_eq]
  exact m64WeakPartialDeriv_ae_congr hv hd
    (hasWeakPartialDeriv_lineDeriv_of_lipschitz hF i)

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64LipschitzOn_precompact_weak_columns
    {K O : Set LoopPlane} (hK : IsCompact K) (hO : IsOpen O) (hOK : O ⊆ K)
    {f : LoopPlane → E} {L : ℝ≥0} (hf : LipschitzOnWith L f K) :
    MemLp f 2 (volume.restrict O) ∧
      (∀ i, MemLp (fun p => fderiv ℝ f p (EuclideanSpace.single i 1)) 2 (volume.restrict O)) ∧
      ∀ i b, HasWeakPartialDeriv i
        (fun p => (fderiv ℝ f p (EuclideanSpace.single i 1)) b) (fun p => f p b) O := by
  let : IsFiniteMeasure (volume.restrict O) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hOK).trans_lt hK.measure_lt_top⟩
  have hfo := hf.mono hOK
  have hdiff : ∀ᵐ p ∂volume.restrict O, DifferentiableAt ℝ f p := by
    filter_upwards [hfo.ae_differentiableWithinAt hO.measurableSet,
      ae_restrict_mem hO.measurableSet] with p hp hpO
    exact hp.differentiableAt (hO.mem_nhds hpO)
  have hcoordinate (b : Fin m) : LipschitzOnWith
      (‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) b‖₊ * L) (fun p => f p b) O :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) b).lipschitz.comp_lipschitzOnWith hfo
  have hd (i : Fin 2) (b : Fin m) :
      (fun p => fderiv ℝ (fun q => f q b) p (EuclideanSpace.single i 1)) =ᵐ[volume.restrict O]
        (fun p => (fderiv ℝ f p (EuclideanSpace.single i 1)) b) := by
    filter_upwards [hdiff] with p hp
    let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) b
    have h := (P.hasFDerivAt.comp p hp.hasFDerivAt).fderiv
    exact congrArg (fun D => D (EuclideanSpace.single i 1)) h
  refine ⟨?_, ?_, ?_⟩
  · apply (memLp_two_iff_integrable_sq_norm
      (hfo.continuousOn.aestronglyMeasurable hO.measurableSet)).mpr
    exact (hf.continuousOn.norm.pow 2).integrableOn_compact hK |>.mono_set hOK
  · intro i
    apply MemLp.of_eval_piLp
    intro b
    have h := (memLp_top_fderiv_apply_of_lipschitzOn hO (hcoordinate b)
      (EuclideanSpace.single i 1)).mono_exponent (p := 2) le_top
    exact (memLp_congr_ae (hd i b)).mp h
  · intro i b
    exact m64WeakPartialDeriv_ae_congr EventuallyEq.rfl (hd i b)
      (scalar_weak_partial_on_open hO (hcoordinate b) i)

theorem m64RadialCorrect_weak_data
    {f h : LoopPlane → E} (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h)
    {a : LoopPlane} (ha : a 1 = 0) (r : ℝ) :
    MemLp (m64RadialCorrect f h) 2 (volume.restrict (ball a r)) ∧
      (∀ i, MemLp (fun p => fderiv ℝ (m64RadialCorrect f h) p
        (EuclideanSpace.single i 1)) 2 (volume.restrict (ball a r))) ∧
      ∀ i b, HasWeakPartialDeriv i
        (fun p => (fderiv ℝ (m64RadialCorrect f h) p (EuclideanSpace.single i 1)) b)
        (fun p => m64RadialCorrect f h p b) (ball a r) := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall a r) (isCompact_closedBall a r)
  obtain ⟨L, hL⟩ := hh.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall a r) (isCompact_closedBall a r)
  exact m64LipschitzOn_precompact_weak_columns (isCompact_closedBall a r) isOpen_ball
    ball_subset_closedBall (m64RadialCorrect_lipschitzOn ha hK hL)

end PoincareConjecture
