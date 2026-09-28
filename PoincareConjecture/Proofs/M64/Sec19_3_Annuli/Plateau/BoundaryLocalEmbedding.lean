import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateSwap
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConformalGain
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.Sobolev












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean

namespace PoincareConjecture





theorem m64HalfBall_H1_memLp {u : LoopPlane → ℝ} {a : LoopPlane} {r R : ℝ}
    (hrR : r < R) (hu : MemW1p 2 u (ball a R ∩ {p : LoopPlane | 0 < p 1}))
    {q : ℝ} (hq : 1 ≤ q) :
    MemLp u (ENNReal.ofReal q)
      (volume.restrict (ball a r ∩ {p : LoopPlane | 0 < p 1})) := by
  let H := {p : LoopPlane | 0 < p 1}
  have hH : IsOpen H := isOpen_lt continuous_const
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
  obtain ⟨chi, hchi, hc, -, hone, hs⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (isCompact_closedBall a r) isOpen_ball (closedBall_subset_ball hrR)
  have hloc := Poincare.Analysis.Sobolev.BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset
    1 hH isOpen_ball (MemWkp.one_iff_memW1p.mpr hu) hchi hc hs
  have hlp := m64NormalHalfPlane_H1_memLp hc.mul_right
    (MemWkp.one_iff_memW1p.mp hloc) hq
  apply (hlp.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)).ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_ball.inter hH.measurableSet)] with p hp
  change chi p * u p = u p
  rw [hone p (ball_subset_closedBall hp.1), one_mul]





theorem m64HalfBall_conformal_columns_memLp
    {n : ℕ} (G : LoopPlane → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {a : LoopPlane} {r R : ℝ}
    {kappa C modulus : ℝ} (hrR : r < R) (hk : 0 < kappa)
    (htangent : ∀ j, MemW1p 2 (fun p => V 0 p j)
      (ball a R ∩ {p : LoopPlane | 0 < p 1}))
    (hnormal : AEStronglyMeasurable (V 1)
      (volume.restrict (ball a R ∩ {p : LoopPlane | 0 < p 1})))
    (hdata : ∀ᵐ p ∂volume.restrict (ball a R ∩ {p : LoopPlane | 0 < p 1}),
      ‖G p‖ ≤ C ∧ kappa * ‖V 1 p‖ ^ 2 ≤ G p (V 1 p) (V 1 p) ∧
      G p (V 1 p) (V 1 p) = modulus ^ 2 * G p (V 0 p) (V 0 p))
    {q : ℝ} (hq : 1 ≤ q) :
    ∀ i, MemLp (V i) (ENNReal.ofReal q)
      (volume.restrict (ball a r ∩ {p : LoopPlane | 0 < p 1})) := by
  have hsub : ball a r ∩ {p : LoopPlane | 0 < p 1} ⊆
      ball a R ∩ {p : LoopPlane | 0 < p 1} :=
    inter_subset_inter_left _ (ball_subset_ball hrR.le)
  have hle := Measure.restrict_mono hsub (le_rfl : volume ≤ (volume : Measure LoopPlane))
  have hzero : MemLp (V 0) (ENNReal.ofReal q)
      (volume.restrict (ball a r ∩ {p : LoopPlane | 0 < p 1})) :=
    MemLp.of_eval_piLp (fun j => m64HalfBall_H1_memLp hrR (htangent j) hq)
  intro i
  fin_cases i
  · exact hzero
  · exact m64WeightedConformal_normal_memLp G hk hzero (hnormal.mono_measure hle)
      (MeasureTheory.ae_mono hle hdata)

end PoincareConjecture
