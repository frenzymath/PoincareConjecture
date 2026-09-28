import PoincareConjecture.Proofs.M64.Mathlib.ConnectedPhaseDifference
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeMidpoint














noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M64BoundaryCone

open Proofs.M58

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]




def normalizedPhase (beta : C → ℝ) (v : ℝ → C) (L : ℝ → ℝ) : C → ℝ :=
  fun y => beta y + (L 0 - beta (v 0))




theorem normalizedPhase_properties {beta : C → ℝ} {v : ℝ → C} {L : ℝ → ℝ}
    {U : Set C} {k : ℝ} (hk : k ≠ 0) (hbeta : ContDiffOn ℝ 1 beta U)
    (hv : ContinuousOn v (Icc (0 : ℝ) Real.pi))
    (hvU : MapsTo v (Icc (0 : ℝ) Real.pi) U)
    (hL : ContinuousOn L (Icc (0 : ℝ) Real.pi))
    (hobs : ∀ theta ∈ Icc (0 : ℝ) Real.pi,
      angularPoint (k * L theta) = angularPoint (k * beta (v theta))) :
    ContDiffOn ℝ 1 (normalizedPhase beta v L) U ∧
      (∀ theta ∈ Icc (0 : ℝ) Real.pi, normalizedPhase beta v L (v theta) = L theta) ∧
      ∀ y : C, angularPoint (k * normalizedPhase beta v L y) =
        angularPoint (k * beta y) := by
  refine ⟨hbeta.add contDiffOn_const, ?_, ?_⟩
  · exact fun theta htheta => (m64ContinuousPhase_difference isPreconnected_Icc hk hL
      (hbeta.continuousOn.comp hv hvU) hobs
      (show (0 : ℝ) ∈ Icc (0 : ℝ) Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
      theta htheta).symm
  · exact fun y => m64AngularPoint_phase_shift (hobs 0 ⟨le_rfl, Real.pi_pos.le⟩) (beta y)




theorem normalizedPhase_diameter {beta : C → ℝ} {v : ℝ → C} {L : ℝ → ℝ}
    {r : ℝ} {axis : ℝ → C} {a b c : ℝ} (hr : 0 < r) (hba : b ≤ a)
    (haxis : ∀ t ∈ Icc b a, beta (axis t) = t + c)
    (hfirst : v 0 = axis a) (hlast : v Real.pi = axis b)
    (hline : ∀ t : ℝ, AffineMap.lineMap (axis b) (axis a) t =
      axis (AffineMap.lineMap b a t))
    (hend : normalizedPhase beta v L (v Real.pi) = L Real.pi)
    {s : ℝ} (hs : s ∈ Icc (-r) r) :
    normalizedPhase beta v L (halfConeDiameter r (v 0) (v Real.pi) s) =
      AffineMap.lineMap (L Real.pi) (L 0) ((s + r) / (2 * r)) := by
  have ha : a ∈ Icc b a := ⟨hba, le_rfl⟩
  have hb : b ∈ Icc b a := ⟨le_rfl, hba⟩
  have ht : (s + r) / (2 * r) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [hs.1]) (by positivity),
      (div_le_one (by positivity : 0 < 2 * r)).mpr (by linarith [hs.2])⟩
  have hchord : AffineMap.lineMap b a ((s + r) / (2 * r)) ∈ Icc b a :=
    (convex_Icc b a).mapsTo_lineMap hb ha ht
  have hLpi : L Real.pi = b + c + (L 0 - (a + c)) := by
    simpa only [normalizedPhase, hfirst, hlast, haxis a ha, haxis b hb] using hend.symm
  dsimp only [normalizedPhase, halfConeDiameter]
  rw [hfirst, hlast, hline, haxis _ hchord, haxis a ha, hLpi]
  simp only [AffineMap.lineMap_apply_module, smul_eq_mul]
  ring

end PoincareConjecture.M64BoundaryCone
