import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Poincare.Analysis.Sobolev.BoundaryCoordinates

def split (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin m) × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (m + 1) => ℝ)).symm.trans
      ((ContinuousLinearEquiv.prodComm ℝ ℝ (Fin m → ℝ)).trans
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.prodCongr
          (ContinuousLinearEquiv.refl ℝ ℝ))))

@[simp] theorem split_fst_apply (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 1))) (i : Fin m) :
    (split m x).1 i = x i.succ := rfl

@[simp] theorem split_snd (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (split m x).2 = x 0 := rfl

@[simp] theorem split_symm_zero (m : ℕ) (p : EuclideanSpace ℝ (Fin m) × ℝ) :
    (split m).symm p 0 = p.2 := rfl

@[simp] theorem split_symm_succ (m : ℕ) (p : EuclideanSpace ℝ (Fin m) × ℝ) (i : Fin m) :
    (split m).symm p i.succ = p.1 i := rfl

theorem measurePreserving_split (m : ℕ) :
    MeasurePreserving (split m) volume
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).prod (volume : Measure ℝ)) := by
  have hsplit : MeasurePreserving
      (fun x : Fin (m + 1) → ℝ => (x 0, fun i : Fin m => x i.succ))
      volume volume := by
    convert! volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 using 1
  have hpair := ((PiLp.volume_preserving_toLp (Fin m)).prod
    (MeasurePreserving.id (volume : Measure ℝ))).comp
      (Measure.measurePreserving_swap.comp
        (hsplit.comp (PiLp.volume_preserving_ofLp (Fin (m + 1)))))
  convert! hpair using 1

theorem measurePreserving_split_symm (m : ℕ) :
    MeasurePreserving (split m).symm
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).prod (volume : Measure ℝ)) volume :=
  (measurePreserving_split m).symm (split m).toHomeomorph.toMeasurableEquiv

end Poincare.Analysis.Sobolev.BoundaryCoordinates
