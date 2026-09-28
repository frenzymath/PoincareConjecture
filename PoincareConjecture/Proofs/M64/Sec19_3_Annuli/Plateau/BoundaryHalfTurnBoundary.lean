import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnMeasure
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "S" => interior m64AnnulusDomain
local notation "a" => curvePeriod / 2




def m64BoundaryHalfTurn (x : ℝ) : ℝ :=
  if x < curvePeriod / 2 then x + curvePeriod / 2 else x - curvePeriod / 2



theorem m64BoundaryHalfTurn_measurable : Measurable m64BoundaryHalfTurn :=
  Measurable.ite measurableSet_Iio (measurable_id.add measurable_const)
    (measurable_id.sub measurable_const)




theorem m64Annulus_angular_projection_measurePreserving :
    MeasurePreserving (fun p : LoopPlane => p 0) (volume.restrict S) (volume.restrict I) := by
  have hp : Measurable (fun p : LoopPlane => p 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).measurable
  refine ⟨hp, ?_⟩
  rw [← m64AnnulusPoint_measurePreserving.map_eq,
    Measure.map_map hp m64AnnulusPoint_measurePreserving.measurable]
  change Measure.map Prod.fst
    ((volume.restrict I).prod (volume.restrict (Icc (0 : ℝ) 1))) = volume.restrict I
  rw [Measure.map_fst_prod]
  simp only [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, one_smul]




theorem m64BoundaryHalfTurn_measurePreserving :
    MeasurePreserving m64BoundaryHalfTurn (volume.restrict I) (volume.restrict I) := by
  refine ⟨m64BoundaryHalfTurn_measurable, ?_⟩
  rw [← m64Annulus_angular_projection_measurePreserving.map_eq,
    Measure.map_map m64BoundaryHalfTurn_measurable
      m64Annulus_angular_projection_measurePreserving.measurable]
  have heq : (fun p : LoopPlane => m64BoundaryHalfTurn (p 0)) =
      fun p => m64AnnulusHalfTurn p 0 := by
    funext p
    simp only [m64BoundaryHalfTurn, m64AnnulusHalfTurn]
    split_ifs <;> rfl
  rw [show m64BoundaryHalfTurn ∘ (fun p : LoopPlane => p 0) =
    (fun p => m64AnnulusHalfTurn p 0) from heq]
  rw [m64Annulus_angular_projection_measurePreserving.map_eq]
  exact (m64Annulus_angular_projection_measurePreserving.comp
    m64AnnulusHalfTurn_measurePreserving).map_eq




theorem m64BoundaryHalfTurn_involutive_ae :
    ∀ᵐ x ∂volume.restrict I, m64BoundaryHalfTurn (m64BoundaryHalfTurn x) = x := by
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ curvePeriod := by
    apply ae_iff.mpr
    simp only [not_not]
    exact measure_singleton _
  filter_upwards [ae_restrict_of_ae hn, ae_restrict_mem measurableSet_Icc] with x hx hI
  by_cases hl : x < a
  · have hsum : ¬x + a < a := by linarith [hI.1]
    simp only [m64BoundaryHalfTurn, if_pos hl, if_neg hsum, add_sub_cancel_right]
  · have hsub : x - a < a := by
      have hlt : x < curvePeriod := lt_of_le_of_ne hI.2 hx
      linarith
    simp only [m64BoundaryHalfTurn, if_neg hl, if_pos hsub, sub_add_cancel]




theorem m64AnnulusHalfTurn_boundary_point (x s : ℝ) :
    m64AnnulusHalfTurn (annulusPoint x s) = annulusPoint (m64BoundaryHalfTurn x) s := by
  simp only [m64AnnulusHalfTurn, m64BoundaryHalfTurn, annulusPoint, Matrix.cons_val_zero]
  split_ifs <;> ext i <;> fin_cases i <;> simp




theorem m64BoundaryHalfTurn_integral_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : AEStronglyMeasurable f (volume.restrict I)) :
    (∫ x in I, f (m64BoundaryHalfTurn x)) = ∫ x in I, f x := by
  have hh : AEStronglyMeasurable f (Measure.map m64BoundaryHalfTurn (volume.restrict I)) := by
    rw [m64BoundaryHalfTurn_measurePreserving.map_eq]
    exact hf
  have h := integral_map m64BoundaryHalfTurn_measurable.aemeasurable hh
  rw [m64BoundaryHalfTurn_measurePreserving.map_eq] at h
  exact h.symm




theorem m64BoundaryHalfTurn_integral_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {phi : ℝ → ℝ} {f : ℝ → E}
    (hp : AEStronglyMeasurable phi (volume.restrict I))
    (hf : AEStronglyMeasurable f (volume.restrict I)) :
    (∫ x in I, phi x • f (m64BoundaryHalfTurn x)) =
      ∫ x in I, phi (m64BoundaryHalfTurn x) • f x := by
  have hpm := hp.comp_quasiMeasurePreserving
    m64BoundaryHalfTurn_measurePreserving.quasiMeasurePreserving
  have hpair : AEStronglyMeasurable
      (fun x => phi (m64BoundaryHalfTurn x) • f x) (volume.restrict I) := hpm.smul hf
  rw [← m64BoundaryHalfTurn_integral_comp hpair]
  apply integral_congr_ae
  filter_upwards [m64BoundaryHalfTurn_involutive_ae] with x hx
  rw [hx]

end PoincareConjecture
