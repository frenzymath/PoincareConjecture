import PoincareConjecture.Definitions.Ch11.SingularLimits
import PoincareConjecture.Proofs.M12.GeneralizedCylinderRestriction

set_option autoImplicit false

universe u

namespace PoincareConjecture

namespace GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

theorem time_mem_interval (e : GeneralizedFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (x : C.carrier) : origin + s / scale ∈ F.interval :=
  (F.slice_nonempty_iff _).mp ⟨e.forward s hs x⟩

end GeneralizedFlowCylinder

theorem GeneralizedStrongNeck.backward_time_mem
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon)
    {s : ℝ} (hs : s ∈ Set.Ioc (-1 : ℝ) 0) :
    t + s / (N.scale⁻¹ ^ 2) ∈ F.interval :=
  N.time_cylinder.time_mem_interval s hs N.center

theorem GeneralizedStrongNeck.not_minimum
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon)
    (hmin : ∀ s ∈ F.interval, t ≤ s) : False := by
  have htime := N.backward_time_mem (s := -(1 / 2 : ℝ)) (by constructor <;> norm_num)
  have hle := hmin _ htime
  have hscale : 0 < N.scale⁻¹ ^ 2 := N.time_cylinder.scale_pos
  have hneg : -(1 / 2 : ℝ) / (N.scale⁻¹ ^ 2) < 0 := div_neg_of_neg_of_pos
    (by norm_num) hscale
  linarith

end PoincareConjecture
