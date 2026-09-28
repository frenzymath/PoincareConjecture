import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.ConeTopology
import Mathlib.Topology.OpenPartialHomeomorph.Defs

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y] {p : X}

theorem cone_unit_iff_radial_potential_eq (hcomparison : RayComparison p)
    (F : OpenPartialHomeomorph Y (AsymptoticCone p hcomparison)) (f : Y → ℝ)
    (hpotential : ∀ x ∈ F.source,
      (asymptoticConeRadius hcomparison (F x) : ℝ) ^ 2 / 2 = f x)
    {x : Y} (hx : x ∈ F.source) :
    asymptoticConeRadius hcomparison (F x) = 1 ↔ f x = 1 / 2 := by
  have h := hpotential x hx
  constructor
  · intro hr
    rw [hr] at h
    norm_num at h
    exact h.symm
  · intro hf
    apply NNReal.coe_injective
    change (asymptoticConeRadius hcomparison (F x) : ℝ) = 1
    nlinarith [(asymptoticConeRadius hcomparison (F x)).coe_nonneg]

def unitLinkLocalLevelHomeomorph (hcomparison : RayComparison p)
    (F : OpenPartialHomeomorph Y (AsymptoticCone p hcomparison)) (f : Y → ℝ)
    (hpotential : ∀ x ∈ F.source,
      (asymptoticConeRadius hcomparison (F x) : ℝ) ^ 2 / 2 = f x) :
    {x : Y // x ∈ F.source ∧ f x = 1 / 2} ≃ₜ
      {z : AsymptoticConeUnitSlice p hcomparison // z.1 ∈ F.target} where
  toFun x := ⟨⟨F x, (cone_unit_iff_radial_potential_eq hcomparison F f hpotential x.2.1).mpr
    x.2.2⟩, F.map_source x.2.1⟩
  invFun z := ⟨F.symm z.1.1, F.map_target z.2, by
    apply (cone_unit_iff_radial_potential_eq hcomparison F f hpotential (F.map_target z.2)).mp
    rw [F.right_inv z.2]
    exact z.1.2⟩
  left_inv x := by
    apply Subtype.ext
    exact F.left_inv x.2.1
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact F.right_inv z.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact F.continuousOn.comp_continuous continuous_subtype_val (fun x => x.2.1)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact F.continuousOn_symm.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.2)

theorem isOpen_unitLink_chart_target (hcomparison : RayComparison p)
    (F : OpenPartialHomeomorph Y (AsymptoticCone p hcomparison)) :
    IsOpen {z : AsymptoticConeUnitSlice p hcomparison |
      z.1 ∈ F.target} :=
  F.open_target.preimage continuous_subtype_val

end Poincare.AncientVolume.ScalarRatio
