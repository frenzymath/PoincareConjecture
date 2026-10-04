import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderIntervalModel
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Geometry.UnitIntervalReparametrization

/-!
# Place the terminal-neck threshold at the middle height

Morgan--Tian Claim 10.8, p. 254; M28 derivation 94. A smooth fractional
linear change retains the same cylinder carrier and gives the exact
old-height criterion for the new positive half.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

/-- A chosen strict height cutoff becomes the positive-half threshold
of a smooth model on the same cylinder (MT Claim 10.8, p. 254). -/
theorem exists_midlevel_model (T : OpenCylinderModel U) {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ T' : OpenCylinderModel U,
      T'.coordinate = (fun z => T.coordinate (z.1, Poincare.unitIntervalReparam a z.2)) ∧
      T'.inverse = (fun x => ((T.inverse x).1,
        Poincare.unitIntervalReparam (1 - a) (T.inverse x).2)) ∧
      ∀ x ∈ U, (1 / 2 : ℝ) < (T'.inverse x).2 ↔ a < (T.inverse x).2 := by
  obtain ⟨hf, hfI, hgf, _hmid, hhalf⟩ := Poincare.unitIntervalReparam_properties ha
  have hb : 1 - a ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.mpr ha.2, by linarith [ha.1]⟩
  obtain ⟨hg, hgI, hfg, _hmid', _hhalf'⟩ := Poincare.unitIntervalReparam_properties hb
  have heq : 1 - (1 - a) = a := by ring
  rw [heq] at hfg
  obtain ⟨T', hc, hv⟩ := T.exists_model_of_interval_reparametrization subset_rfl
    (V := U) (fun x => ⟨fun hx => ⟨hx, (T.inverse_mem x hx).2⟩, fun hx => hx.1⟩)
    (Poincare.unitIntervalReparam a) (Poincare.unitIntervalReparam (1 - a))
    hf hg hfI hgI hgf hfg
  refine ⟨T', hc, hv, ?_⟩
  intro x hx
  rw [hv]
  exact hhalf _ (T.inverse_mem x hx).2

end PoincareMT.OpenCylinderModel
