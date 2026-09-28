import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderIntervalModel
import PoincareConjecture.Proofs.M28.Mathlib.UnitIntervalReparametrization









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}



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

end PoincareConjecture.OpenCylinderModel
