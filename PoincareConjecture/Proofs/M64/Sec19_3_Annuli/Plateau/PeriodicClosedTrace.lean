import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.H1SliceTrace
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.HausdorffDistance











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology

namespace PoincareConjecture



theorem m64Curve_periodic_extension {Y : Type*} [TopologicalSpace Y]
    (W : ℝ → Y) {T : ℝ} (hT : 0 < T) (hW : ContinuousOn W (Icc (0 : ℝ) T))
    (hends : W 0 = W T) :
    ∃ U : ℝ → Y, Continuous U ∧ Function.Periodic U T ∧ EqOn U W (Icc (0 : ℝ) T) := by
  let : Fact (0 < T) := ⟨hT⟩
  let U := fun x : ℝ => AddCircle.liftIco T 0 W (x : AddCircle T)
  have h0 : U 0 = W 0 :=
    AddCircle.liftIco_zero_coe_apply ⟨le_rfl, hT⟩
  refine ⟨U, (AddCircle.liftIco_zero_continuous hends hW).comp
    (AddCircle.continuous_mk' T), ?_, ?_⟩
  · intro x
    exact congrArg (AddCircle.liftIco T 0 W) (AddCircle.coe_add_period T x)
  · intro x hx
    by_cases hxt : x = T
    · subst x
      change AddCircle.liftIco T 0 W (T : AddCircle T) = W T
      rw [AddCircle.coe_period]
      exact h0.trans hends
    · exact AddCircle.liftIco_zero_coe_apply ⟨hx.1, lt_of_le_of_ne hx.2 hxt⟩



theorem m64Curve_closed_target_of_ae
    {E : Type*} [PseudoMetricSpace E] (W : ℝ → E) {T : ℝ} (hT : 0 < T)
    (hW : ContinuousOn W (Icc (0 : ℝ) T)) {C : Set E}
    (hC : IsClosed C) (hne : C.Nonempty)
    (hae : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) T), W x ∈ C) :
    MapsTo W (Icc (0 : ℝ) T) C := by
  have hd : ContinuousOn (fun x => Metric.infDist (W x) C) (Icc (0 : ℝ) T) :=
    (Metric.continuous_infDist_pt C).comp_continuousOn hW
  have hz : (fun x => Metric.infDist (W x) C) =ᵐ[volume.restrict (Icc (0 : ℝ) T)]
      (fun _ => (0 : ℝ)) :=
    hae.mono (fun x hx => Metric.infDist_zero_of_mem hx)
  have hclosure : Icc (0 : ℝ) T ⊆ closure (interior (Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo hT.ne]
  have heq := Measure.eqOn_of_ae_eq hz hd continuousOn_const hclosure
  intro x hx
  exact (hC.mem_iff_infDist_zero hne).mpr (heq hx)

end PoincareConjecture
