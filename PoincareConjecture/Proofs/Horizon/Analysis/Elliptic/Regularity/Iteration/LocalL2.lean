import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.LocalIntegrability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal ContDiff

namespace Poincare.Analysis.Elliptic

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem memLp_two_restrict_union {u : E → ℝ} {s t : Set E}
    (hs : MemLp u 2 (volume.restrict s)) (ht : MemLp u 2 (volume.restrict t)) :
    MemLp u 2 (volume.restrict (s ∪ t)) := by
  apply (memLp_two_iff_integrable_sq
    (aestronglyMeasurable_union_iff.mpr ⟨hs.1, ht.1⟩)).mpr
  exact IntegrableOn.union hs.integrable_sq ht.integrable_sq

theorem memLp_two_restrict_finset_biUnion {ι : Type*} {u : E → ℝ}
    (s : Finset ι) (V : ι → Set E) (h : ∀ i ∈ s, MemLp u 2 (volume.restrict (V i))) :
    MemLp u 2 (volume.restrict (⋃ i ∈ s, V i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    exact memLp_two_restrict_union (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem compact_memLp_of_local_memLp {O : Set E} {u : E → ℝ}
    (hu : ∀ x ∈ O, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      MemLp u 2 (volume.restrict V)) :
    ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K) := by
  classical
  intro K hK hKO
  choose V hV hxV hVO huV using fun x : K => hu x (hKO x.property)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV (fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  exact (memLp_two_restrict_finset_biUnion s V (fun x _ => huV x)).mono_measure
    (Measure.restrict_mono hs le_rfl)

theorem local_memLp_of_compact_memLp {O : Set E} {u : E → ℝ} (hO : IsOpen O)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K)) :
    ∀ x ∈ O, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      MemLp u 2 (volume.restrict V) := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hx)
  refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    Metric.ball_subset_closedBall.trans hball, ?_⟩
  exact (hu (Metric.closedBall x r) (isCompact_closedBall x r) hball).mono_measure
    (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)

theorem local_memLp_iff_compact_memLp {O : Set E} {u : E → ℝ} (hO : IsOpen O) :
    (∀ x ∈ O, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      MemLp u 2 (volume.restrict V)) ↔
    ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K) :=
  ⟨compact_memLp_of_local_memLp, local_memLp_of_compact_memLp hO⟩

theorem local_memLp_mul_continuousOn {O : Set E} {u c : E → ℝ} (hO : IsOpen O)
    (hc : ContinuousOn c O)
    (hu : ∀ x ∈ O, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      MemLp u 2 (volume.restrict V)) :
    ∀ x ∈ O, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      MemLp (fun y => c y * u y) 2 (volume.restrict V) := by
  apply local_memLp_of_compact_memLp hO
  intro K hK hKO
  exact compact_memLp_mul_continuousOn hc (compact_memLp_of_local_memLp hu) hK hKO

theorem compact_memLp_mul_contDiffOn {O : Set E} {u c : E → ℝ} {k : WithTop ℕ∞}
    (hc : ContDiffOn ℝ k c O)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K)) :
    ∀ K, IsCompact K → K ⊆ O →
      MemLp (fun y => c y * u y) 2 (volume.restrict K) := by
  intro K hK hKO
  exact compact_memLp_mul_continuousOn hc.continuousOn hu hK hKO

end Poincare.Analysis.Elliptic
