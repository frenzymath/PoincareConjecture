import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set Metric

local notation "I" => Icc (-1 : ℝ) 1

variable {A X : Type*} [TopologicalSpace A] [CompactSpace A] [TopologicalSpace X]

theorem Continuous.exists_closed_strip_subset {f : A × I → X} (hf : Continuous f)
    {W : Set X} (hW : IsOpen W)
    (hzero : ∀ a : A, f (a, ⟨0, by norm_num⟩) ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (a : A) (t : I), |(t : ℝ)| ≤ δ → f (a, t) ∈ W := by
  let i0 : I := ⟨0, by norm_num⟩
  have hbase : (univ : Set A) ×ˢ {i0} ⊆ f ⁻¹' W := by
    rintro ⟨a, t⟩ ⟨_, ht⟩
    have ht' : t = i0 := ht
    subst t
    exact hzero a
  obtain ⟨u, v, _, hv, hu, h0v, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton (hW.preimage hf) hbase
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.mp hv i0 (h0v (mem_singleton i0))
  let δ := min (r / 2) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (half_pos hr) (by norm_num)
  have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro a t ht
  have htv : t ∈ v := hrv (by
    change dist (t : ℝ) (0 : ℝ) < r
    rw [Real.dist_eq, sub_zero]
    exact ht.trans_lt hδr)
  exact huv ⟨hu (mem_univ a), htv⟩
