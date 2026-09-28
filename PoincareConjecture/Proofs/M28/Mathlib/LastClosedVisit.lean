import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas










set_option autoImplicit false

open Set

namespace Poincare

variable {X : Type*} [TopologicalSpace X]




theorem exists_last_visit_of_isClosed {S : Set X} (hS : IsClosed S)
    {gamma : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hgamma : ContinuousOn gamma (Icc a b)) (ha : gamma a ∈ S) :
    ∃ t ∈ Icc a b, gamma t ∈ S ∧ ∀ u ∈ Ioc t b, gamma u ∉ S := by
  let F : Set ℝ := Icc a b ∩ gamma ⁻¹' S
  have hF : IsCompact F := isCompact_Icc.of_isClosed_subset
    (hgamma.preimage_isClosed_of_isClosed isClosed_Icc hS) inter_subset_left
  obtain ⟨t, ht, hmax⟩ := hF.exists_isGreatest ⟨a, ⟨le_rfl, hab⟩, ha⟩
  refine ⟨t, ht.1, ht.2, ?_⟩
  intro u hu huS
  exact (not_lt_of_ge (hmax ⟨⟨ht.1.1.trans hu.1.le, hu.2⟩, huS⟩)) hu.1





theorem exists_last_visit_component {S U : Set X} (hS : IsClosed S)
    {gamma : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hgamma : ContinuousOn gamma (Icc a b))
    (hU : MapsTo gamma (Icc a b) U) (ha : gamma a ∈ S) :
    ∃ t ∈ Icc a b, gamma t ∈ S ∧
      ∀ u ∈ Ioc t b, gamma u ∈ connectedComponentIn (U \ S) (gamma b) := by
  obtain ⟨t, ht, htS, hafter⟩ := exists_last_visit_of_isClosed hS hab hgamma ha
  refine ⟨t, ht, htS, ?_⟩
  intro u hu
  have hsub : Icc u b ⊆ Icc a b := Icc_subset_Icc (ht.1.trans hu.1.le) le_rfl
  have hconn : IsPreconnected (gamma '' Icc u b) :=
    isPreconnected_Icc.image gamma (hgamma.mono hsub)
  have hcomp : gamma '' Icc u b ⊆ U \ S := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨hU (hsub hv), hafter v ⟨hu.1.trans_le hv.1, hv.2⟩⟩
  exact hconn.subset_connectedComponentIn
    (mem_image_of_mem gamma (right_mem_Icc.mpr hu.2)) hcomp
    (mem_image_of_mem gamma (left_mem_Icc.mpr hu.2))

end Poincare
