import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousMap.Basic

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt

theorem inward_family_mem_connectedComponentIn
    {P X : Type*} [TopologicalSpace P] [PreconnectedSpace P] [TopologicalSpace X]
    (Γ : C(P × unitInterval,X)) {V : Set X}
    (hinto : ∀ p (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → Γ (p,t) ∈ V)
    (p₀ : P) :
    ∀ p (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      Γ (p,t) ∈ connectedComponentIn V (Γ (p₀,⟨1/2,by norm_num,by norm_num⟩)) := by
  have hconn : IsPreconnected (Γ '' (univ ×ˢ Ioo (0 : unitInterval) 1)) :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image Γ Γ.continuous.continuousOn
  have hsub : Γ '' (univ ×ˢ Ioo (0 : unitInterval) 1) ⊆ V := by
    rintro _ ⟨⟨p,t⟩,⟨_,ht⟩,rfl⟩
    exact hinto p t ht.1 ht.2
  have hbase : Γ (p₀,⟨1/2,by norm_num,by norm_num⟩) ∈
      Γ '' (univ ×ˢ Ioo (0 : unitInterval) 1) := by
    apply mem_image_of_mem
    exact ⟨mem_univ _,show (0 : ℝ) < 1/2 ∧ 1/2 < (1 : ℝ) by norm_num⟩
  intro p t ht ht1
  exact hconn.subset_connectedComponentIn hbase hsub
    (mem_image_of_mem Γ ⟨mem_univ _,ht,ht1⟩)

end PoincareConjecture.M76.PrismBelt
