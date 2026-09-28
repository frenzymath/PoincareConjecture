import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.Injection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.CollarGluing.OriginalDomainInjection










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem isClopen_frontier_of_closed_deletion
    {X : Type*} [TopologicalSpace X] {R R' D : Set X}
    (hD : IsClosed D) (hfront : frontier R' = frontier R \ D) :
    IsClopen ((Subtype.val : frontier R → X) ⁻¹' frontier R') := by
  have heq : (Subtype.val : frontier R → X) ⁻¹' frontier R' =
      (Subtype.val : frontier R → X) ⁻¹' Dᶜ := by
    ext x
    simp only [mem_preimage, hfront, mem_sdiff, x.property, true_and, mem_compl_iff]
  exact ⟨isClosed_frontier.preimage continuous_subtype_val,
    heq ▸ hD.isOpen_compl.preimage continuous_subtype_val⟩

theorem frontier_ambient_injective_of_closed_deletion
    {X : Type*} [TopologicalSpace X] {R R' D : Set X}
    (hD : IsClosed D) (hfront : frontier R' = frontier R \ D)
    (hinj : ∀ x : frontier R, Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier R)) x)) :
    ∀ x : frontier R', Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier R')) x) := by
  have hsub : frontier R' ⊆ frontier R := hfront ▸ sdiff_subset
  let inc := ContinuousMap.inclusion hsub
  intro x
  have hinc := FundamentalGroup.inclusion_injective_of_isClopen hsub
    (isClopen_frontier_of_closed_deletion hD hfront) x
  have heq : VanKampen.inclusion (frontier R') =
      (VanKampen.inclusion (frontier R)).comp inc := rfl
  rw [heq, FundamentalGroup.map_comp]
  exact (hinj (inc x)).comp hinc




theorem PLDomain.closed_sides_ambient_injective_of_frontier_ambient
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hminus : IsCompact (interior R)ᶜ)
    (hne : (interior R).Nonempty) (hneminus : (interior (interior R)ᶜ).Nonempty)
    (hinj : ∀ x : frontier R, Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier R)) x)) :
    ∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X)), ∀ x : T,
      Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x) := by
  apply he.closed_sides_ambient_injective hR hminus hne hneminus
  intro T hT
  have hFT : frontier R ⊆ T := by
    simp only [mem_insert_iff, mem_singleton_iff] at hT
    rcases hT with rfl | rfl
    · exact he.closed.frontier_subset
    · exact fun _ hx => hx.2
  refine ⟨hFT, ?_⟩
  intro x
  have hh := hinj x
  have heq : VanKampen.inclusion (frontier R) =
      (VanKampen.inclusion T).comp (ContinuousMap.inclusion hFT) := rfl
  rw [heq, FundamentalGroup.map_comp] at hh
  intro a b hab
  apply hh
  exact congrArg (FundamentalGroup.map (VanKampen.inclusion T)
    ((ContinuousMap.inclusion hFT) x)) hab



theorem PLDomain.closed_sides_ambient_injective_of_frontier_deletion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R R' D : Set X}
    (he : PLDomain e R') (hR : IsCompact R') (hminus : IsCompact (interior R')ᶜ)
    (hne : (interior R').Nonempty) (hneminus : (interior (interior R')ᶜ).Nonempty)
    (hD : IsClosed D) (hfront : frontier R' = frontier R \ D)
    (hinj : ∀ x : frontier R, Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier R)) x)) :
    (∀ x : frontier R', Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier R')) x)) ∧
    ∀ T ∈ ({R', (interior R')ᶜ} : Set (Set X)), ∀ x : T,
      Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x) := by
  have hnew := frontier_ambient_injective_of_closed_deletion hD hfront hinj
  exact ⟨hnew, he.closed_sides_ambient_injective_of_frontier_ambient
    hR hminus hne hneminus hnew⟩

end PoincareConjecture.M76
