import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem connectedComponentIn_component_replacement_inside
    {X : Type*} [TopologicalSpace X] {A Q N : Set X} {a x : X}
    (hQA : Q ⊆ A) (hNC : N ⊆ connectedComponentIn A a) (hx : x ∈ N) :
    connectedComponentIn ((Q \ connectedComponentIn A a) ∪ N) x =
      connectedComponentIn N x := by
  let C := connectedComponentIn A a
  let Q' := (Q \ C) ∪ N
  have hsub : Q' ⊆ A := union_subset (inter_subset_left.trans hQA)
    (hNC.trans (connectedComponentIn_subset A a))
  have hCC : connectedComponentIn Q' x ⊆ C := by
    have h := connectedComponentIn_mono x hsub
    rwa [←connectedComponentIn_eq (hNC hx)] at h
  apply Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (show x ∈ Q' from Or.inr hx))
    intro y hy
    rcases connectedComponentIn_subset Q' x hy with hyQ | hyN
    · exact False.elim (hyQ.2 (hCC hy))
    · exact hyN
  · exact connectedComponentIn_mono x subset_union_right

theorem connectedComponentIn_component_replacement_outside
    {X : Type*} [TopologicalSpace X] {A Q N : Set X} {a x : X}
    (hQA : Q ⊆ A) (hNC : N ⊆ connectedComponentIn A a)
    (hx : x ∈ Q \ connectedComponentIn A a) :
    connectedComponentIn ((Q \ connectedComponentIn A a) ∪ N) x =
      connectedComponentIn Q x := by
  let C := connectedComponentIn A a
  let Q' := (Q \ C) ∪ N
  have hsub : Q' ⊆ A := union_subset (inter_subset_left.trans hQA)
    (hNC.trans (connectedComponentIn_subset A a))
  have haway : Disjoint (connectedComponentIn A x) C := by
    apply disjoint_left.mpr
    intro y hyx hya
    have heq := (connectedComponentIn_eq hyx).trans (connectedComponentIn_eq hya).symm
    exact hx.2 (heq ▸ mem_connectedComponentIn (hQA hx.1))
  apply Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (show x ∈ Q' from Or.inl hx))
    intro y hy
    rcases connectedComponentIn_subset Q' x hy with hyQ | hyN
    · exact hyQ.1
    · exact False.elim (disjoint_left.mp haway (connectedComponentIn_mono x hsub hy) (hNC hyN))
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx.1)
    intro y hy
    exact Or.inl ⟨connectedComponentIn_subset Q x hy,
      fun hyC => disjoint_left.mp haway (connectedComponentIn_mono x hQA hy) hyC⟩

theorem HasNoPuncturedSphereComponents.replace_ambient_component
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : X → E}
    {A Q N : Set X} {a : X}
    (hQA : Q ⊆ A) (hNC : N ⊆ connectedComponentIn A a)
    (hQ : HasNoPuncturedSphereComponents e f Q)
    (hN : HasNoPuncturedSphereComponents e f N) :
    HasNoPuncturedSphereComponents e f ((Q \ connectedComponentIn A a) ∪ N) := by
  intro x hx hm
  rcases hx with hx | hx
  · rw [connectedComponentIn_component_replacement_outside hQA hNC hx] at hm
    exact hQ x hx.1 hm
  · rw [connectedComponentIn_component_replacement_inside hQA hNC hx] at hm
    exact hN x hx hm

theorem HasNoPuncturedSphereComponents.replace_component_cut
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : X → E}
    {A O U : Set X} {a : X}
    (hOC : O ⊆ connectedComponentIn A a) (hUC : U ⊆ connectedComponentIn A a)
    (hQ : HasNoPuncturedSphereComponents e f (A \ O))
    (hN : HasNoPuncturedSphereComponents e f (connectedComponentIn A a \ U)) :
    HasNoPuncturedSphereComponents e f (A \ U) := by
  have heq : ((A \ O) \ connectedComponentIn A a) ∪ (connectedComponentIn A a \ U) =
      A \ U := by
    ext x
    constructor
    · rintro (⟨⟨hxA,_⟩,hxC⟩ | ⟨hxC,hxU⟩)
      · exact ⟨hxA,fun hxU => hxC (hUC hxU)⟩
      · exact ⟨connectedComponentIn_subset A a hxC,hxU⟩
    · rintro ⟨hxA,hxU⟩
      by_cases hxC : x ∈ connectedComponentIn A a
      · exact Or.inr ⟨hxC,hxU⟩
      · exact Or.inl ⟨⟨hxA,fun hxO => hxC (hOC hxO)⟩,hxC⟩
  rw [←heq]
  exact hQ.replace_ambient_component inter_subset_left inter_subset_left hN

end PoincareConjecture.M76
