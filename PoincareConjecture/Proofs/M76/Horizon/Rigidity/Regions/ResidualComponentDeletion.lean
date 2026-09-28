import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.ResidualModelInvariance
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.Compression.PhaseModelExcision








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.FrontierResidualModel

local notation "V3" => (Fin 3 → ℝ)

theorem exists_component_embedding_of_deletion
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N N' F F' : Set X}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel e N' F')
    (D : Set (Fin M.count))
    (hF : F' = F \ ⋃ i ∈ D, M.components i) :
    ∃ f : Fin M'.count ↪ Fin M.count,
      (∀ j, f j ∉ D) ∧ ∀ j, M'.components j = M.components (f j) := by
  classical
  have hsub : F' ⊆ F := hF.subset.trans sdiff_subset
  have hkeep (i : Fin M.count) (hi : i ∉ D) : M.components i ⊆ F' := by
    intro x hx
    rw [hF]
    refine ⟨(M.component i).2.2.1 hx, ?_⟩
    rintro ⟨_, ⟨j, rfl⟩, hj⟩
    obtain ⟨_, ⟨hjD, rfl⟩, hxj⟩ := hj
    have hij : i ≠ j := fun hij => hi (hij.symm ▸ hjD)
    exact disjoint_left.mp (M.disjoint hij) hx hxj
  have hex (j : Fin M'.count) :
      ∃ i : Fin M.count, i ∉ D ∧ M'.components j = M.components i := by
    obtain ⟨x, hx⟩ := (M'.component j).2.1.nonempty
    have hxF' := (M'.component j).2.2.1 hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (M.cover.symm.subset (hsub hxF'))
    have hi : i ∉ D := by
      intro hi
      exact (hF.subset hxF').2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxi⟩⟩)
    refine ⟨i, hi, Subset.antisymm ?_ ?_⟩
    · rw [← (M'.component j).2.2.2 x hx, ← (M.component i).2.2.2 x hxi]
      exact connectedComponentIn_mono x hsub
    · rw [← (M'.component j).2.2.2 x hx]
      exact (M.component i).2.1.isPreconnected.subset_connectedComponentIn hxi (hkeep i hi)
  choose f hfD hf using hex
  have hfi : Function.Injective f := by
    intro i j hij
    obtain ⟨x, hx⟩ := (M'.component i).2.1.nonempty
    have hxj : x ∈ M'.components j := by rw [hf j, ← hij, ← hf i]; exact hx
    by_contra hne
    exact disjoint_left.mp (M'.disjoint hne) hx hxj
  exact ⟨⟨f, hfi⟩, hfD, hf⟩

theorem count_lt_of_component_deletion
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N N' F F' : Set X}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel e N' F')
    (D : Set (Fin M.count)) (hne : D.Nonempty)
    (hF : F' = F \ ⋃ i ∈ D, M.components i) :
    M'.count < M.count := by
  obtain ⟨f, hfD, _⟩ := M.exists_component_embedding_of_deletion M' D hF
  have hfns : ¬ Function.Surjective f := by
    intro hs
    obtain ⟨i, hi⟩ := hne
    obtain ⟨j, hj⟩ := hs i
    exact hfD j (hj.symm ▸ hi)
  simpa only [Fintype.card_fin] using
    Fintype.card_lt_of_injective_not_surjective f f.injective hfns

theorem nonspherical_of_component_deletion
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N N' F F' : Set X}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel e N' F')
    (D : Set (Fin M.count))
    (hF : F' = F \ ⋃ i ∈ D, M.components i)
    (hno : ∀ i, ¬ Nonempty (ChartwisePLSphere e (M.components i))) :
    ∀ j, ¬ Nonempty (ChartwisePLSphere e (M'.components j)) := by
  obtain ⟨f, _, hf⟩ := M.exists_component_embedding_of_deletion M' D hF
  intro j
  rw [hf j]
  exact hno (f j)

theorem nontrivial_groups_of_component_deletion
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N N' F F' : Set X}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel e N' F')
    (D : Set (Fin M.count))
    (hF : F' = F \ ⋃ i ∈ D, M.components i)
    (hgroups : ∀ i (x : M.components i), Nontrivial (FundamentalGroup (M.components i) x)) :
    ∀ j (x : M'.components j), Nontrivial (FundamentalGroup (M'.components j) x) := by
  obtain ⟨f, _, hf⟩ := M.exists_component_embedding_of_deletion M' D hF
  intro j
  rw [hf j]
  exact hgroups (f j)

theorem exists_component_embedding_of_closed_excision
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N N' F F' D : Set X}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel e N' F')
    (hD : IsClosed D) (hfront : Disjoint F (frontier D))
    (hF : F' = F \ D) :
    ∃ f : Fin M'.count ↪ Fin M.count,
      ∀ j, M'.components j = M.components (f j) := by
  classical
  let J : Set (Fin M.count) := {i | M.components i ⊆ D}
  have hdelete : F' = F \ ⋃ i ∈ J, M.components i := by
    rw [hF]
    ext x
    constructor
    · rintro ⟨hxF, hxD⟩
      refine ⟨hxF, ?_⟩
      intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨hiJ, hxi⟩ := mem_iUnion.mp hi
      exact hxD (hiJ hxi)
    · rintro ⟨hxF, hx⟩
      refine ⟨hxF, ?_⟩
      intro hxD
      obtain ⟨i, hxi⟩ := mem_iUnion.mp (M.cover.symm.subset hxF)
      rcases Poincare.Topology.subset_interior_or_disjoint_of_disjoint_frontier
        (M.component i).2.1.isPreconnected hD
        (hfront.mono_left (M.component i).2.2.1) with hin | hout
      · exact hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hin.trans interior_subset, hxi⟩⟩)
      · exact disjoint_left.mp hout hxi hxD
  obtain ⟨f, _, hf⟩ := M.exists_component_embedding_of_deletion M' J hdelete
  exact ⟨f, hf⟩



theorem exists_retained_model_after_closed_excision
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N F D : Set X}
    (M : FrontierResidualModel e N F) (hD : IsClosed D)
    (hfront : Disjoint F (frontier D)) (hne : (F \ D).Nonempty) :
    ∃ Mnew : FrontierResidualModel e N (F \ D),
      Mnew.count ≤ M.count ∧ ((F ∩ D).Nonempty → Mnew.count < M.count) ∧
      ∃ f : Fin Mnew.count ↪ Fin M.count,
        ∀ j, Mnew.components j = M.components (f j) := by
  have heq : F \ interior D = F \ D := by
    ext x
    constructor
    · rintro ⟨hxF, hx⟩
      refine ⟨hxF, ?_⟩
      intro hxD
      exact disjoint_left.mp hfront hxF
        (by rw [frontier, hD.closure_eq]; exact ⟨hxD, hx⟩)
    · exact fun hx => ⟨hx.1, fun hi => hx.2 (interior_subset hi)⟩
  have hh := M.exists_model_after_closed_excision hD hfront (heq.symm ▸ hne)
  rw [heq] at hh
  obtain ⟨Mnew, _, hle, hlt⟩ := hh
  exact ⟨Mnew, hle, hlt, M.exists_component_embedding_of_closed_excision Mnew hD hfront rfl⟩

end PoincareConjecture.M76.FrontierResidualModel
