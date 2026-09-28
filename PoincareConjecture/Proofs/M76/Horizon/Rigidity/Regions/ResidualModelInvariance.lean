import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.SourcePhaseResidualModels
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionGenusDecrease

set_option autoImplicit false
open Set Geometry
open scoped BigOperators

namespace PoincareConjecture.M76.FrontierResidualModel

local notation "V3" => (Fin 3 → ℝ)

theorem exists_component_matching
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N N' F : Set X}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel e N' F) :
    ∃ r : Fin M.count ≃ Fin M'.count,
      ∀ i, M.components i = M'.components (r i) := by
  classical
  have hex (i : Fin M.count) : ∃ j, M.components i = M'.components j := by
    obtain ⟨x, hx⟩ := (M.component i).2.1.nonempty
    obtain ⟨j, hj⟩ := mem_iUnion.mp (M'.cover.symm.subset ((M.component i).2.2.1 hx))
    exact ⟨j, ((M.component i).2.2.2 x hx).symm.trans ((M'.component j).2.2.2 x hj)⟩
  choose f hf using hex
  have hi : Function.Injective f := by
    intro i j hij
    obtain ⟨x, hx⟩ := (M.component i).2.1.nonempty
    have hxj : x ∈ M.components j := by rw [hf j, ← hij, ← hf i]; exact hx
    by_contra hne
    exact disjoint_left.mp (M.disjoint hne) hx hxj
  have hs : Function.Surjective f := by
    intro j
    obtain ⟨x, hx⟩ := (M'.component j).2.1.nonempty
    obtain ⟨i, hi⟩ := mem_iUnion.mp (M.cover.symm.subset ((M'.component j).2.2.1 hx))
    refine ⟨i, ?_⟩
    by_contra hne
    exact disjoint_left.mp (M'.disjoint hne) ((hf i).subset hi) hx
  exact ⟨Equiv.ofBijective f ⟨hi, hs⟩, hf⟩

theorem residual_eq_of_component_eq
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N N' F F' : Set X}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel e N' F')
    (hF' : F' ⊆ N') (i : Fin M.count) (j : Fin M'.count)
    (hij : M.components i = M'.components j) : M.residual i = M'.residual j := by
  classical
  let A := M.complex.edgeComponentComplex (M.pick i)
  let A' := M'.complex.edgeComponentComplex (M'.pick j)
  have hA : A.faces.Finite := M.finite.subset (M.complex.edgeComponentComplex_le _)
  have hA' : A'.faces.Finite := M'.finite.subset (M'.complex.edgeComponentComplex_le _)
  have hsub : A.space ⊆ M.complex.space :=
    SimplicialComplex.space_subset_of_le (M.complex.edgeComponentComplex_le _)
  have hsub' : A'.space ⊆ M'.complex.space :=
    SimplicialComplex.space_subset_of_le (M'.complex.edgeComponentComplex_le _)
  have hEuler := original_component_surfaceEulerCount_eq A A' hA hA'
    (fun t ht => M.dimension t (M.complex.edgeComponentComplex_le _ ht))
    (fun t ht => M'.dimension t (M'.complex.edgeComponentComplex_le _ ht))
    M.map M'.map M'.coordinates (M.pl.restrict_finite A hA hsub)
    (M.injective.mono hsub) (M.images i).symm
    ((M'.images j).symm.trans hij.symm) M'.coordinates_pl
    (M'.coordinates_injective.mono (hij.subset.trans ((M'.component j).2.2.1.trans hF')))
    (fun z hz => M'.inverse z (hsub' hz))
  change (M.complex.edgeComponentComplex (M.pick i)).surfaceEulerCount =
    (M'.complex.edgeComponentComplex (M'.pick j)).surfaceEulerCount at hEuler
  rw [M.euler i, M'.euler j] at hEuler
  omega

theorem complexity_eq_of_same_surface
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N N' F : Set X}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel e N' F)
    (hF : F ⊆ N') : M.complexity = M'.complexity := by
  classical
  obtain ⟨r, hr⟩ := M.exists_component_matching M'
  have hres (i) := M.residual_eq_of_component_eq M' hF i (r i) (hr i)
  unfold complexity
  calc
    (∑ i : Fin M.count, (M.residual i - 1)) =
        ∑ i : Fin M.count, (M'.residual (r i) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hres i]
    _ = ∑ j : Fin M'.count, (M'.residual j - 1) := r.sum_comp (fun j => M'.residual j - 1)

end PoincareConjecture.M76.FrontierResidualModel
