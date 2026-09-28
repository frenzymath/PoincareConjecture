import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.SourcePhaseResidualModels










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.FrontierResidualModel

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {N F : Set X}


def transportPhase (M : FrontierResidualModel e N F) {Fnew : Set X} (h : F = Fnew) :
    FrontierResidualModel e N Fnew := h ▸ M

@[simp] theorem transportPhase_complexity (M : FrontierResidualModel e N F)
    {Fnew : Set X} (h : F = Fnew) :
    (M.transportPhase h).complexity = M.complexity := by cases h; rfl

@[simp] theorem transportPhase_count (M : FrontierResidualModel e N F)
    {Fnew : Set X} (h : F = Fnew) :
    (M.transportPhase h).count = M.count := by cases h; rfl



def retain (M : FrontierResidualModel e N F) {m : ℕ}
    (keep : Fin m ↪ Fin M.count) (hm : 0 < m) :
    FrontierResidualModel e N (⋃ i, M.components (keep i)) where
  vertices := M.vertices
  coordinates := M.coordinates
  complex := M.complex
  map := M.map
  count := m
  pick := keep.trans M.pick
  components := fun i => M.components (keep i)
  residual := fun i => M.residual (keep i)
  coordinates_continuous := M.coordinates_continuous
  coordinates_injective := M.coordinates_injective
  coordinates_pl := M.coordinates_pl
  finite := M.finite
  dimension := M.dimension
  pl := M.pl
  injective := M.injective
  inverse := M.inverse
  positive := hm
  images := fun i => M.images (keep i)
  cover := rfl
  disjoint := fun i j hij => M.disjoint (fun h => hij (keep.injective h))
  component := by
    intro i
    have hi : M.components (keep i) ⊆ ⋃ j, M.components (keep j) :=
      subset_iUnion (fun j : Fin m => M.components (keep j)) i
    have hsub : (⋃ j, M.components (keep j)) ⊆ F := by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact (M.component (keep j)).2.2.1 hj
    refine ⟨(M.component (keep i)).1, (M.component (keep i)).2.1, hi, ?_⟩
    intro x hx
    apply Subset.antisymm
    · exact ((connectedComponentIn_mono x hsub).trans
        ((M.component (keep i)).2.2.2 x hx).subset)
    · exact (M.component (keep i)).2.1.isPreconnected.subset_connectedComponentIn hx hi
  euler := fun i => M.euler (keep i)
  zero_sphere := fun i => M.zero_sphere (keep i)

theorem retain_complexity_le (M : FrontierResidualModel e N F) {m : ℕ}
    (keep : Fin m ↪ Fin M.count) (hm : 0 < m) :
    (M.retain keep hm).complexity ≤ M.complexity := by
  classical
  change (∑ i : Fin m, (M.residual (keep i) - 1)) ≤
    ∑ i : Fin M.count, (M.residual i - 1)
  calc
    (∑ i : Fin m, (M.residual (keep i) - 1)) =
        ∑ i ∈ Finset.univ.map keep, (M.residual i - 1) := by rw [Finset.sum_map]
    _ ≤ ∑ i : Fin M.count, (M.residual i - 1) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem retain_count_le (M : FrontierResidualModel e N F) {m : ℕ}
    (keep : Fin m ↪ Fin M.count) (hm : 0 < m) :
    (M.retain keep hm).count ≤ M.count := by
  change m ≤ M.count
  simpa using Fintype.card_le_of_injective keep keep.injective



theorem exists_retained_finset_model (M : FrontierResidualModel e N F)
    (J : Finset (Fin M.count)) (hJ : J.Nonempty) :
    ∃ Mnew : FrontierResidualModel e N (⋃ j ∈ J, M.components j),
      Mnew.count = J.card ∧ Mnew.complexity ≤ M.complexity := by
  classical
  let keep : Fin J.card ↪ Fin M.count :=
    ⟨fun j => J.equivFin.symm j,
      fun j k h => J.equivFin.symm.injective (Subtype.ext h)⟩
  have hkeep : (⋃ j, M.components (keep j)) = ⋃ j ∈ J, M.components j := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨keep j, mem_iUnion.mpr ⟨(J.equivFin.symm j).property, hj⟩⟩
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      obtain ⟨hjJ, hxj⟩ := mem_iUnion.mp hj
      refine mem_iUnion.mpr ⟨J.equivFin ⟨j, hjJ⟩, ?_⟩
      have hp : keep (J.equivFin ⟨j, hjJ⟩) = j :=
        congrArg Subtype.val (J.equivFin.symm_apply_apply ⟨j, hjJ⟩)
      exact hp.symm ▸ hxj
  have hm : 0 < J.card := Finset.card_pos.mpr hJ
  let Mnew := M.retain keep hm
  have hcount : Mnew.count = J.card := rfl
  have hcomplexity : Mnew.complexity ≤ M.complexity := M.retain_complexity_le keep hm
  exact hkeep ▸ ⟨Mnew, hcount, hcomplexity⟩

end PoincareConjecture.M76.FrontierResidualModel
