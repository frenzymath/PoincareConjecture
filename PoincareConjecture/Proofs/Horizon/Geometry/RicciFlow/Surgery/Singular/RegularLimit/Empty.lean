import PoincareConjecture.Definitions.M31SingularRegularLimit

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace GeneralizedFlowExtension

noncomputable def refl (F : GeneralizedRicciFlowData.{u}) (T : ℝ) :
    GeneralizedFlowExtension F T where
  extended := F
  times_subset := Set.subset_union_left
  old_times := Set.Subset.rfl
  forward := fun _ _ => id
  inverse := fun _ _ => id
  forward_smooth := fun _ _ => contMDiff_id
  inverse_smooth := fun _ _ => contMDiff_id
  left_inverse := fun _ _ _ => rfl
  right_inverse := fun _ _ _ => rfl
  metric_pullback := by intros; simp
  scalar_pullback := by intros; rfl
  spacetime_forward := id
  spacetime_time := fun _ => rfl
  spacetime_slices := fun _ _ _ => rfl
  spacetime_openEmbedding := Topology.IsOpenEmbedding.id
  spacetime_image := by
    ext p
    simp only [Set.range_id, Set.mem_univ, Set.mem_ofPred_eq, true_iff]
    exact (F.slice_nonempty_iff p.1).mp ⟨p.2⟩
  vertical_compatibility := by
    intro b t ht x
    exact ⟨b, x, 1, zero_lt_one, fun s hs _ => ⟨hs, rfl⟩⟩

end GeneralizedFlowExtension

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

noncomputable def regularLimitOfEmpty (H : SingularTimeAssumptions F T M)
    (hempty : H.reference.regularLimitSet = ∅) :
    RepairedSingularRegularLimitData H := by
  letI : IsEmpty (F.slice T).carrier :=
    ⟨fun x => H.terminal_not_in_interval ((F.slice_nonempty_iff T).mp ⟨x⟩)⟩
  letI : IsEmpty ((GeneralizedFlowExtension.refl F T).extended.slice T).carrier :=
    inferInstanceAs (IsEmpty (F.slice T).carrier)
  let i : (F.slice T).carrier → M := isEmptyElim
  let G : Set.Ioc H.reference.tMinus T × (F.slice T).carrier → F.point :=
    fun p => isEmptyElim p.2
  refine {
    regular_open := by rw [hempty]; exact isOpen_empty
    regular_eventually_bounded := by simp [hempty]
    extension := GeneralizedFlowExtension.refl F T
    terminal_source := i
    terminal_source_image := (Set.range_eq_empty i).trans hempty.symm
    terminal_source_openEmbedding := Topology.IsOpenEmbedding.of_isEmpty i
    terminal_source_smooth := by intro x; exact isEmptyElim x
    terminal_source_regular := by intro x; exact isEmptyElim x
    terminal_time_iff := by simp [GeneralizedFlowExtension.refl, hempty,
      H.terminal_not_in_interval]
    terminal_metric := F.metric T
    terminal_metric_eq := rfl
    terminal_scalar := (F.connection T).scalarCurvature
    terminal_scalar_eq := rfl
    scalar_lower := ⟨0, fun x => isEmptyElim x⟩
    scalar_proper := by
      intro K _
      change IsCompact ((F.connection T).scalarCurvature ⁻¹' K)
      rw [Set.eq_empty_of_isEmpty ((F.connection T).scalarCurvature ⁻¹' K)]
      exact isCompact_empty
    metric_limit_on_compacts := by intro q; exact isEmptyElim q
    gluing_map := G
    gluing_time := fun p => isEmptyElim p.2
    gluing_old := fun _ _ _ x => isEmptyElim x
    gluing_terminal := fun x => isEmptyElim x
    gluing_openEmbedding := Topology.IsOpenEmbedding.of_isEmpty G
    gluing_cover := by
      change Set.range (id : F.point → F.point) ∪ Set.range G = Set.univ
      rw [Set.range_id, Set.univ_union]
    gluing_vertical_compatibility := fun _ _ x => isEmptyElim x
    component_paths := fun x => isEmptyElim x
    end_tube := fun K => isEmptyElim K.basepoint
    canonical_neighborhood := fun x => isEmptyElim x
  }

end SingularTimeAssumptions

end PoincareConjecture
