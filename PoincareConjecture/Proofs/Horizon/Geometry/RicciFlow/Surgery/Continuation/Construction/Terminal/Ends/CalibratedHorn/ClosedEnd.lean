import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.HalfNormalization








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {U : Set M}

theorem isClosed_closedTail_of_isClosed_closedTail
    (Q : OpenCylinderModel U) (side : Bool)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hclosed : IsClosed (Q.closedTail side a)) : IsClosed (Q.closedTail side b) := by
  let K := Q.coordinate '' (univ ×ˢ Icc (min a b) (max a b))
  have hK : IsCompact K := Q.isCompact_coordinate_slab
    (lt_min ha.1 hb.1) (max_lt ha.2 hb.2)
  have hKU : K ⊆ U := Q.coordinate_slab_subset
    (lt_min ha.1 hb.1) (max_lt ha.2 hb.2)
  have hAU : Q.closedTail side a ⊆ U :=
    fun _ hx => ((Q.mem_closedTail_iff side ha).mp hx).1
  apply Q.isClosed_closedTail_of_subset side hb (hclosed.union hK.isClosed)
    (union_subset hAU hKU)
  intro x hx
  by_cases hxa : x ∈ Q.closedTail side a
  · exact Or.inl hxa
  · right
    have hx' := (Q.mem_closedTail_iff side hb).mp hx
    have hnot : ¬ (if side then a ≤ (Q.inverse x).2 else (Q.inverse x).2 ≤ a) :=
      fun h => hxa ((Q.mem_closedTail_iff side ha).mpr ⟨hx'.1, h⟩)
    refine ⟨Q.inverse x, ⟨mem_univ _, ?_⟩, Q.right_inverse hx'.1⟩
    cases side
    · exact ⟨(min_le_left _ _).trans (le_of_lt (lt_of_not_ge hnot)),
        hx'.2.trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans hx'.2,
        (le_of_lt (lt_of_not_ge hnot)).trans (le_max_left _ _)⟩



theorem exists_closedHalf_of_closedTail
    (Q P : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hclosed : IsClosed (Q.closedTail side a)) :
    ∃ newSide : Bool, IsClosed (P.closedTail newSide (1 / 2)) ∧
      ∃ b ∈ Ioo (0 : ℝ) 1, Q.tail side b ⊆ P.closedTail newSide (1 / 2) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hmidU : P.middleSphere ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact P.coordinate_mem ⟨mem_univ _, hz.2 ▸ hhalf⟩
  obtain ⟨δ, hδ, hlow, hhigh, _, _⟩ :=
    Q.exists_tails_disjoint_of_isCompact (P.isCompact_axial_sphere hhalf) hmidU
  have hδone : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, hδ.2.trans (by norm_num)⟩
  have hδcomp : 1 - δ ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hδ.1, hδ.2]
  let c : ℝ := if side then δ else 1 - δ
  have hc : c ∈ Ioo (0 : ℝ) 1 := by
    cases side
    · exact hδcomp
    · exact hδone
  have hmid : P.middleSphere ⊆ Q.closedTail side c := by
    intro x hx
    apply (Q.mem_closedTail_iff side hc).mpr
    refine ⟨hmidU hx, ?_⟩
    cases side
    · exact le_of_not_gt (fun h => disjoint_left.mp hhigh
        ((Q.mem_tail_iff true hδcomp).mpr ⟨hmidU hx, h⟩) hx)
    · exact le_of_not_gt (fun h => disjoint_left.mp hlow
        ((Q.mem_tail_iff false hδone).mpr ⟨hmidU hx, h⟩) hx)
  obtain ⟨newSide, hnew, _, hcapture⟩ := Q.exists_closedHalf_inside_closedTail P side hc
    (Q.isClosed_closedTail_of_isClosed_closedTail side ha hc hclosed) hmid
  exact ⟨newSide, hnew, hcapture⟩

end PoincareConjecture.OpenCylinderModel
