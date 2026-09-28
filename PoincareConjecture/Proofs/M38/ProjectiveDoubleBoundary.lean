import PoincareConjecture.Proofs.M38.ProjectiveTopology

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38

variable {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]

theorem puncturedProjectiveCover_connected {p : RealProjectiveThree} {U : Set Q}
    (C : StandardPuncturedProjectiveCover Q p U) : IsConnected U := by
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective p
  have hpre : IsConnected {z : UnitThreeSphere | Quotient.mk' z ≠ Quotient.mk' a} := by
    change IsConnected ((Quotient.mk' : UnitThreeSphere → RealProjectiveThree) ⁻¹'
      {q | q ≠ Quotient.mk' a})
    rw [projective_puncture_preimage]
    exact three_sphere_antipodal_compl_connected a
  rw [← C.image_eq]
  exact hpre.image C.cover C.local_diffeomorph.contMDiffOn.continuousOn

variable (C : SmoothProjectiveDoubleModel Q)

theorem projectiveDouble_regions_connected :
    IsConnected C.first_region ∧ IsConnected C.second_region :=
  ⟨puncturedProjectiveCover_connected C.first_model,
    puncturedProjectiveCover_connected C.second_model⟩

theorem projectiveDouble_central_continuous :
    Continuous (fun z : UnitTwoSphere => C.collar (z, 0)) := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun z : UnitTwoSphere => C.collar (z, 0)) := by
    intro z
    apply (C.collar_local_diffeomorph ⟨(z, 0), by simp⟩).contMDiffAt.comp z
    exact (contMDiff_id.prodMk contMDiff_const) z
  exact hs.continuous

theorem projectiveDouble_central_range :
    Set.range (fun z : UnitTwoSphere => C.collar (z, 0)) = C.sphere := by
  rw [← C.collar_sphere]
  apply Set.Subset.antisymm
  · rintro y ⟨z, rfl⟩
    exact ⟨(z, 0), by simp, rfl⟩
  · rintro y ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    subst s
    exact Set.mem_range_self z

theorem projectiveDouble_sphere_compact_connected :
    IsCompact C.sphere ∧ IsConnected C.sphere := by
  let : ConnectedSpace UnitTwoSphere :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  rw [← projectiveDouble_central_range C]
  exact ⟨isCompact_range (projectiveDouble_central_continuous C),
    isConnected_range (projectiveDouble_central_continuous C)⟩

theorem projectiveDouble_sphere_subset_closures :
    C.sphere ⊆ closure C.first_region ∩ closure C.second_region := by
  intro y hy
  rw [← projectiveDouble_central_range C] at hy
  obtain ⟨z, rfl⟩ := hy
  have hside {a b : ℝ} (hab : a < b) (ha : -1 < a) (hb : b < 1)
      (hzero : a ≤ 0 ∧ 0 ≤ b) {U : Set Q}
      (hsub : C.collar '' (Set.univ ×ˢ Set.Ioo a b) ⊆ U) :
      C.collar (z, 0) ∈ closure U := by
    let V : Set RoundCylinderSpace := Set.univ ×ˢ Set.Ioo a b
    have hclosure : closure V = Set.univ ×ˢ Set.Icc a b := by
      dsimp only [V]
      rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
    have hdom : closure V ⊆ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
      rw [hclosure]
      intro p hp
      exact ⟨hp.1, ha.trans_le hp.2.1, hp.2.2.trans_lt hb⟩
    have hmem : (z, 0) ∈ closure V := by
      rw [hclosure]
      exact ⟨Set.mem_univ z, hzero⟩
    apply closure_mono hsub
    exact (C.collar_local_diffeomorph.contMDiffOn.continuousOn.mono hdom).image_closure
      (Set.mem_image_of_mem _ hmem)
  constructor
  · apply hside (a := -(1 / 2)) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    apply Set.Subset.trans (Set.image_mono ?_) C.collar_negative
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩
  · apply hside (a := 0) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    apply Set.Subset.trans (Set.image_mono ?_) C.collar_positive
    intro p hp
    exact ⟨hp.1, hp.2.1, by linarith [hp.2.2]⟩

theorem projectiveDouble_side_complements :
    C.first_region ∪ C.sphere = C.second_regionᶜ ∧
      C.second_region ∪ C.sphere = C.first_regionᶜ := by
  have hcover (y : Q) : y ∈ C.first_region ∪ C.second_region ∪ C.sphere := by
    rw [C.cover]
    exact Set.mem_univ y
  constructor
  · ext y
    constructor
    · rintro (hy | hy) hsecond
      · exact Set.disjoint_left.mp C.disjoint hy hsecond
      · exact Set.disjoint_left.mp C.sphere_disjoint hy (Or.inr hsecond)
    · intro hy
      rcases hcover y with (hfirst | hsecond) | hsphere
      · exact Or.inl hfirst
      · exact (hy hsecond).elim
      · exact Or.inr hsphere
  · ext y
    constructor
    · rintro (hy | hy) hfirst
      · exact Set.disjoint_left.mp C.disjoint hfirst hy
      · exact Set.disjoint_left.mp C.sphere_disjoint hy (Or.inl hfirst)
    · intro hy
      rcases hcover y with (hfirst | hsecond) | hsphere
      · exact (hy hfirst).elim
      · exact Or.inl hsecond
      · exact Or.inr hsphere

theorem projectiveDouble_region_closures :
    closure C.first_region = C.first_region ∪ C.sphere ∧
      closure C.second_region = C.second_region ∪ C.sphere := by
  constructor
  · have hclosed : IsClosed (C.first_region ∪ C.sphere) := by
      rw [(projectiveDouble_side_complements C).1]
      exact C.second_open.isClosed_compl
    apply (closure_minimal Set.subset_union_left hclosed).antisymm
    rintro y (hy | hy)
    · exact subset_closure hy
    · exact (projectiveDouble_sphere_subset_closures C hy).1
  · have hclosed : IsClosed (C.second_region ∪ C.sphere) := by
      rw [(projectiveDouble_side_complements C).2]
      exact C.first_open.isClosed_compl
    apply (closure_minimal Set.subset_union_left hclosed).antisymm
    rintro y (hy | hy)
    · exact subset_closure hy
    · exact (projectiveDouble_sphere_subset_closures C hy).2

theorem projectiveDouble_region_frontiers :
    frontier C.first_region = C.sphere ∧ frontier C.second_region = C.sphere := by
  constructor
  · rw [frontier, C.first_open.interior_eq, (projectiveDouble_region_closures C).1]
    ext y
    constructor
    · rintro ⟨hy | hy, hnot⟩
      · exact (hnot hy).elim
      · exact hy
    · intro hy
      exact ⟨Or.inr hy, fun hfirst =>
        Set.disjoint_left.mp C.sphere_disjoint hy (Or.inl hfirst)⟩
  · rw [frontier, C.second_open.interior_eq, (projectiveDouble_region_closures C).2]
    ext y
    constructor
    · rintro ⟨hy | hy, hnot⟩
      · exact (hnot hy).elim
      · exact hy
    · intro hy
      exact ⟨Or.inr hy, fun hsecond =>
        Set.disjoint_left.mp C.sphere_disjoint hy (Or.inr hsecond)⟩

theorem projectiveDouble_closed_sides_compact :
    IsCompact (closure C.first_region) ∧ IsCompact (closure C.second_region) := by
  let : CompactSpace Q := isCompact_univ_iff.mp C.compact
  exact ⟨isClosed_closure.isCompact, isClosed_closure.isCompact⟩

end PoincareConjecture.M38
