import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.ClosingCapTail
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary














set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem closing_sides_accumulate_outside_tube (C D : CapCertificate g)
    {U K : Set M} (hU : IsOpen U) (hend : C.end_neck.carrier ⊆ U)
    (hfirst : Disjoint C.closed_core U)
    (hDC : Disjoint D.closed_core C.carrier)
    (hCD : Disjoint C.closed_core D.carrier)
    (hK : IsClosed K) (hKD : K ⊆ D.carrier)
    (hcore : D.closed_core ⊆ interior K)
    (hencounter : (frontier (C.carrier ∪ U) ∩ D.core).Nonempty) :
    (closure (U ∩ interior K) \ U).Nonempty ∧
      (closure (U \ K) \ U).Nonempty := by
  obtain ⟨x, hxfront, hxcore⟩ := hencounter
  have hxout : x ∉ U := fun hx =>
    ((C.carrier_open.union hU).frontier_eq ▸ hxfront).2 (Or.inr hx)
  have hxcl : x ∈ closure U := by
    have h := frontier_subset_closure hxfront
    rw [closure_union] at h
    refine h.resolve_left ?_
    intro hxC
    obtain ⟨y, hyD, hyC⟩ := mem_closure_iff.mp hxC D.core D.isOpen_core hxcore
    exact disjoint_left.mp hDC (D.core_subset_closed_core hyD) hyC
  have hxK := hcore (D.core_subset_closed_core hxcore)
  have hxside : x ∈ closure (U ∩ interior K) := by
    apply mem_closure_iff.mpr
    intro V hV hxV
    obtain ⟨y, hy, hyU⟩ := mem_closure_iff.mp hxcl (V ∩ interior K)
      (hV.inter isOpen_interior) ⟨hxV, hxK⟩
    exact ⟨y, hy.1, hyU, hy.2⟩
  have hcB : C.boundary_neck.center ∈ C.boundary_sphere :=
    C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
  have hcCore := C.boundary_subset_closed_core hcB
  have hcout : C.boundary_neck.center ∉ U := fun hc =>
    disjoint_left.mp hfirst hcCore hc
  have hcK : C.boundary_neck.center ∉ K := fun hc =>
    disjoint_left.mp hCD hcCore (hKD hc)
  have hccl : C.boundary_neck.center ∈ closure U :=
    closure_mono ((C.end_neck.region_subset_carrier _ _).trans hend)
      (C.boundary_subset_negative_end_closure hcB)
  have hcside : C.boundary_neck.center ∈ closure (U \ K) := by
    apply mem_closure_iff.mpr
    intro V hV hcV
    obtain ⟨y, hy, hyU⟩ := mem_closure_iff.mp hccl (V ∩ Kᶜ)
      (hV.inter hK.isOpen_compl) ⟨hcV, hcK⟩
    exact ⟨y, hy.1, hyU, hy.2⟩
  exact ⟨⟨x, hxside, hxout⟩, ⟨C.boundary_neck.center, hcside, hcout⟩⟩



theorem exists_second_cap_essential_slice_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), D.epsilon ≤ ε₀ →
          ∀ {U : Set M}, IsOpen U → C.end_neck.carrier ⊆ U →
            Disjoint C.closed_core U → Disjoint D.closed_core C.carrier →
            Disjoint C.closed_core D.carrier →
            IsCompact (C.carrier ∪ U ∪ D.carrier) →
            (frontier (C.carrier ∪ U) ∩ D.core).Nonempty →
            ∃ s ∈ Ioo 0 D.epsilon⁻¹, ∃ η : ℝ, 0 < η ∧ 0 < s - η ∧
              s + η < D.epsilon⁻¹ ∧ D.end_neck.region (s - η) (s + η) ⊆ U ∧
              D.end_neck.region (s - η) D.epsilon⁻¹ ⊆ U ∧
              let K := D.closed_core ∪ closure (D.end_neck.region (-D.epsilon⁻¹) s)
              IsCompact K ∧ K ⊆ D.carrier ∧ D.closed_core ⊆ interior K ∧
                frontier K = range (fun q : UnitTwoSphere =>
                  D.end_neck.coordinate_map (q, s)) ∧
                D.carrier ∩ U = (U ∩ interior K) ∪
                  D.end_neck.region (s - η) D.epsilon⁻¹ ∧
                (U ∩ interior K) ∩ D.end_neck.region (s - η) D.epsilon⁻¹ =
                  D.end_neck.region (s - η) s ∧
                ∀ L : Set M, IsCompact L → L ⊆ U →
                  ¬ U ∩ interior K ⊆ L ∧ ¬ U \ K ⊆ L := by
  obtain ⟨ε₁, hε₁, hsmall, htail⟩ :=
    exists_second_cap_tail_of_compact_closing_threshold.{u}
  obtain ⟨ε₂, hε₂, -, htrunc⟩ := exists_truncated_core_domain_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε U hU hend hfirst hDC hCD hcompact hencounter
  obtain ⟨a, ha, htail⟩ := htail C D (hε.trans (min_le_left _ _)) hU hend hCD hcompact
  let s := (a + D.epsilon⁻¹) / 2
  let η := (D.epsilon⁻¹ - a) / 4
  have hs : s ∈ Ioo 0 D.epsilon⁻¹ := by dsimp [s]; constructor <;> linarith [ha.1, ha.2]
  have hη : 0 < η := by dsimp [η]; linarith [ha.2]
  have hal : a < s - η := by dsimp [s, η]; linarith [ha.2]
  have hu : s + η < D.epsilon⁻¹ := by dsimp [s, η]; linarith [ha.2]
  obtain ⟨hK, hKD, hinterior, hfront, -, hcore⟩ := htrunc D
    (hε.trans (min_le_right _ _)) s
    ⟨(neg_lt_zero.mpr (inv_pos.mpr D.epsilon_pos)).trans hs.1, hs.2⟩
  have htail' : D.end_neck.region (s - η) D.epsilon⁻¹ ⊆ U := by
    intro x hx
    exact htail ⟨hx.1, hal.trans hx.2.1, hx.2.2⟩
  refine ⟨s, hs, η, hη, ha.1.trans hal, hu, ?_, htail',
    hK, hKD, hcore, hfront, ?_, ?_, ?_⟩
  · intro x hx
    exact htail ⟨hx.1, hal.trans hx.2.1, hx.2.2.trans hu⟩
  · rw [hinterior]
    apply Subset.antisymm
    · rintro x ⟨hxD, hxU⟩
      rcases D.carrier_eq_closed_core_union_end ▸ hxD with hc | he
      · exact Or.inl ⟨hxU, Or.inl hc⟩
      · have hh := (D.end_neck.coordinate_inverse_mem x he).2
        rw [D.end_neck_epsilon] at hh
        by_cases hxs : (D.end_neck.coordinate_inverse x).2 < s
        · exact Or.inl ⟨hxU, Or.inr ⟨he, hh.1, hxs⟩⟩
        · exact Or.inr ⟨he, by linarith [le_of_not_gt hxs], hh.2⟩
    · rintro x (⟨hxU, hc | he⟩ | he)
      · exact ⟨D.closed_core_subset_carrier hc, hxU⟩
      · exact ⟨D.end_neck_subset he.1, hxU⟩
      · exact ⟨D.end_neck_subset he.1, htail' he⟩
  · rw [hinterior]
    apply Subset.antisymm
    · rintro x ⟨⟨-, hc | he⟩, ht⟩
      · exact (disjoint_left.mp D.disjoint_closed_core_end hc ht.1).elim
      · exact ⟨he.1, ht.2.1, he.2.2⟩
    · intro x hx
      have hh := (D.end_neck.coordinate_inverse_mem x hx.1).2
      rw [D.end_neck_epsilon] at hh
      have ht : x ∈ D.end_neck.region (s - η) D.epsilon⁻¹ :=
        ⟨hx.1, hx.2.1, hh.2⟩
      exact ⟨⟨htail' ht, Or.inr ⟨hx.1, hh.1, hx.2.2⟩⟩, ht⟩
  · have hsides := C.closing_sides_accumulate_outside_tube D hU hend hfirst hDC hCD
      hK.isClosed hKD hcore hencounter
    intro L hL hLU
    constructor
    · intro hsub
      obtain ⟨x, hxcl, hxout⟩ := hsides.1
      exact hxout (hLU (hL.isClosed.closure_eq ▸ closure_mono hsub hxcl))
    · intro hsub
      obtain ⟨x, hxcl, hxout⟩ := hsides.2
      exact hxout (hLU (hL.isClosed.closure_eq ▸ closure_mono hsub hxcl))

end PoincareConjecture.CapCertificate
