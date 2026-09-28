import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.NeckCap.Cap.Core.Truncation
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.NeckCap.Cap.CoreConnected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Noncompact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.FrontierHeight

open _root_.AddCircle
open _root_.Poincare
open _root_.PoincareConjecture
open _root_.PoincareConjecture.CapCertificate

namespace M38Schoenflies

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in
private theorem core_disjoint_closure_end (C : CapCertificate g) :
    Disjoint C.core (closure C.end_neck.carrier) := by
  rw [disjoint_left]
  intro x hx hcl
  obtain ⟨y, hycore, hyend⟩ := mem_closure_iff.mp hcl C.core (CapCertificate.isOpen_core C) hx
  exact disjoint_left.mp (CapCertificate.disjoint_closed_core_end C)
    ((CapCertificate.core_subset_closed_core C) hycore) hyend

theorem exists_closed_core_disjoint_positive_end_closure_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ a : ℝ, a ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ →
          Disjoint C.closed_core (closure (C.end_neck.region a C.epsilon⁻¹)) := by
  obtain ⟨ε₁, hε₁, hsmall, hcapture⟩ :=
    EpsilonNeck.exists_closure_positive_quarter_subset_closedCollar_of_central_sphere_contact.{u}
  obtain ⟨ε₂, hε₂, _, hnegative⟩ := exists_negative_end_compact_capture_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε
  have hr : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hrad : (0.75 : ℝ) * C.epsilon⁻¹ < C.boundary_neck.epsilon⁻¹ := by
    rw [C.boundary_neck_epsilon]
    linarith
  have hneg := hnegative C (hε.trans (min_le_right _ _))
  have hnegcomp := (C.boundary_neck.isCompact_closedCollar hrad).of_isClosed_subset
    isClosed_closure hneg
  have hnegsub := hneg.trans
    ((C.boundary_neck.closedCollar_subset_carrier hrad).trans C.boundary_neck_subset)
  have hquarter : Disjoint C.closed_core
      (closure (C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹)) := by
    rw [disjoint_left]
    intro x hx hxp
    have hxnotcore : x ∉ C.core := fun hxc => disjoint_left.mp (core_disjoint_closure_end C) hxc
      (closure_mono (C.end_neck.region_subset_carrier _ _) hxp)
    have hxboundary : x ∈ C.boundary_sphere :=
      (CapCertificate.boundary_eq_closed_core_diff_core C).symm ▸ ⟨hx, hxnotcore⟩
    have hpos := hcapture C.end_neck C.boundary_neck
      (C.end_neck_epsilon.trans_le (hε.trans (min_le_left _ _)))
      (C.boundary_neck_epsilon.trans C.end_neck_epsilon.symm)
      ⟨x, by simpa only [C.end_neck_epsilon] using hxp,
        C.boundary_eq_neck_sphere ▸ hxboundary⟩
    rw [C.end_neck_epsilon, C.boundary_neck_epsilon] at hpos
    have hposcomp := (C.boundary_neck.isCompact_closedCollar hrad).of_isClosed_subset
      isClosed_closure hpos
    have hpossub := hpos.trans
      ((C.boundary_neck.closedCollar_subset_carrier hrad).trans C.boundary_neck_subset)
    let K := C.end_neck.coordinate_map ''
      (univ ×ˢ Icc (-C.epsilon⁻¹ / 2) (C.epsilon⁻¹ / 2))
    have hlo : -C.end_neck.epsilon⁻¹ < -C.epsilon⁻¹ / 2 := by
      rw [C.end_neck_epsilon]; linarith
    have hhi : C.epsilon⁻¹ / 2 < C.end_neck.epsilon⁻¹ := by
      rw [C.end_neck_epsilon]; linarith
    have hK := C.end_neck.isCompact_coordinate_slab hlo hhi
    have hKsub : K ⊆ C.carrier := by
      rintro _ ⟨z, hz, rfl⟩
      exact C.end_neck_subset (C.end_neck.coordinate_map_mem
        ⟨mem_univ _, hlo.trans_le hz.2.1, hz.2.2.trans_lt hhi⟩)
    have hcover : C.carrier =
        (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2))) ∪
          (K ∪ closure (C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹)) := by
      apply Subset.antisymm
      · intro y hy
        rcases (CapCertificate.carrier_eq_closed_core_union_end C) ▸ hy with hcore | hend
        · exact Or.inl (Or.inl hcore)
        · have hcoord := (C.end_neck.coordinate_inverse_mem y hend).2
          rw [C.end_neck_epsilon] at hcoord
          by_cases hn : (C.end_neck.coordinate_inverse y).2 < -C.epsilon⁻¹ / 2
          · exact Or.inl (Or.inr (subset_closure ⟨hend, hcoord.1, hn⟩))
          · by_cases hp : C.epsilon⁻¹ / 2 < (C.end_neck.coordinate_inverse y).2
            · exact Or.inr (Or.inr (subset_closure ⟨hend, hp, hcoord.2⟩))
            · exact Or.inr (Or.inl ⟨C.end_neck.coordinate_inverse y,
                ⟨mem_univ _, le_of_not_gt hn, le_of_not_gt hp⟩,
                C.end_neck.coordinate_map_coordinate_inverse hend⟩)
      · exact union_subset (union_subset C.closed_core_subset_carrier hnegsub)
          (union_subset hKsub hpossub)
    exact C.not_isCompact_carrier
      (hcover ▸ (C.closed_core_compact.union hnegcomp).union (hK.union hposcomp))
  intro a ha
  let b := max a (C.epsilon⁻¹ / 2)
  let K := C.end_neck.coordinate_map '' (univ ×ˢ Icc a b)
  have hlo : -C.end_neck.epsilon⁻¹ < a := by simpa only [C.end_neck_epsilon] using ha.1
  have hhi : b < C.end_neck.epsilon⁻¹ := by
    rw [C.end_neck_epsilon]
    exact max_lt ha.2 (by linarith)
  have hK := C.end_neck.isCompact_coordinate_slab hlo hhi
  have hKsub : K ⊆ C.end_neck.carrier := by
    rintro _ ⟨z, hz, rfl⟩
    exact C.end_neck.coordinate_map_mem ⟨mem_univ _, hlo.trans_le hz.2.1, hz.2.2.trans_lt hhi⟩
  have hreg : C.end_neck.region a C.epsilon⁻¹ ⊆
      K ∪ C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹ := by
    intro y hy
    by_cases hp : C.epsilon⁻¹ / 2 < (C.end_neck.coordinate_inverse y).2
    · exact Or.inr ⟨hy.1, hp, hy.2.2⟩
    · exact Or.inl ⟨C.end_neck.coordinate_inverse y,
        ⟨mem_univ _, hy.2.1.le, (le_of_not_gt hp).trans (le_max_right _ _)⟩,
        C.end_neck.coordinate_map_coordinate_inverse hy.1⟩
  rw [disjoint_left]
  intro x hx hxp
  have h := closure_mono hreg hxp
  rw [closure_union, hK.isClosed.closure_eq] at h
  exact h.elim
    (fun hKx => disjoint_left.mp (CapCertificate.disjoint_closed_core_end C) hx (hKsub hKx))
    (fun hQx => disjoint_left.mp hquarter hx hQx)

omit [T2Space M] in
private theorem mem_closure_end_region_iff (C : CapCertificate g) {a b : ℝ}
    (hab : a < b) {x : M} (hx : x ∈ C.end_neck.carrier) :
    x ∈ closure (C.end_neck.region a b) ↔
      a ≤ (C.end_neck.coordinate_inverse x).2 ∧ (C.end_neck.coordinate_inverse x).2 ≤ b := by
  have himage : C.end_neck.coordinatePartialHomeomorph.symm.IsImage
      (C.end_neck.region a b) ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) := by
    intro y hy
    change (C.end_neck.coordinate_inverse y).1 ∈ univ ∧
      (C.end_neck.coordinate_inverse y).2 ∈ Ioo a b ↔
        y ∈ C.end_neck.carrier ∧ a < (C.end_neck.coordinate_inverse y).2 ∧
          (C.end_neck.coordinate_inverse y).2 < b
    simp only [mem_univ, true_and, mem_Ioo, show y ∈ C.end_neck.carrier from hy]
  have h := himage.closure.apply_mem_iff hx
  change C.end_neck.coordinate_inverse x ∈ closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) ↔
    x ∈ closure (C.end_neck.region a b) at h
  simpa only [closure_prod_eq, closure_univ, closure_Ioo hab.ne,
    mem_prod, mem_univ, true_and, mem_Icc] using h.symm

private theorem boundary_mem_closure_truncated_end (C : CapCertificate g)
    {a : ℝ} (ha : -C.epsilon⁻¹ < a) {x : M} (hx : x ∈ C.boundary_sphere) :
    x ∈ closure (C.end_neck.region (-C.epsilon⁻¹) a) := by
  have hquarter : x ∈ closure (C.end_neck.reversed.region
      (C.end_neck.reversed.epsilon⁻¹ / 2) C.end_neck.reversed.epsilon⁻¹) := by
    simpa only [EpsilonNeck.reversed_epsilon, EpsilonNeck.reversed_region,
      C.end_neck_epsilon, neg_div] using C.boundary_subset_negative_end_closure hx
  have hout : x ∉ C.end_neck.reversed.carrier :=
    fun h => disjoint_left.mp (CapCertificate.disjoint_closed_core_end C)
      (C.boundary_subset_closed_core hx) h
  have h := C.end_neck.reversed.mem_closure_positive_tail hquarter hout
    (b := -a) (by rw [EpsilonNeck.reversed_epsilon, C.end_neck_epsilon]; linarith)
  simpa only [EpsilonNeck.reversed_epsilon, EpsilonNeck.reversed_region,
    C.end_neck_epsilon, neg_neg] using h

theorem exists_truncated_core_domain_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ a : ℝ, a ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ →
          let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)
          IsCompact K ∧ K ⊆ C.carrier ∧
            interior K = C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) a ∧
            frontier K = range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, a)) ∧
            IsConnected (interior K) ∧ C.closed_core ⊆ interior K := by
  obtain ⟨ε₁, hε₁, hsmall, hcompact⟩ := exists_compact_truncated_core_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hpositive⟩ := exists_closed_core_disjoint_positive_end_closure_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε a ha
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)
  obtain ⟨hK, hKsub⟩ := hcompact C (hε.trans (min_le_left _ _)) a ha.2
  have hdisj := hpositive C (hε.trans (min_le_right _ _)) a ha
  have hKeq : K = C.carrier \ C.end_neck.region a C.epsilon⁻¹ := by
    ext x
    constructor
    · intro hx
      refine ⟨hKsub hx, ?_⟩
      intro hpos
      rcases hx with hcore | hneg
      · exact disjoint_left.mp (CapCertificate.disjoint_closed_core_end C) hcore hpos.1
      · have hax := ((mem_closure_end_region_iff C) ha.1 hpos.1).mp hneg
        exact (not_lt_of_ge hax.2) hpos.2.1
    · rintro ⟨hx, hnotpos⟩
      rcases (CapCertificate.carrier_eq_closed_core_union_end C) ▸ hx with hcore | hend
      · exact Or.inl hcore
      · have hdom := (C.end_neck.coordinate_inverse_mem x hend).2
        rw [C.end_neck_epsilon] at hdom
        have hax : (C.end_neck.coordinate_inverse x).2 ≤ a := by
          by_contra h
          exact hnotpos ⟨hend, lt_of_not_ge h, hdom.2⟩
        exact Or.inr (((mem_closure_end_region_iff C) ha.1 hend).mpr ⟨hdom.1.le, hax⟩)
  have hIeq : interior K = C.carrier \ closure (C.end_neck.region a C.epsilon⁻¹) := by
    rw [hKeq, Set.sdiff_eq, interior_inter, C.carrier_open.interior_eq, interior_compl]
    rfl
  have hinterior : interior K = C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) a := by
    rw [hIeq]
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      rcases (CapCertificate.carrier_eq_closed_core_union_end C) ▸ hx with hcore | hend
      · exact Or.inl hcore
      · have hdom := (C.end_neck.coordinate_inverse_mem x hend).2
        rw [C.end_neck_epsilon] at hdom
        have hax : (C.end_neck.coordinate_inverse x).2 < a := by
          by_contra h
          exact hn (((mem_closure_end_region_iff C) ha.2 hend).mpr ⟨le_of_not_gt h, hdom.2.le⟩)
        exact Or.inr ⟨hend, hdom.1, hax⟩
    · rintro (hcore | hneg)
      · exact ⟨C.closed_core_subset_carrier hcore, fun h => disjoint_left.mp hdisj hcore h⟩
      · refine ⟨C.end_neck_subset hneg.1, ?_⟩
        intro h
        exact (not_lt_of_ge (((mem_closure_end_region_iff C) ha.2 hneg.1).mp h).1) hneg.2.2
  have hfrontier : frontier K =
      range (fun q : UnitTwoSphere => C.end_neck.coordinate_map (q, a)) := by
    rw [frontier, hK.isClosed.closure_eq, hinterior]
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      have hxC := hKsub hx
      have hend : x ∈ C.end_neck.carrier :=
        ((CapCertificate.carrier_eq_closed_core_union_end C) ▸ hxC).resolve_left
          (fun h => hn (Or.inl h))
      have hdom := (C.end_neck.coordinate_inverse_mem x hend).2
      rw [C.end_neck_epsilon] at hdom
      have hneg : x ∈ closure (C.end_neck.region (-C.epsilon⁻¹) a) :=
        hx.resolve_left (fun h => hn (Or.inl h))
      have hle := (((mem_closure_end_region_iff C) ha.1 hend).mp hneg).2
      have heq : (C.end_neck.coordinate_inverse x).2 = a := by
        apply le_antisymm hle
        by_contra h
        exact hn (Or.inr ⟨hend, hdom.1, lt_of_not_ge h⟩)
      refine ⟨(C.end_neck.coordinate_inverse x).1, ?_⟩
      have hz : ((C.end_neck.coordinate_inverse x).1, a) = C.end_neck.coordinate_inverse x :=
        Prod.ext rfl heq.symm
      change C.end_neck.coordinate_map ((C.end_neck.coordinate_inverse x).1, a) = x
      rw [hz, C.end_neck.coordinate_map_coordinate_inverse hend]
    · rintro ⟨q, rfl⟩
      have hqa : (q, a) ∈ C.end_neck.cylinderDomain :=
        ⟨mem_univ _, by simpa only [C.end_neck_epsilon] using ha⟩
      have hend := C.end_neck.coordinate_map_mem hqa
      refine ⟨Or.inr (((mem_closure_end_region_iff C) ha.1 hend).mpr ?_), ?_⟩
      · rw [C.end_neck.coordinate_inverse_coordinate_map hqa]
        exact ⟨ha.1.le, le_rfl⟩
      · rintro (hcore | hneg)
        · exact disjoint_left.mp (CapCertificate.disjoint_closed_core_end C) hcore hend
        · have hlt := hneg.2.2
          rw [C.end_neck.coordinate_inverse_coordinate_map hqa] at hlt
          exact lt_irrefl a hlt
  have hconn : IsConnected (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) a) := by
    let x := C.boundary_neck.center
    have hxB : x ∈ C.boundary_sphere :=
      C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
    have hxcore := C.boundary_subset_closed_core hxB
    have hxclosure := (boundary_mem_closure_truncated_end C) ha.1 hxB
    have hneg := C.end_neck.isConnected_region
      (by rw [C.end_neck_epsilon]) (by rw [C.end_neck_epsilon]; exact ha.2.le) ha.1
    have hnegx : IsConnected (insert x (C.end_neck.region (-C.epsilon⁻¹) a)) :=
      hneg.subset_closure (subset_insert _ _) (insert_subset hxclosure subset_closure)
    have hu := (CapCertificate.isConnected_closed_core C).union ⟨x, hxcore, by simp⟩ hnegx
    rw [union_insert] at hu
    have hxU : x ∈ C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) a := Or.inl hxcore
    rw [Set.insert_eq_of_mem hxU] at hu
    exact hu
  exact ⟨hK, hKsub, hinterior, hfrontier, hinterior.symm ▸ hconn,
    hinterior.symm ▸ subset_union_left⟩

end PoincareConjecture.CapCertificate

end M38Schoenflies
