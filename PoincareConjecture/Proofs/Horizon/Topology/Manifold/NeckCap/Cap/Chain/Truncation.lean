import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Maximal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.NegativeEnd
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InnerSlabCover
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.PositiveEnd
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem mem_closure_neck_region_iff (N : EpsilonNeck g) {a b : ℝ}
    (hab : a < b) {x : M} (hx : x ∈ N.carrier) :
    x ∈ closure (N.region a b) ↔
      a ≤ (N.coordinate_inverse x).2 ∧ (N.coordinate_inverse x).2 ≤ b := by
  have himage : N.coordinatePartialHomeomorph.symm.IsImage
      (N.region a b) ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) := by
    intro y hy
    change (N.coordinate_inverse y).1 ∈ univ ∧
      (N.coordinate_inverse y).2 ∈ Ioo a b ↔
        y ∈ N.carrier ∧ a < (N.coordinate_inverse y).2 ∧
          (N.coordinate_inverse y).2 < b
    simp only [mem_univ, true_and, mem_Ioo, show y ∈ N.carrier from hy]
  have h := himage.closure.apply_mem_iff hx
  change N.coordinate_inverse x ∈ closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) ↔
    x ∈ closure (N.region a b) at h
  simpa only [closure_prod_eq, closure_univ, closure_Ioo hab.ne,
    mem_prod, mem_univ, true_and, mem_Icc] using h.symm

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem disjoint_closure_of_open {U V : Set M}
    (hU : IsOpen U) (hUV : Disjoint U V) : Disjoint U (closure V) := by
  rw [disjoint_left]
  intro x hx hxcl
  obtain ⟨y, hyU, hyV⟩ := mem_closure_iff.mp hxcl U hU hx
  exact disjoint_left.mp hUV hyU hyV




theorem exists_finite_chain_truncation_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T →
          ∀ b : ℤ, T.shape = .finite 0 b →
          ∀ t : ℝ, t ∈ Ioo (C.epsilon⁻¹ / 2) C.epsilon⁻¹ →
            let A := C.carrier ∪ (T.unionOpen : Set M)
            let K := A \ (T.neck b).region t C.epsilon⁻¹
            IsCompact K ∧ K ⊆ A ∧
              interior K = A \ closure ((T.neck b).region t C.epsilon⁻¹) ∧
              frontier K = range (fun q : UnitTwoSphere => (T.neck b).coordinate_map (q, t)) ∧
              C.closed_core ⊆ interior K ∧ IsConnected (interior K) := by
  obtain ⟨ε₁, hε₁, hsmall, hcompact⟩ := exists_compact_truncated_core_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hpositive⟩ :=
    exists_closed_core_disjoint_positive_end_closure_threshold.{u}
  obtain ⟨ε₃, hε₃, -, havoid⟩ := exists_chain_later_disjoint_closed_core_threshold.{u}
  obtain ⟨ε₄, hε₄, -, hexclude⟩ :=
    BalancedNeckChain.exists_positive_end_exclusion_threshold.{u}
  refine ⟨min ε₁ (min ε₂ (min ε₃ ε₄)),
    lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε H T hT b hshape t ht
  classical
  have h₁ := hε.trans (min_le_left _ _)
  have hrest := hε.trans (min_le_right _ _)
  have h₂ := hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have h₃ := hrest.trans (min_le_left _ _)
  have h₄ := hrest.trans (min_le_right _ _)
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hbnonneg : 0 ≤ b := by
    have h := hT.zero_active
    simpa only [hshape, ChainShape.active, mem_Icc, le_refl, true_and] using h
  have hb : b ∈ T.shape.active := by
    simp only [hshape, ChainShape.active, mem_Icc]
    exact ⟨hbnonneg, le_rfl⟩
  have hbounds {j : ℤ} (hj : j ∈ T.shape.active) : 0 ≤ j ∧ j ≤ b := by
    simpa only [hshape, ChainShape.active, mem_Icc] using hj
  let N := T.neck b
  have heN : N.epsilon = C.epsilon := T.epsilon_eq b hb
  let A := C.carrier ∪ (T.unionOpen : Set M)
  let P := N.region t C.epsilon⁻¹
  let K := A \ P
  have hA : IsOpen A := C.carrier_open.union T.unionOpen.isOpen
  have hNA : N.carrier ⊆ A := fun x hx => Or.inr (mem_iUnion.mpr ⟨⟨b, hb⟩, hx⟩)
  have hend : C.end_neck.carrier ⊆ (T.unionOpen : Set M) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨0, hT.zero_active⟩, hT.first_neck.symm ▸ hx⟩
  have hAc : A = C.closed_core ∪ (T.unionOpen : Set M) := by
    apply Subset.antisymm
    · rintro x (hxC | hxT)
      · rcases C.carrier_eq_closed_core_union_end ▸ hxC with hxcore | hxend
        · exact Or.inl hxcore
        · exact Or.inr (hend hxend)
      · exact Or.inr hxT
    · exact union_subset (C.closed_core_subset_carrier.trans subset_union_left)
        subset_union_right
  let K₀ := C.closed_core ∪ closure
    (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2))
  obtain ⟨hK₀, hK₀sub⟩ := hcompact C h₁ (-C.epsilon⁻¹ / 2) (by linarith)
  let slab (j : ℤ) := (T.neck j).coordinate_map ''
    (Set.prod univ (Icc (-(3 / 4 : ℝ) * C.epsilon⁻¹) ((3 / 4 : ℝ) * C.epsilon⁻¹)))
  have hslab (j : ℤ) (hj : j ∈ T.shape.active) :
      IsCompact (slab j) ∧ slab j ⊆ A := by
    have he := T.epsilon_eq j hj
    have hlo : -(T.neck j).epsilon⁻¹ < -(3 / 4 : ℝ) * C.epsilon⁻¹ := by
      rw [he]
      linarith
    have hhi : (3 / 4 : ℝ) * C.epsilon⁻¹ < (T.neck j).epsilon⁻¹ := by
      rw [he]
      linarith
    refine ⟨(T.neck j).isCompact_coordinate_slab hlo hhi, ?_⟩
    intro x hx
    have hxj := ((T.neck j).mem_coordinate_slab_iff hlo hhi).mp hx
    exact Or.inr (mem_iUnion.mpr ⟨⟨j, hj⟩, hxj.1⟩)
  have hfinite : T.shape.active.Finite := by
    rw [hshape]
    exact finite_Icc _ _
  let : Fintype {j // j ∈ T.shape.active} := hfinite.fintype
  let B := ⋃ j : {j // j ∈ T.shape.active}, slab j.1
  have hB : IsCompact B := isCompact_iUnion fun j => (hslab j.1 j.2).1
  have hBA : B ⊆ A := iUnion_subset fun j => (hslab j.1 j.2).2
  let L := N.coordinate_map '' (univ ×ˢ Icc (C.epsilon⁻¹ / 2) t)
  have hlo : -N.epsilon⁻¹ < C.epsilon⁻¹ / 2 := by rw [heN]; linarith
  have hhi : t < N.epsilon⁻¹ := by simpa only [heN] using ht.2
  have hL : IsCompact L := N.isCompact_coordinate_slab hlo hhi
  have hLA : L ⊆ A := fun x hx => hNA ((N.mem_coordinate_slab_iff hlo hhi).mp hx).1
  let S := (K₀ ∪ B) ∪ L
  have hS : IsCompact S := (hK₀.union hB).union hL
  have hSA : S ⊆ A := union_subset
    (union_subset (hK₀sub.trans subset_union_left) hBA) hLA
  have hKS : K ⊆ S := by
    rintro x ⟨hxA, hxP⟩
    rw [hAc] at hxA
    rcases hxA with hxcore | hxT
    · exact Or.inl (Or.inl (Or.inl hxcore))
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxT
      rcases T.mem_inner_slab_or_missing_neighbor_quarter hT.quarter_capture j.2 hxj with
        ⟨i, hi, hxi⟩ | ⟨hprev, hxneg⟩ | ⟨hnext, hxpos⟩
      · have hxi' : x ∈ slab i := by simpa only [slab, T.epsilon_eq i hi] using hxi
        exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi'⟩))
      · have hjzero : j.1 = 0 := by
          have hj := hbounds j.2
          simp only [hshape, ChainShape.active, mem_Icc] at hprev
          omega
        rw [hjzero, hT.first_neck] at hxneg
        exact Or.inl (Or.inl (Or.inr (subset_closure hxneg)))
      · have hjlast : j.1 = b := by
          have hj := hbounds j.2
          simp only [hshape, ChainShape.active, mem_Icc] at hnext
          omega
        rw [hjlast] at hxpos
        have hle : (N.coordinate_inverse x).2 ≤ t := by
          by_contra h
          exact hxP ⟨hxpos.1, lt_of_not_ge h, hxpos.2.2⟩
        exact Or.inr ((N.mem_coordinate_slab_iff hlo hhi).mpr ⟨hxpos.1, hxpos.2.1.le, hle⟩)
  have hKeq : K = S \ P := by
    apply Subset.antisymm
    · exact fun _ hx => ⟨hKS hx, hx.2⟩
    · exact fun _ hx => ⟨hSA hx.1, hx.2⟩
  have hK : IsCompact K := by
    rw [hKeq, Set.sdiff_eq]
    exact hS.inter_right (N.isOpen_region t C.epsilon⁻¹).isClosed_compl
  have hPquarter : P ⊆ N.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹ :=
    fun _ hx => ⟨hx.1, ht.1.trans hx.2.1, hx.2.2⟩
  have hearlier (j : ℤ) (hj : j ∈ T.shape.active) (hjb : j < b) :
      Disjoint (T.neck j).carrier (closure P) := by
    apply disjoint_closure_of_open (T.neck j).carrier_open
    exact (hexclude T h₄ j hj b hb hjb).mono_right hPquarter
  have hcore : Disjoint C.closed_core (closure P) := by
    by_cases hbzero : b = 0
    · have hN : N = C.end_neck := by simp only [N, hbzero, hT.first_neck]
      change Disjoint C.closed_core (closure (N.region t C.epsilon⁻¹))
      rw [hN]
      exact hpositive C h₂ t ⟨by linarith [ht.1], ht.2⟩
    · have hbpos : 0 < b := by omega
      have havoidcore := havoid C h₃ T 0 hT.zero_active b hb hT.first_neck hbpos
        ((hT.centers b hb hbpos).2)
      have hCquarter : Disjoint C.carrier (N.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) := by
        rw [disjoint_left]
        intro x hxC hxQ
        rcases C.carrier_eq_closed_core_union_end ▸ hxC with hxcore | hxend
        · exact disjoint_left.mp havoidcore hxQ.1 hxcore
        · have h := hexclude T h₄ 0 hT.zero_active b hb hbpos
          rw [hT.first_neck] at h
          exact disjoint_left.mp h hxend hxQ
      exact (disjoint_closure_of_open C.carrier_open
        (hCquarter.mono_right hPquarter)).mono_left C.closed_core_subset_carrier
  have hlocal : A ∩ closure P ⊆ N.carrier := by
    rintro x ⟨hxA, hxcl⟩
    rw [hAc] at hxA
    rcases hxA with hxcore | hxT
    · exact (disjoint_left.mp hcore hxcore hxcl).elim
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxT
      by_cases hjb : j.1 = b
      · simpa only [hjb] using hxj
      · exact (disjoint_left.mp (hearlier j.1 j.2 (lt_of_le_of_ne (hbounds j.2).2 hjb))
          hxj hxcl).elim
  have hinterior : interior K = A \ closure P := by
    change interior (A \ P) = _
    rw [Set.sdiff_eq, interior_inter, hA.interior_eq, interior_compl]
    rfl
  have hfrontier : frontier K =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) := by
    rw [frontier, hK.isClosed.closure_eq, hinterior]
    ext x
    constructor
    · rintro ⟨hxK, hxint⟩
      have hxcl : x ∈ closure P := by
        by_contra h
        exact hxint ⟨hxK.1, h⟩
      have hxN := hlocal ⟨hxK.1, hxcl⟩
      have hge := ((mem_closure_neck_region_iff N ht.2 hxN).mp hxcl).1
      have hdom := (N.coordinate_inverse_mem x hxN).2
      rw [heN] at hdom
      have hle : (N.coordinate_inverse x).2 ≤ t := by
        by_contra h
        exact hxK.2 ⟨hxN, lt_of_not_ge h, hdom.2⟩
      have heq := le_antisymm hle hge
      refine ⟨(N.coordinate_inverse x).1, ?_⟩
      have hz : ((N.coordinate_inverse x).1, t) = N.coordinate_inverse x :=
        Prod.ext rfl heq.symm
      change N.coordinate_map ((N.coordinate_inverse x).1, t) = x
      rw [hz, N.coordinate_map_coordinate_inverse hxN]
    · rintro ⟨q, rfl⟩
      have hqt : (q, t) ∈ N.cylinderDomain := by
        refine ⟨mem_univ _, ?_⟩
        rw [heN]
        exact ⟨by linarith [ht.1], ht.2⟩
      have hxN := N.coordinate_map_mem hqt
      have hxcl : N.coordinate_map (q, t) ∈ closure P := by
        apply (mem_closure_neck_region_iff N ht.2 hxN).mpr
        rw [N.coordinate_inverse_coordinate_map hqt]
        exact ⟨le_rfl, ht.2.le⟩
      refine ⟨⟨hNA hxN, ?_⟩, fun hx => hx.2 hxcl⟩
      intro hxP
      have hlt := hxP.2.1
      rw [N.coordinate_inverse_coordinate_map hqt] at hlt
      exact lt_irrefl t hlt
  have hcoreint : C.closed_core ⊆ interior K := by
    intro x hx
    rw [hinterior]
    exact ⟨Or.inl (C.closed_core_subset_carrier hx), fun h => disjoint_left.mp hcore hx h⟩
  let F (j : ℤ) := if j = b then N.region (-C.epsilon⁻¹) t else (T.neck j).carrier
  let V := ⋃ j ∈ T.shape.active, F j
  have hF (j : ℤ) (_ : j ∈ T.shape.active) : IsConnected (F j) := by
    dsimp only [F]
    split_ifs
    · exact N.isConnected_region (by rw [heN]) (by rw [heN]; exact ht.2.le)
        (by linarith [ht.1])
    · exact (T.neck j).isConnected_carrier
  have hV : IsConnected V := by
    apply IsConnected.biUnion_of_chain T.active_nonempty T.shape.ordConnected_active hF
    intro j hj hjnext
    change j + 1 ∈ T.shape.active at hjnext
    change (F j ∩ F (j + 1)).Nonempty
    have hjne : j ≠ b := by have h := hbounds hjnext; omega
    dsimp only [F]
    rw [if_neg hjne]
    by_cases hnext : j + 1 = b
    · rw [if_pos hnext]
      let q := (N.coordinate_inverse N.center).1
      let s := -(3 / 4 : ℝ) * C.epsilon⁻¹
      have hs : (q, s) ∈ N.cylinderDomain := by
        refine ⟨mem_univ _, ?_⟩
        rw [heN]
        dsimp [s]
        constructor <;> linarith
      have hxneg : N.coordinate_map (q, s) ∈
          N.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) := by
        refine ⟨N.coordinate_map_mem hs, ?_⟩
        rw [N.coordinate_inverse_coordinate_map hs]
        dsimp [s]
        constructor <;> linarith
      have hxold := (T.overlap_contains_quarters j hj hjnext).2
        (show N.coordinate_map (q, s) ∈ (T.neck (j + 1)).region
          (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) by simpa only [hnext] using hxneg)
      exact ⟨N.coordinate_map (q, s), hxold, hxneg.1, hxneg.2.1,
        hxneg.2.2.trans (by linarith [ht.1])⟩
    · rw [if_neg hnext]
      exact T.adjacent_overlap j hj hjnext
  have hVeq : interior K = C.closed_core ∪ V := by
    rw [hinterior]
    apply Subset.antisymm
    · rintro x ⟨hxA, hxP⟩
      rw [hAc] at hxA
      rcases hxA with hxcore | hxT
      · exact Or.inl hxcore
      · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxT
        apply Or.inr
        apply mem_iUnion₂.mpr
        refine ⟨j.1, j.2, ?_⟩
        dsimp only [F]
        by_cases hjb : j.1 = b
        · rw [if_pos hjb]
          have hxN : x ∈ N.carrier := by simpa only [hjb] using hxj
          have hdom := (N.coordinate_inverse_mem x hxN).2
          rw [heN] at hdom
          refine ⟨hxN, hdom.1, ?_⟩
          by_contra h
          exact hxP ((mem_closure_neck_region_iff N ht.2 hxN).mpr
            ⟨le_of_not_gt h, hdom.2.le⟩)
        · rwa [if_neg hjb]
    · rintro x (hxcore | hxV)
      · exact ⟨Or.inl (C.closed_core_subset_carrier hxcore),
          fun h => disjoint_left.mp hcore hxcore h⟩
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxV
        dsimp only [F] at hxj
        by_cases hjb : j = b
        · rw [if_pos hjb] at hxj
          exact ⟨hNA hxj.1, fun h => not_lt_of_ge
            ((mem_closure_neck_region_iff N ht.2 hxj.1).mp h).1 hxj.2.2⟩
        · rw [if_neg hjb] at hxj
          exact ⟨Or.inr (mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩), fun h =>
            disjoint_left.mp (hearlier j hj (lt_of_le_of_ne (hbounds hj).2 hjb)) hxj h⟩
  have hnegV : C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ⊆ V := by
    intro x hx
    apply mem_iUnion₂.mpr
    refine ⟨0, hT.zero_active, ?_⟩
    dsimp only [F]
    by_cases hbzero : b = 0
    · rw [if_pos hbzero.symm]
      have hN : N = C.end_neck := by simp only [N, hbzero, hT.first_neck]
      rw [hN]
      exact ⟨hx.1, hx.2.1, hx.2.2.trans (by linarith [ht.1])⟩
    · rw [if_neg (Ne.symm hbzero), hT.first_neck]
      exact hx.1
  have hcenter : C.boundary_neck.center ∈ C.boundary_sphere :=
    C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
  have hcenterCore := C.boundary_subset_closed_core hcenter
  have hcenterV : C.boundary_neck.center ∈ closure V :=
    closure_mono hnegV (C.boundary_subset_negative_end_closure hcenter)
  have hVinsert : IsConnected (insert C.boundary_neck.center V) :=
    hV.subset_closure (subset_insert _ _) (insert_subset hcenterV subset_closure)
  have hconn := C.isConnected_closed_core.union
    ⟨C.boundary_neck.center, hcenterCore, mem_insert _ _⟩ hVinsert
  rw [union_insert, Set.insert_eq_of_mem
    (show C.boundary_neck.center ∈ C.closed_core ∪ V from Or.inl hcenterCore)] at hconn
  exact ⟨hK, sdiff_subset, hinterior, hfrontier, hcoreint, hVeq.symm ▸ hconn⟩

end PoincareConjecture.CapCertificate
