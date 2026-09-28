import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckRegions











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



theorem BalancedNeckChain.closure_region_inter_later_carrier_subset
    {ε : ℝ} (C : BalancedNeckChain g ε) {i j : ℤ}
    (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active) (hij : i ≤ j)
    {s : ℝ} (hs : s < ε⁻¹) :
    closure ((C.neck i).region (-ε⁻¹) s) ∩ (C.neck j).carrier ⊆
      (C.neck i).carrier := by
  intro x hx
  rcases hij.eq_or_lt with rfl | hij
  · exact hx.2
  obtain ⟨c, hc, hdis⟩ := C.later_disjoint_negative_end i hi j hj hij
  have hcN : -(C.neck i).epsilon⁻¹ < c := by
    rw [C.epsilon_eq i hi]
    exact hc.1
  have hsN : s < (C.neck i).epsilon⁻¹ := by
    rwa [C.epsilon_eq i hi]
  let K : Set M := (C.neck i).coordinate_map '' (univ ×ˢ Icc c s)
  have hK : IsCompact K := (C.neck i).isCompact_coordinate_slab_intrinsic hcN hsN
  have hinter : (C.neck i).region (-ε⁻¹) s ∩ (C.neck j).carrier ⊆ K := by
    intro y hy
    have hcy : c ≤ ((C.neck i).coordinate_inverse y).2 := by
      by_contra h
      exact Set.disjoint_left.mp hdis hy.2 ⟨hy.1.1, hy.1.2.1, lt_of_not_ge h⟩
    exact ⟨(C.neck i).coordinate_inverse y, ⟨mem_univ _, hcy, hy.1.2.2.le⟩,
      (C.neck i).coordinate_map_coordinate_inverse hy.1.1⟩
  have hxK : x ∈ K := by
    by_contra hxnot
    obtain ⟨y, hyO, hyW⟩ := mem_closure_iff.mp hx.1 ((C.neck j).carrier \ K)
      ((C.neck j).carrier_open.sdiff hK.isClosed) ⟨hx.2, hxnot⟩
    exact hyO.2 (hinter ⟨hyW, hyO.1⟩)
  exact (C.neck i).coordinate_slab_subset_carrier_m28 hcN hsN hxK



theorem EpsilonTubeCertificate.frontier_first_region {X : Set M}
    (T : EpsilonTubeCertificate g X) {i : ℤ} (hi : IsLeast T.chain.shape.active i)
    {s : ℝ} (hslo : -T.epsilon⁻¹ < s) (hshi : s < T.epsilon⁻¹) :
    frontier ((T.chain.neck i).region (-T.epsilon⁻¹) s) ∩ T.carrier =
      (T.chain.neck i).coordinate_map '' (univ ×ˢ ({s} : Set ℝ)) := by
  let N := T.chain.neck i
  have hε : N.epsilon = T.epsilon := T.chain.epsilon_eq i hi.1
  have hW : IsOpen (N.region (-T.epsilon⁻¹) s) := N.region_open _ _
  ext x
  constructor
  · intro hx
    have hxcl : x ∈ closure (N.region (-T.epsilon⁻¹) s) :=
      frontier_subset_closure hx.1
    have hxnot : x ∉ N.region (-T.epsilon⁻¹) s := (hW.frontier_eq ▸ hx.1).2
    have hxT : x ∈ ⋃ j : {j // j ∈ T.chain.shape.active},
        (T.chain.neck j.1).carrier := T.carrier_eq_chain_union ▸ hx.2
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxT
    have hxN : x ∈ N.carrier :=
      T.chain.closure_region_inter_later_carrier_subset hi.1 j.2 (hi.2 j.2)
        hshi ⟨hxcl, hxj⟩
    have hlo : -T.epsilon⁻¹ < (N.coordinate_inverse x).2 := by
      simpa only [hε] using (N.coordinate_inverse_mem x hxN).2.1
    have hhi : (N.coordinate_inverse x).2 < T.epsilon⁻¹ := by
      simpa only [hε] using (N.coordinate_inverse_mem x hxN).2.2
    have hheight : (N.coordinate_inverse x).2 = s := by
      rcases lt_trichotomy (N.coordinate_inverse x).2 s with hlt | heq | hgt
      · exact False.elim (hxnot ⟨hxN, hlo, hlt⟩)
      · exact heq
      · obtain ⟨y, hyouter, hyW⟩ := mem_closure_iff.mp hxcl
          (N.region s T.epsilon⁻¹) (N.region_open _ _) ⟨hxN, hgt, hhi⟩
        exact False.elim ((not_lt_of_ge hyW.2.2.le) hyouter.2.1)
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hheight⟩,
      N.coordinate_map_coordinate_inverse hxN⟩
  · rintro ⟨z, hz, rfl⟩
    have hzs : z.2 = s := hz.2
    have hzN : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hε, hzs]
      exact ⟨hslo, hshi⟩
    have hzcl : z ∈ closure (univ ×ˢ Ioo (-T.epsilon⁻¹) s) := by
      rw [closure_prod_eq, closure_univ, closure_Ioo hslo.ne]
      exact ⟨mem_univ _, by rw [hzs]; exact ⟨hslo.le, le_rfl⟩⟩
    have hcont : ContinuousAt N.coordinate_map z :=
      N.coordinate_map_smooth.continuousOn.continuousAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hzN⟩)
    have himage : N.coordinate_map '' (univ ×ˢ Ioo (-T.epsilon⁻¹) s) ⊆
        N.region (-T.epsilon⁻¹) s := by
      rintro y ⟨w, hw, rfl⟩
      have hwN : w.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
        rw [hε]
        exact ⟨hw.2.1, hw.2.2.trans hshi⟩
      refine ⟨N.coordinate_map_mem_of_axial w hwN, ?_⟩
      rw [N.coordinate_inverse_coordinate_map_of_axial w hwN]
      exact hw.2
    have hxcl : N.coordinate_map z ∈ closure (N.region (-T.epsilon⁻¹) s) :=
      closure_mono himage (hcont.continuousWithinAt.mem_closure_image hzcl)
    have hxnot : N.coordinate_map z ∉ N.region (-T.epsilon⁻¹) s := by
      intro hxW
      have hlt := hxW.2.2
      rw [N.coordinate_inverse_coordinate_map_of_axial z hzN, hzs] at hlt
      exact (lt_irrefl s) hlt
    refine ⟨hW.frontier_eq.symm ▸ And.intro hxcl hxnot, ?_⟩
    rw [T.carrier_eq_chain_union]
    exact mem_iUnion.mpr ⟨⟨i, hi.1⟩, N.coordinate_map_mem_of_axial z hzN⟩

end PoincareConjecture
