import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryDiskPush

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

private theorem exists_finite_boundary_collar_parameter
    {V E X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V → X}
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hcompat : ∀ i k, (e i).symm.trans (e k) ∈ piecewiseAffineGroupoid V3)
    (hj : PolyhedralPLInCharts e j K.space) (hjB : MapsTo j K.space (frontier N))
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ frontier N) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) ↦ c z))
    (hbase : ∀ x : L.space, c ((x : E), 0) = HB x) :
    ∃ q : V → E, FinitePiecewiseAffineOn q K.space ∧
      ∀ x : K.space, q x = (HB.symm ⟨j x, hjB x.property⟩ : E) := by
  classical
  let q : V → E := fun x ↦ if hx : x ∈ K.space then HB.symm ⟨j x, hjB hx⟩ else 0
  have hqval (x : K.space) : q x = (HB.symm ⟨j x, hjB x.property⟩ : E) := by
    simp only [q, dif_pos x.property]
  have hqcont : ContinuousOn q K.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (HB.symm.continuous.comp
      (hj.continuousOn.domRestrict.subtype_mk (fun x ↦ hjB x.property)))
    convert h using 1
    funext x
    exact hqval x
  have hqmap : MapsTo q K.space L.space := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact (HB.symm ⟨j x, hjB hx⟩).property
  have hbasePL : PolyhedralPLInCharts e (fun z ↦ c (z, 0)) L.space :=
    PolyhedralPLInCharts.finite_product_slice L hL hc (by norm_num)
  have hbaseInj : InjOn (fun z ↦ c (z, 0)) L.space := by
    intro x hx y hy hxy
    have hpairs := congrArg Subtype.val (hi.injective
      (a₁ := ⟨(x, 0), ⟨hx, by norm_num⟩⟩)
      (a₂ := ⟨(y, 0), ⟨hy, by norm_num⟩⟩) hxy)
    exact congrArg Prod.fst hpairs
  have hcomposite : PolyhedralPLInCharts e ((fun z ↦ c (z, 0)) ∘ q) K.space :=
    hj.congr (by
      intro x hx
      change j x = c (q x, 0)
      rw [hqval ⟨x, hx⟩, hbase, HB.apply_symm_apply])
  exact ⟨q, hbasePL.finitePiecewiseAffineOn_lift hcompat hbaseInj K hK
    hqcont hqmap hcomposite, hqval⟩

theorem exists_original_finite_boundary_push
    {V X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V → X}
    (K A : SimplicialComplex ℝ V) (hK : K.faces.Finite) (hA : A.faces.Finite)
    (hAK : A.space ⊆ K.space) (hne : K.space.Nonempty)
    (hN : IsCompact N) (he : PLDomain e N)
    (hj : PolyhedralPLInCharts e j K.space)
    (hjemb : Topology.IsEmbedding (fun x : K.space ↦ j x))
    (hjB : MapsTo j K.space (frontier N)) :
    ∃ k : V → X, PolyhedralPLInCharts e k K.space ∧
      Topology.IsEmbedding (fun x : K.space ↦ k x) ∧ MapsTo k K.space N ∧
      EqOn k j A.space ∧ ∀ x : K.space, k x ∈ frontier N ↔ (x : V) ∈ A.space := by
  obtain ⟨v, hv⟩ := hne
  have hNne : N.Nonempty := ⟨j v, he.closed.frontier_subset (hjB hv)⟩
  have hNint : (interior N).Nonempty := closure_nonempty_iff.mp
    (he.closure_interior.symm ▸ hNne)
  obtain ⟨B, _, hBN, ⟨b⟩⟩ := he.exists_ball_in_interior hNint
  obtain ⟨s, L, HB, c, hL, hc, hi, hinside, hbase, hproper, _⟩ :=
    exists_protected_small_boundary_collar hN he (hBN.trans interior_subset) b
      isOpen_univ (fun _ _ ↦ mem_univ _)
  obtain ⟨q, hq, hqval⟩ := exists_finite_boundary_collar_parameter K hK
    he.compatible hj hjB L hL HB c hc hi hbase
  obtain ⟨h, hh, hheight⟩ := K.exists_finitePL_subpolyhedron_zero_set A hK hA hAK
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hqmap : MapsTo q K.space L.space := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact (HB.symm ⟨j x, hjB hx⟩).property
  have hrecover (x : K.space) : c (q x, 0) = j x := by
    rw [hqval x, hbase, HB.apply_symm_apply]
  let a := fun x : V ↦ (q x, h x)
  have hamap : MapsTo a K.space (L.space ×ˢ I) := by
    intro x hx
    exact ⟨hqmap hx, (hheight x hx).1.1,
      (hheight x hx).1.2.trans (by norm_num)⟩
  have haPL : FinitePiecewiseAffineOn a K.space := hq.prod_mk hh
  let k := c ∘ a
  have hkPL : PolyhedralPLInCharts e k K.space :=
    hc.comp_finitePiecewiseAffineOn K hK haPL hamap
  have hkinj : InjOn k K.space := by
    intro x hx y hy hxy
    have hpair : (⟨a x, hamap hx⟩ : (L.space ×ˢ I : Set _)) =
        ⟨a y, hamap hy⟩ := hi.injective hxy
    have hqeq : q x = q y := congrArg (fun z : (L.space ×ˢ I : Set _) ↦ z.val.1) hpair
    have hjxy : j x = j y := by
      rw [← hrecover ⟨x, hx⟩, ← hrecover ⟨y, hy⟩, hqeq]
    have hsub : (⟨x, hx⟩ : K.space) = ⟨y, hy⟩ := hjemb.injective hjxy
    exact congrArg Subtype.val hsub
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  have hkemb : Topology.IsEmbedding (fun x : K.space ↦ k x) :=
    (hkPL.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy ↦ Subtype.ext (hkinj x.property y.property hxy))).isEmbedding
  refine ⟨k, hkPL, hkemb, fun x hx ↦ hinside (hamap hx), ?_, ?_⟩
  · intro x hx
    have hzero := (hheight x (hAK hx)).2.mpr hx
    change c (q x, h x) = j x
    rw [hzero]
    exact hrecover ⟨x, hAK hx⟩
  · intro x
    exact (hproper ⟨a x, hamap x.property⟩).trans (hheight x x.property).2

end PoincareConjecture.M76.Dehn
