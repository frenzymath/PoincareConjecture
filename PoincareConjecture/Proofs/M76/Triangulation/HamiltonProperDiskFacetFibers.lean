import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskLowerIncidence
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskSignedFiber
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskEdgeWitnesses










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "W" => ((ℝ × ℝ) × ℝ)
local notation "Cube" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_fiber_of_paired_ends {N : Set E} {a z q : E}
    (hN : IsFinitePLBallPair ℝ N {a, z}) (f : E → ℝ)
    (hf : ContinuousOn f N) (hzero : N ∩ {x | f x = 0} = {q})
    (hsign : (f a < 0 ∧ 0 < f z) ∨ (0 < f a ∧ f z < 0)) :
    ∃ F : ℝ → E, FinitePiecewiseAffineOn F I ∧ InjOn F I ∧ F '' I = N ∧
      F 0 = q ∧ (∀ t ∈ I, F t ∈ ({a, z} : Set E) ↔ t ∈ ({-1, 1} : Set ℝ)) ∧
      (∀ t ∈ I, 0 ≤ f (F t) ↔ 0 ≤ t) ∧
      ∀ t ∈ I, f (F t) ≤ 0 ↔ t ≤ 0 := by
  have hordered {an ap : E} (hpair : IsFinitePLBallPair ℝ N {an, ap})
      (hn : f an < 0) (hp : 0 < f ap) :
      ∃ F : ℝ → E, FinitePiecewiseAffineOn F I ∧ InjOn F I ∧ F '' I = N ∧
        F 0 = q ∧ (∀ t ∈ I, F t ∈ ({an, ap} : Set E) ↔
          t ∈ ({-1, 1} : Set ℝ)) ∧
        (∀ t ∈ I, 0 ≤ f (F t) ↔ 0 ≤ t) ∧
        ∀ t ∈ I, f (F t) ≤ 0 ↔ t ≤ 0 := by
    obtain ⟨F, hF, hi, him, h0, hnval, hpval, hpos, hneg⟩ :=
      exists_signed_interval_fiber hpair f hf hzero hn hp
    refine ⟨F, hF, hi, him, h0, ?_, hpos, hneg⟩
    intro t ht
    constructor
    · rintro (he | he)
      · exact Or.inl (hi ht (by norm_num) (he.trans hnval.symm))
      · exact Or.inr (hi ht (by norm_num) (he.trans hpval.symm))
    · rintro (rfl | rfl)
      · exact Or.inl hnval
      · exact Or.inr hpval
  rcases hsign with h | h
  · exact hordered hN h.1 h.2
  · obtain ⟨F, hF, hi, him, h0, hrim, hpos, hneg⟩ :=
      hordered (by simpa only [pair_comm] using hN) h.2 h.1
    exact ⟨F, hF, hi, him, h0, by simpa only [pair_comm] using hrim, hpos, hneg⟩

variable [DecidableEq E] {R D : Set E} {b : Cube ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}




theorem HamiltonProperDiskCoherentSides.exists_triangle_fiber
    (C : HamiltonProperDiskCoherentSides T c) (h3 : Module.finrank ℝ E = 3)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 3) :
    ∃ F : ℝ → E, FinitePiecewiseAffineOn F I ∧ InjOn F I ∧
      F '' I = T.dualRegion s ∧ F 0 = s.centroid ℝ id ∧
      (∀ t ∈ I, F t ∈ T.dualRegionRim s ↔ t ∈ ({-1, 1} : Set ℝ)) ∧
      (∀ p : T.disk.vertices, (p : E) ∈ s → ∀ t ∈ I,
        0 ≤ C.labels.height p (F t) ↔ 0 ≤ t) ∧
      ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ t ∈ I,
        C.labels.height p (F t) ≤ 0 ↔ t ≤ 0 := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  obtain ⟨p0, hp0⟩ := T.disk.nonempty_of_mem_faces hs
  let p : T.disk.vertices := ⟨p0, T.disk.face_subset_vertices hs hp0⟩
  have hps : (p : E) ∈ s := hp0
  let H := (T.pairChart p).chart
  let N := T.ambient.barycentricDualBlock s
  have hinside := T.dualBlock_subset_interior hs (T.disk_triangle_not_boundary hproper hs hcard)
  have hNR : N.space ⊆ R := hinside.trans interior_subset
  have hN : T.dualRegion s = N.space := inter_eq_left.mpr hNR
  obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, _, hpair, _, hlink⟩ :=
    T.exists_triangle_normal_interval h3 hs hcard
  have hNF : N.space ∩ frontier R = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    exact fun x hx => hx.2.2 (hinside hx.1)
  have hQR : (N.link (s.centroid ℝ id)).space ⊆ R := by
    rw [hlink]
    exact hpair.1.trans hNR
  have hQ : T.dualRegionRim s = {t.centroid ℝ id, u.centroid ℝ id} := by
    change ((N.link (s.centroid ℝ id)).space ∩ R) ∪ (N.space ∩ frontier R) = _
    rw [inter_eq_left.mpr hQR, hNF, union_empty]
    exact hlink
  have hsource := T.dualRegion_subset_chart_source p hps
  have hzero : T.dualRegion s ∩ {x | C.labels.height p x = 0} =
      {s.centroid ℝ id} := by
    rw [← T.triangle_base_eq_singleton hs hcard]
    ext x
    exact and_congr_right (fun hx => C.labels.height_eq_zero_iff p (hsource hx) hx.2)
  let ell : W →ₗ[ℝ] ℝ := C.labels.weight p • LinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz := congrArg (fun m : W →ₗ[ℝ] ℝ => m ((0, 0), 1)) he
    apply C.labels.nonzero p
    change C.labels.weight p * 1 = 0 at hz
    simpa only [mul_one] using hz
  have hstar {v : Finset E} (hv : v ∈ T.ambient.faces) (hsv : s ⊆ v) :
      v ∈ (T.ambient.closedStar p).faces :=
    ⟨hv, by simpa only [Finset.insert_eq_of_mem (hsv hps)] using hv⟩
  have hvertexzero : ∀ x ∈ s, ell (H x) = 0 := by
    intro x hx
    exact (C.labels.height_eq_zero_iff p
      (T.star_source p ((T.ambient.closedStar p).subset_space
        (hstar (T.disk_le hs) Subset.rfl) hx))
      (T.disk_subset_region (T.disk_space.subset (T.disk.subset_space hs hx)))).mpr
      (T.disk_space.subset (T.disk.subset_space hs hx))
  have hsign := (T.star_affine p).opposite_centroid_signs
    (H.injOn.mono (T.star_source p)) (hstar (T.disk_le hs) Subset.rfl)
    (hstar ht hst) (hstar hu hsu)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using hcard)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using htc)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using huc)
    hst hsu htu ell.toAffineMap hell hvertexzero
  obtain ⟨F, hF, hi, him, h0, hrim, hpos, hneg⟩ := exists_fiber_of_paired_ends
    (hN.symm ▸ hpair) (C.labels.height p)
    ((C.labels.continuousOn_height p).mono hsource) hzero hsign
  refine ⟨F, hF, hi, him, h0, ?_, ?_, ?_⟩
  · simpa only [hQ] using hrim
  · intro q hqs r hr
    have hx : F r ∈ T.dualRegion s := him.subset (mem_image_of_mem F hr)
    have he : 0 ≤ C.labels.height q (F r) ↔ 0 ≤ C.labels.height p (F r) :=
      ⟨fun h => ((C.agreement s hs p q hps hqs).symm.subset ⟨hx, h⟩).2,
        fun h => ((C.agreement s hs p q hps hqs).subset ⟨hx, h⟩).2⟩
    exact he.trans (hpos r hr)
  · intro q hqs r hr
    have hx : F r ∈ T.dualRegion s := him.subset (mem_image_of_mem F hr)
    have he : C.labels.height q (F r) ≤ 0 ↔ C.labels.height p (F r) ≤ 0 :=
      ⟨fun h => ((C.negative_agreement hs p q hps hqs).symm.subset ⟨hx, h⟩).2,
        fun h => ((C.negative_agreement hs p q hps hqs).subset ⟨hx, h⟩).2⟩
    exact he.trans (hneg r hr)




theorem HamiltonProperDiskCoherentSides.exists_boundary_edge_fiber
    (C : HamiltonProperDiskCoherentSides T c) (h3 : Module.finrank ℝ E = 3)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 2)
    (hsF : s ∈ T.boundary.faces) :
    ∃ F : ℝ → E, FinitePiecewiseAffineOn F I ∧ InjOn F I ∧
      F '' I = T.dualRegion s ∩ frontier R ∧ F 0 = s.centroid ℝ id ∧
      (∀ p : T.disk.vertices, (p : E) ∈ s → ∀ t ∈ I,
        0 ≤ C.labels.height p (F t) ↔ 0 ≤ t) ∧
      ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ t ∈ I,
        C.labels.height p (F t) ≤ 0 ↔ t ≤ 0 := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.boundary.faces := (T.finite.subset T.boundary_le).fintype
  obtain ⟨p0, hp0⟩ := T.disk.nonempty_of_mem_faces hs
  let p : T.disk.vertices := ⟨p0, T.disk.face_subset_vertices hs hp0⟩
  have hps : (p : E) ∈ s := hp0
  have hpfront : (p : E) ∈ frontier R :=
    T.boundary_space.subset (T.boundary.subset_space hsF hps)
  obtain ⟨f, hf, hfi, _, hfval⟩ := T.exists_frontier_star_plane_chart p hpfront
  obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hcofaces⟩ :=
    T.exists_frontier_edge_triangle_cofaces hs hsF hcard
  let L := T.boundary.barycentricDualBlock s
  have hpair := (T.boundary.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
    (fun v hv => T.frontier_face_card_le h3 hv) hsF ht hu hcard htc huc
    hst hsu htu hcofaces).1
  have hRclosed : IsClosed R := T.region_space ▸
    (T.region.isCompact_space_of_finite (T.finite.subset T.region_le)).isClosed
  have hFR : frontier R ⊆ R := fun _ hx => hRclosed.closure_eq.subset hx.1
  have hNF : T.dualRegion s ∩ frontier R = L.space := by
    have he := T.ambient.barycentricDualBlock_space_inter_subcomplex
      T.boundary T.boundary_le s
    rw [T.boundary_space] at he
    change ((T.ambient.barycentricDualBlock s).space ∩ R) ∩ frontier R = L.space
    rw [inter_assoc, inter_eq_right.mpr hFR]
    exact he
  have hsource := T.dualRegion_subset_chart_source p hps
  have hzero : (T.dualRegion s ∩ frontier R) ∩
      {x | C.labels.height p x = 0} = {s.centroid ℝ id} := by
    rw [← T.boundary_edge_base_contact hproper hs hcard hsF]
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1.1,
        (C.labels.height_eq_zero_iff p (hsource hx.1.1) hx.1.1.2).mp hx.2⟩, hx.1.2⟩
    · intro hx
      exact ⟨⟨hx.1.1, hx.2⟩,
        (C.labels.height_eq_zero_iff p (hsource hx.1.1) hx.1.1.2).mpr hx.1.2⟩
  let ell : (ℝ × ℝ) →ₗ[ℝ] ℝ := C.labels.weight p • LinearMap.snd ℝ ℝ ℝ
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz := congrArg (fun m : (ℝ × ℝ) →ₗ[ℝ] ℝ => m (0, 1)) he
    apply C.labels.nonzero p
    change C.labels.weight p * 1 = 0 at hz
    simpa only [mul_one] using hz
  have heval (x : E) : ell (f x) = C.labels.height p x := by
    rw [hfval]
    rfl
  have hstar {v : Finset E} (hv : v ∈ T.boundary.faces) (hsv : s ⊆ v) :
      v ∈ (T.boundary.closedStar p).faces :=
    ⟨hv, by simpa only [Finset.insert_eq_of_mem (hsv hps)] using hv⟩
  have hvertexzero : ∀ x ∈ s, ell (f x) = 0 := by
    intro x hx
    rw [heval]
    have hsstar : s ∈ (T.ambient.closedStar p).faces :=
      ⟨T.disk_le hs, by simpa only [Finset.insert_eq_of_mem hps] using T.disk_le hs⟩
    have hxD := T.disk_space.subset (T.disk.subset_space hs hx)
    exact (C.labels.height_eq_zero_iff p
      (T.star_source p ((T.ambient.closedStar p).subset_space hsstar hx))
      (T.disk_subset_region hxD)).mpr hxD
  have hsign := hf.opposite_centroid_signs hfi (hstar hsF Subset.rfl)
    (hstar ht hst) (hstar hu hsu)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using hcard)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using htc)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using huc)
    hst hsu htu ell.toAffineMap hell hvertexzero
  change (ell (f (t.centroid ℝ id)) < 0 ∧ 0 < ell (f (u.centroid ℝ id))) ∨
    (0 < ell (f (t.centroid ℝ id)) ∧ ell (f (u.centroid ℝ id)) < 0) at hsign
  simp only [heval] at hsign
  obtain ⟨F, hF, hi, him, h0, _, hpos, hneg⟩ := exists_fiber_of_paired_ends
    (hNF.symm ▸ hpair) (C.labels.height p)
    ((C.labels.continuousOn_height p).mono (inter_subset_left.trans hsource)) hzero hsign
  refine ⟨F, hF, hi, him, h0, ?_, ?_⟩
  · intro q hqs r hr
    have hx := (him.subset (mem_image_of_mem F hr)).1
    have he : 0 ≤ C.labels.height q (F r) ↔ 0 ≤ C.labels.height p (F r) :=
      ⟨fun h => ((C.agreement s hs p q hps hqs).symm.subset ⟨hx, h⟩).2,
        fun h => ((C.agreement s hs p q hps hqs).subset ⟨hx, h⟩).2⟩
    exact he.trans (hpos r hr)
  · intro q hqs r hr
    have hx := (him.subset (mem_image_of_mem F hr)).1
    have he : C.labels.height q (F r) ≤ 0 ↔ C.labels.height p (F r) ≤ 0 :=
      ⟨fun h => ((C.negative_agreement hs p q hps hqs).symm.subset ⟨hx, h⟩).2,
        fun h => ((C.negative_agreement hs p q hps hqs).subset ⟨hx, h⟩).2⟩
    exact he.trans (hneg r hr)

end PoincareConjecture.M76.HamiltonIndexOne
