import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFacetInterior
import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.HeightPlaneAffineCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedManifoldConditions
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoCofaceCarrierGerm
import PoincareConjecture.Proofs.M76.Mathlib.MinimalFaceRadialTransport
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFiniteAffineCover
import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms

set_option autoImplicit false

open Set Module

namespace Geometry.SimplicialComplex

section Parents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem triangle_parent_unique
    (K L : SimplicialComplex ℝ E) (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {a t u : Finset E} (ha : a ∈ L.faces) (ha3 : a.card = 3)
    (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hat : convexHull ℝ (a : Set E) ⊆ convexHull ℝ (t : Set E))
    (hau : convexHull ℝ (a : Set E) ⊆ convexHull ℝ (u : Set E)) : t = u := by
  classical
  have hainter : convexHull ℝ (a : Set E) ⊆ convexHull ℝ ((t ∩ u : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull ht hu]
    exact subset_inter hat hau
  have hle := (L.indep ha).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ (a : Set E)).trans
      (hainter.trans (convexHull_subset_affineSpan (s := ((t ∩ u : Finset E) : Set E)))))
  have htbound := hbound t ht
  have hubound := hbound u hu
  have hti : t ∩ u = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hui : t ∩ u = u := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact hti.symm.trans hui

theorem IsSubdivision.existsUnique_triangle_coface_parent
    {K L : SimplicialComplex ℝ E} (hLK : L.IsSubdivision K)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s a : Finset E} (hs : s ∈ K.faces) (ha : a ∈ L.faces) (ha3 : a.card = 3)
    {x : E} (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxa : x ∈ convexHull ℝ (a : Set E)) :
    ∃! t : Finset E, t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t ∧
      convexHull ℝ (a : Set E) ⊆ convexHull ℝ (t : Set E) := by
  obtain ⟨t, ht, hat⟩ := hLK.face_subset a ha
  have hle := (L.indep ha).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ (a : Set E)).trans
      (hat.trans (convexHull_subset_affineSpan (s := (t : Set E)))))
  have htbound := hbound t ht
  refine ⟨t, ⟨ht, by omega, K.subset_of_mem_intrinsicInterior_face hs ht hxs (hat hxa), hat⟩,
    fun u hu => ?_⟩
  exact K.triangle_parent_unique L hbound ha ha3 hu.1 ht hu.2.2.2 hat

end Parents

section Paired

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem triangle_plane_projection
    (K : SimplicialComplex ℝ E) {t : Finset E}
    (ht : t ∈ K.faces) (ht3 : t.card = 3) :
    ∃ f : E →ᴬ[ℝ] (ℝ × ℝ), InjOn f (affineSpan ℝ (t : Set E)) := by
  let W := (affineSpan ℝ (t : Set E)).direction
  obtain ⟨p, hp⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  let e : W ≃ₗ[ℝ] (ℝ × ℝ) := LinearEquiv.ofFinrankEq _ _ (by
    simpa only [Module.finrank_prod, Module.finrank_self] using
      K.finrank_faceDirection_of_card ht ht3)
  let f : E →ᴬ[ℝ] (ℝ × ℝ) :=
    (e.toLinearMap.comp p).toContinuousLinearMap.toContinuousAffineMap
  refine ⟨f, ?_⟩
  intro x hx y hy hxy
  have hpxy : p x = p y := e.injective hxy
  let d : W := ⟨x - y, (affineSpan ℝ (t : Set E)).vsub_mem_direction hx hy⟩
  have hd : p (d : E) = d := LinearMap.congr_fun hp d
  have hd0 : d = 0 := by
    rw [← hd]
    change p (x - y) = 0
    rw [map_sub, hpxy, sub_self]
  exact sub_eq_zero.mp (congrArg Subtype.val hd0)

private theorem affine_image_intrinsic_interior
    (f : E →ᴬ[ℝ] (ℝ × ℝ)) {S : Set E}
    (hf : InjOn f (affineSpan ℝ S)) {x : E}
    (hx : x ∈ intrinsicInterior ℝ S) :
    f x ∈ intrinsicInterior ℝ (f '' S) := by
  rw [← intrinsicClosure_sdiff_intrinsicFrontier]
  refine ⟨subset_intrinsicClosure (mem_image_of_mem f (intrinsicInterior_subset hx)), ?_⟩
  intro hfront
  have himage := f.toAffineMap.intrinsicFrontier_image_of_injOn S hf
  obtain ⟨y, hy, he⟩ := himage.subset hfront
  have hyS : y ∈ affineSpan ℝ S := intrinsicClosure_subset_affineSpan
    (by rw [← intrinsicClosure_sdiff_intrinsicInterior] at hy; exact hy.1)
  have hyx : y = x := hf hyS
    (subset_affineSpan ℝ _ (intrinsicInterior_subset hx)) he
  rw [hyx, ← intrinsicClosure_sdiff_intrinsicInterior] at hy
  exact hy.2 hx

theorem fine_triangle_pair_not_in_one_coarse_triangle
    (K L : SimplicialComplex ℝ E)
    {r a b s t : Finset E} (hr : r ∈ L.faces)
    (ha : a ∈ L.faces) (hb : b ∈ L.faces)
    (hr2 : r.card = 2) (ha3 : a.card = 3) (hb3 : b.card = 3)
    (hra : r ⊆ a) (hrb : r ⊆ b) (hab : a ≠ b)
    (ht : t ∈ K.faces) (ht3 : t.card = 3) (hst : s ⊂ t)
    (hat : convexHull ℝ (a : Set E) ⊆ convexHull ℝ (t : Set E))
    (hbt : convexHull ℝ (b : Set E) ⊆ convexHull ℝ (t : Set E))
    {x : E} (hxr : x ∈ intrinsicInterior ℝ (convexHull ℝ (r : Set E)))
    (hxs : x ∈ convexHull ℝ (s : Set E)) : False := by
  classical
  obtain ⟨f, hfi⟩ := triangle_plane_projection K ht ht3
  let N : SimplicialComplex ℝ E :=
    { faces := {u | u ∈ L.faces ∧
        convexHull ℝ (u : Set E) ⊆ convexHull ℝ (t : Set E)}
      indep := fun hu => L.indep hu.1
      isRelLowerSet_faces := by
        intro u hu
        exact ⟨L.nonempty_of_mem_faces hu.1, fun v hv hne =>
          ⟨L.down_closed hu.1 hv hne, (convexHull_mono hv).trans hu.2⟩⟩
      inter_subset_convexHull := fun hu hv => L.inter_subset_convexHull hu.1 hv.1 }
  have hNs : N.space ⊆ convexHull ℝ (t : Set E) := by
    intro y hy
    obtain ⟨u, hu, hyu⟩ := mem_space_iff.mp hy
    exact hu.2 hyu
  have hNa : a ∈ N.faces := ⟨ha, hat⟩
  have hNb : b ∈ N.faces := ⟨hb, hbt⟩
  have hNr : r ∈ N.faces := ⟨hr, (convexHull_mono hra).trans hat⟩
  have hNi : InjOn f N.space := hfi.mono
    (hNs.trans (convexHull_subset_affineSpan (s := (t : Set E))))
  have hfN : N.AffineOnFaces f := N.affineOnFaces_affine f
  let M := hfN.embeddedImage hNi
  have hmem (u : Finset E) (hu : u ∈ N.faces) : u.image f ∈ M.faces :=
    (hfN.image_mem_embeddedImage_iff hNi (N.subset_space hu)).mpr hu
  have hcard (u : Finset E) (hu : u ∈ N.faces) : (u.image f).card = u.card :=
    Finset.card_image_iff.mpr (hNi.mono (N.subset_space hu))
  have habf : a.image f ≠ b.image f := by
    intro he
    apply hab
    apply Finset.coe_injective
    apply (hNi.image_eq_image_iff (N.subset_space hNa) (N.subset_space hNb)).mp
    exact (Finset.coe_image.symm.trans
      (congrArg (fun z : Finset (ℝ × ℝ) => (z : Set (ℝ × ℝ))) he)).trans Finset.coe_image
  have hfr : InjOn f (affineSpan ℝ (convexHull ℝ (r : Set E))) := by
    rw [affineSpan_convexHull]
    exact hfi.mono (affineSpan_le.mpr
      ((subset_convexHull ℝ (r : Set E)).trans
        (((convexHull_mono hra).trans hat).trans
          (convexHull_subset_affineSpan (s := (t : Set E))))))
  have hximage : f x ∈ intrinsicInterior ℝ (convexHull ℝ (r.image f : Set (ℝ × ℝ))) := by
    rw [Finset.coe_image, ← hfN.image_convexHull hNr]
    exact affine_image_intrinsic_interior f hfr hxr
  have hxint := M.mem_interior_union_of_paired_facet
    (by rw [hcard r hNr, hr2]; simp [Module.finrank_prod])
    (hmem a hNa) (hmem b hNb)
    (by rw [hcard a hNa, ha3]; simp [Module.finrank_prod])
    (by rw [hcard b hNb, hb3]; simp [Module.finrank_prod])
    (Finset.image_subset_image hra) (Finset.image_subset_image hrb) habf hximage
  have himages (u : Finset E) (hu : u ∈ N.faces)
      (hut : convexHull ℝ (u : Set E) ⊆ convexHull ℝ (t : Set E)) :
      convexHull ℝ (u.image f : Set (ℝ × ℝ)) ⊆ f '' convexHull ℝ (t : Set E) := by
    rw [Finset.coe_image, ← hfN.image_convexHull hu]
    exact image_mono hut
  have hxintT : f x ∈ interior (f '' convexHull ℝ (t : Set E)) :=
    interior_mono (union_subset (himages a hNa hat) (himages b hNb hbt)) hxint
  have hxf : x ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) :=
    (K.indep ht).convexHull_subset_intrinsicFrontier hst hxs
  have hfT : InjOn f (affineSpan ℝ (convexHull ℝ (t : Set E))) := by
    rwa [affineSpan_convexHull]
  have hxfront : f x ∈ frontier (f '' convexHull ℝ (t : Set E)) := by
    apply intrinsicFrontier_subset_frontier (𝕜 := ℝ)
    exact (f.toAffineMap.intrinsicFrontier_image_of_injOn _ hfT).symm.subset
      (mem_image_of_mem f hxf)
  exact hxfront.2 hxintT

omit [FiniteDimensional ℝ E] in
private theorem convex_subset_affine_of_local
    {C : Set E} (hC : Convex ℝ C) {x : E} (hx : x ∈ C)
    {ε : ℝ} (hε : 0 < ε) (A : AffineSubspace ℝ E)
    (hlocal : C ∩ Metric.ball x ε ⊆ A) : C ⊆ A := by
  have hxA : x ∈ A := hlocal ⟨hx, Metric.mem_ball_self hε⟩
  intro y hy
  obtain ⟨r, hr, hrball⟩ := Set.exists_pos_smul_mem_of_mem_nhds
    (Metric.ball_mem_nhds (0 : E) hε) (y - x)
  let z := r • (y - x) + x
  have hzEq : z = AffineMap.lineMap x y r := by
    simp only [z, AffineMap.lineMap_apply_module]
    module
  have hzC : z ∈ C := hzEq.symm ▸
    hC.segment_subset hx hy (lineMap_mem_segment ℝ x y ⟨hr.1.le, hr.2⟩)
  have hzball : z ∈ Metric.ball x ε := by
    simpa only [z, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hrball
  have hd := A.direction.smul_mem r⁻¹ (A.vsub_mem_direction (hlocal ⟨hzC, hzball⟩) hxA)
  have hd' : y - x ∈ A.direction := by
    simpa only [vsub_eq_sub, z, add_sub_cancel_right, inv_smul_smul₀ hr.1.ne'] using hd
  change y ∈ A
  simpa only [vadd_eq_add, sub_add_cancel] using A.vadd_mem_of_mem_direction hd' hxA

theorem IsSubdivision.exists_triangle_coface_in_parent
    {K L : SimplicialComplex ℝ E} (hLK : L.IsSubdivision K) (hL : L.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s r t : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    (hr : r ∈ L.faces) (hr2 : r.card = 2)
    (ht : t ∈ K.faces) (ht3 : t.card = 3) (hst : s ⊆ t)
    {x : E} (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxr : x ∈ intrinsicInterior ℝ (convexHull ℝ (r : Set E))) :
    ∃ a : Finset E, a ∈ L.faces ∧ a.card = 3 ∧ r ⊆ a ∧
      convexHull ℝ (a : Set E) ⊆ convexHull ℝ (t : Set E) := by
  classical
  by_contra hnot
  obtain ⟨U, hU, hxU, hUfaces⟩ := L.exists_open_face_hulls_contain_point hL x
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  let edges : Bool → Finset E := fun i => if i then s else r
  let planes : Bool → AffineSubspace ℝ E := fun i => affineSpan ℝ (edges i : Set E)
  have hcover : convexHull ℝ (t : Set E) ∩ Metric.ball x ε ⊆
      ⋃ i, (planes i : Set E) := by
    rintro y ⟨hyt, hyball⟩
    obtain ⟨a, ha, hya⟩ := mem_space_iff.mp
      (hLK.space_eq.symm.subset (K.convexHull_subset_space ht hyt))
    have hxa := hUfaces a ha ⟨y, hya, hball hyball⟩
    have hra : r ⊆ a := L.subset_of_mem_intrinsicInterior_face hr ha hxr hxa
    obtain ⟨v, hv, hav⟩ := hLK.face_subset a ha
    have halow := Finset.card_le_card hra
    have hacard := (L.indep ha).card_le_card_of_subset_affineSpan
      ((subset_convexHull ℝ (a : Set E)).trans
        (hav.trans (convexHull_subset_affineSpan (s := (v : Set E)))))
    have haup : a.card ≤ 3 := hacard.trans (hbound v hv)
    by_cases hac : a.card = 2
    · have hraeq : r = a := Finset.eq_of_subset_of_card_le hra (by omega)
      refine mem_iUnion.mpr ⟨false, ?_⟩
      change y ∈ affineSpan ℝ (r : Set E)
      exact convexHull_subset_affineSpan (s := (r : Set E)) (hraeq.symm ▸ hya)
    · have ha3 : a.card = 3 := by omega
      obtain ⟨v, ⟨hv, hv3, hsv, hav⟩, _⟩ :=
        hLK.existsUnique_triangle_coface_parent hbound hs ha ha3 hxs hxa
      have hvt : v ≠ t := by
        intro he
        exact hnot ⟨a, ha, ha3, hra, he ▸ hav⟩
      have hintercard : (v ∩ t).card ≤ 2 := by
        by_contra hn
        have hleft : v ∩ t = v :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        have hright : v ∩ t = t :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
        exact hvt (hleft.symm.trans hright)
      have hinter : s = v ∩ t :=
        Finset.eq_of_subset_of_card_le (Finset.subset_inter hsv hst) (by omega)
      have hys : y ∈ convexHull ℝ (s : Set E) := by
        rw [hinter, Finset.coe_inter, ← K.convexHull_inter_convexHull hv ht]
        exact ⟨hav hya, hyt⟩
      exact mem_iUnion.mpr ⟨true, convexHull_subset_affineSpan (s := (s : Set E)) hys⟩
  have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono hst (intrinsicInterior_subset hxs)
  obtain ⟨i, hi⟩ := Convex.exists_subset_affineSubspace_of_subset_iUnion
    ((convex_convexHull ℝ (t : Set E)).inter (convex_ball x ε))
    ⟨x, hxt, Metric.mem_ball_self hε⟩ planes hcover
  have hwhole := convex_subset_affine_of_local (convex_convexHull ℝ (t : Set E)) hxt hε
    (planes i) hi
  have hle := (K.indep ht).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ (t : Set E)).trans hwhole)
  have hedges : (edges i).card = 2 := by cases i <;> assumption
  omega

theorem IsSubdivision.ncard_triangle_cofaces_eq_of_shared_edge_interior
    {K L : SimplicialComplex ℝ E} (hLK : L.IsSubdivision K) (hL : L.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s r : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    (hr : r ∈ L.faces) (hr2 : r.card = 2)
    {x : E} (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxr : x ∈ intrinsicInterior ℝ (convexHull ℝ (r : Set E))) :
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
      {a : Finset E | a ∈ L.faces ∧ a.card = 3 ∧ r ⊆ a}.ncard := by
  classical
  let fine : Set (Finset E) := {a | a ∈ L.faces ∧ a.card = 3 ∧ r ⊆ a}
  have hparents (a : Finset E) (ha : a ∈ fine) :
      ∃ t : Finset E, t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t ∧
        convexHull ℝ (a : Set E) ⊆ convexHull ℝ (t : Set E) :=
    (hLK.existsUnique_triangle_coface_parent hbound hs ha.1 ha.2.1 hxs
      (convexHull_mono ha.2.2 (intrinsicInterior_subset hxr))).exists
  choose parent hparent using hparents
  symm
  refine Set.ncard_congr parent (fun a ha => ?_) (fun a b ha hb he => ?_)
    (fun t ht => ?_)
  · exact ⟨(hparent a ha).1, (hparent a ha).2.1, (hparent a ha).2.2.1⟩
  · by_contra hab
    have hst : s ⊂ parent a ha := Finset.ssubset_iff_subset_ne.mpr
      ⟨(hparent a ha).2.2.1, fun h => by
        have hc := congrArg Finset.card h
        have hpc := (hparent a ha).2.1
        omega⟩
    exact K.fine_triangle_pair_not_in_one_coarse_triangle L hr ha.1 hb.1 hr2
      ha.2.1 hb.2.1 ha.2.2 hb.2.2 hab (hparent a ha).1 (hparent a ha).2.1 hst
      (hparent a ha).2.2.2 (he.symm ▸ (hparent b hb).2.2.2)
      hxr (intrinsicInterior_subset hxs)
  · obtain ⟨a, ha, ha3, hra, hat⟩ := hLK.exists_triangle_coface_in_parent hL hbound
      hs hs2 hr hr2 ht.1 ht.2.1 ht.2.2 hxs hxr
    have hafine : a ∈ fine := ⟨ha, ha3, hra⟩
    exact ⟨a, hafine, K.triangle_parent_unique L hbound ha ha3
      (hparent a hafine).1 ht.1 (hparent a hafine).2.2.2 hat⟩

end Paired

section Avoidance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_edge_interior_point_avoiding_finite
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (hs2 : s.card = 2) {p : E}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {U : Set E} (hU : IsOpen (Subtype.val ⁻¹' U : Set K.space)) (hpU : p ∈ U)
    {bad : Set E} (hbad : bad.Finite) :
    ∃ x : E, x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
      x ∉ bad ∧ x ∈ U := by
  classical
  have hpK := K.convexHull_subset_space hs (intrinsicInterior_subset hp)
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.mp hU
  have hpW : p ∈ W := hWU.symm.subset (show (⟨p, hpK⟩ : K.space) ∈
    Subtype.val ⁻¹' U from hpU)
  obtain ⟨u, v, huv, hsuv⟩ := Finset.card_eq_two.mp hs2
  have hex : ∃ w ∈ s, w ≠ p := by
    by_cases hup : u = p
    · refine ⟨v, hsuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
      intro hvp
      exact huv (hup.trans hvp.symm)
    · exact ⟨u, hsuv.symm ▸ Finset.mem_insert_self _ _, hup⟩
  obtain ⟨w, hw, hwp⟩ := hex
  let S := convexHull ℝ (s : Set E)
  let P := affineSpan ℝ S
  let pP : P := ⟨p, subset_affineSpan ℝ S (intrinsicInterior_subset hp)⟩
  have hpP : pP ∈ interior (Subtype.val ⁻¹' S : Set P) := by
    obtain ⟨y, hy, he⟩ := mem_intrinsicInterior.mp hp
    have hyP : y = pP := Subtype.ext he
    exact hyP ▸ hy
  have hdir : w - p ∈ P.direction := P.vsub_mem_direction
    (subset_affineSpan ℝ S (subset_convexHull ℝ (s : Set E) hw)) pP.property
  let line : ℝ → P := fun r =>
    ⟨r • (w - p) + p, P.vadd_mem_of_mem_direction (P.direction.smul_mem r hdir) pP.property⟩
  let raw : ℝ → E := fun r => r • (w - p) + p
  have hline : Continuous line :=
    ((continuous_id.smul continuous_const).add continuous_const).subtype_mk _
  have hraw : Continuous raw := by fun_prop
  have hzero : line 0 = pP := by apply Subtype.ext; simp [line, pP]
  let V := line ⁻¹' interior (Subtype.val ⁻¹' S : Set P) ∩ raw ⁻¹' W
  have hV : IsOpen V := (isOpen_interior.preimage hline).inter (hW.preimage hraw)
  have hzeroV : (0 : ℝ) ∈ V := by
    refine ⟨?_, ?_⟩
    · change line 0 ∈ interior (Subtype.val ⁻¹' S : Set P)
      rwa [hzero]
    · change raw 0 ∈ W
      simpa only [raw, zero_smul, zero_add] using hpW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzeroV)
  have hrawi : Function.Injective raw := by
    intro a b hab
    change a • (w - p) + p = b • (w - p) + p at hab
    exact smul_left_injective ℝ (sub_ne_zero.mpr hwp) (add_right_cancel hab)
  have hbad' : (raw ⁻¹' bad).Finite := hbad.preimage hrawi.injOn
  obtain ⟨r, hr, hrbad⟩ := (Ioo_infinite hε).exists_notMem_finite hbad'
  have hrV : r ∈ V := hball (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr.1]
      using hr.2)
  have hxS : raw r ∈ intrinsicInterior ℝ S := ⟨line r, hrV.1, rfl⟩
  refine ⟨raw r, hxS, hrbad, ?_⟩
  have hxK : raw r ∈ K.space := K.convexHull_subset_space hs (intrinsicInterior_subset hxS)
  exact hWU.subset (show (⟨raw r, hxK⟩ : K.space) ∈ Subtype.val ⁻¹' W from hrV.2)

theorem exists_edge_interior_point_avoiding_vertices
    (K L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2) {p : E}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {U : Set E} (hU : IsOpen (Subtype.val ⁻¹' U : Set K.space)) (hpU : p ∈ U) :
    ∃ x : E, x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
      x ∉ L.vertices ∧ x ∈ U :=
  K.exists_edge_interior_point_avoiding_finite hs hs2 hp hU hpU
    (L.finite_vertices_of_finite_faces hL)

end Avoidance

end Geometry.SimplicialComplex
