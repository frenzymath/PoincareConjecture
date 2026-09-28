import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryCrossings
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Final
import PoincareConjecture.Proofs.M76.Dehn.OriginalFaceDiskState
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FaceOrderIntersections
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Coordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteClippedChartInverse
import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFacetInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronNeighborhoodRetraction
import PoincareConjecture.Proofs.M76.Mathlib.CommonSimplicialRefinement

set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private theorem triangle_plane_projection
    (K : SimplicialComplex ℝ V3) {t : Finset V3}
    (ht : t ∈ K.faces) (ht3 : t.card = 3) :
    ∃ f : V3 →ᴬ[ℝ] V2, InjOn f (affineSpan ℝ (t : Set V3)) := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < t.card by omega)
  have hcoord : ∃ i : Fin 3, u i ≠ v i := by
    by_contra h
    apply huv
    funext i
    exact not_not.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hcoord
  let A : V3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj i).toContinuousAffineMap
  have hA : ∃ x ∈ affineSpan ℝ (t : Set V3),
      ∃ y ∈ affineSpan ℝ (t : Set V3), A x ≠ A y :=
    ⟨u, subset_affineSpan ℝ _ hu, v, subset_affineSpan ℝ _ hv, hi⟩
  obtain ⟨F, _, _, hplane⟩ :=
    (affineSpan ℝ (t : Set V3)).exists_centered_height_plane_coordinates (by simp)
      (K.finrank_faceDirection_of_card ht ht3) A.toAffineMap hA
      (subset_affineSpan ℝ _ hu)
  let f : V3 →ᴬ[ℝ] V2 :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.comp F.symm.toContinuousAffineMap
  refine ⟨f, ?_⟩
  intro x hx y hy hxy
  apply F.symm.injective
  apply Prod.ext
  · exact hxy
  · have hx0 : (F.symm x).2 = 0 := (hplane _).mp (by simpa using hx)
    have hy0 : (F.symm y).2 = 0 := (hplane _).mp (by simpa using hy)
    exact hx0.trans hy0.symm

private theorem affine_image_intrinsic_interior
    (f : V3 →ᴬ[ℝ] V2) {S : Set V3}
    (hf : InjOn f (affineSpan ℝ S)) {x : V3}
    (hx : x ∈ intrinsicInterior ℝ S) :
    f x ∈ intrinsicInterior ℝ (f '' S) := by
  rw [← intrinsicClosure_sdiff_intrinsicFrontier]
  refine ⟨subset_intrinsicClosure (mem_image_of_mem f (intrinsicInterior_subset hx)), ?_⟩
  intro hfront
  have himage : intrinsicFrontier ℝ (f '' S) = f '' intrinsicFrontier ℝ S :=
    f.toAffineMap.intrinsicFrontier_image_of_injOn S hf
  obtain ⟨y, hy, he⟩ := himage.subset hfront
  have hyS : y ∈ affineSpan ℝ S := intrinsicClosure_subset_affineSpan
    (by rw [← intrinsicClosure_sdiff_intrinsicInterior] at hy; exact hy.1)
  have hyx : y = x := hf hyS
    (subset_affineSpan ℝ _ (intrinsicInterior_subset hx)) he
  rw [hyx, ← intrinsicClosure_sdiff_intrinsicInterior] at hy
  exact hy.2 hx

private theorem fine_pair_not_in_one_triangle
    (K L : SimplicialComplex ℝ V3)
    {s a b r t : Finset V3} (hs : s ∈ L.faces)
    (ha : a ∈ L.faces) (hb : b ∈ L.faces)
    (hs2 : s.card = 2) (ha3 : a.card = 3) (hb3 : b.card = 3)
    (hsa : s ⊆ a) (hsb : s ⊆ b) (hab : a ≠ b)
    (ht : t ∈ K.faces) (ht3 : t.card = 3) (hrt : r ⊂ t)
    (hat : convexHull ℝ (a : Set V3) ⊆ convexHull ℝ (t : Set V3))
    (hbt : convexHull ℝ (b : Set V3) ⊆ convexHull ℝ (t : Set V3))
    {x : V3} (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)))
    (hxr : x ∈ convexHull ℝ (r : Set V3)) : False := by
  classical
  obtain ⟨f, hfi⟩ := triangle_plane_projection K ht ht3
  let N : SimplicialComplex ℝ V3 :=
    { faces := {u | u ∈ L.faces ∧
        convexHull ℝ (u : Set V3) ⊆ convexHull ℝ (t : Set V3)}
      indep := fun hu => L.indep hu.1
      isRelLowerSet_faces := by
        intro u hu
        exact ⟨L.nonempty_of_mem_faces hu.1, fun v hv hne =>
          ⟨L.down_closed hu.1 hv hne, (convexHull_mono hv).trans hu.2⟩⟩
      inter_subset_convexHull := fun hu hv => L.inter_subset_convexHull hu.1 hv.1 }
  have hNs : N.space ⊆ convexHull ℝ (t : Set V3) := by
    intro y hy
    obtain ⟨u, hu, hyu⟩ := SimplicialComplex.mem_space_iff.mp hy
    exact hu.2 hyu
  have hNa : a ∈ N.faces := ⟨ha, hat⟩
  have hNb : b ∈ N.faces := ⟨hb, hbt⟩
  have hNsface : s ∈ N.faces := ⟨hs, (convexHull_mono hsa).trans hat⟩
  have hNplane : N.space ⊆ affineSpan ℝ (t : Set V3) :=
    hNs.trans (convexHull_subset_affineSpan (s := (t : Set V3)))
  have hNi : InjOn f N.space := hfi.mono hNplane
  have hfN : N.AffineOnFaces f := N.affineOnFaces_affine f
  let M := hfN.embeddedImage hNi
  have hmem (u : Finset V3) (hu : u ∈ N.faces) : u.image f ∈ M.faces :=
    (hfN.image_mem_embeddedImage_iff hNi (N.subset_space hu)).mpr hu
  have hcard (u : Finset V3) (hu : u ∈ N.faces) : (u.image f).card = u.card :=
    Finset.card_image_iff.mpr (hNi.mono (N.subset_space hu))
  have habf : a.image f ≠ b.image f := by
    intro he
    apply hab
    apply Finset.coe_injective
    apply (hNi.image_eq_image_iff (N.subset_space hNa) (N.subset_space hNb)).mp
    exact (Finset.coe_image.symm.trans (congrArg (fun z : Finset V2 => (z : Set V2)) he)).trans
      Finset.coe_image
  have hfs : InjOn f (affineSpan ℝ (convexHull ℝ (s : Set V3))) := by
    rw [affineSpan_convexHull]
    exact hfi.mono (affineSpan_le.mpr
      ((subset_convexHull ℝ (s : Set V3)).trans
        (((convexHull_mono hsa).trans hat).trans
          (convexHull_subset_affineSpan (s := (t : Set V3))))))
  have hximage : f x ∈ intrinsicInterior ℝ (convexHull ℝ (s.image f : Set V2)) := by
    rw [Finset.coe_image, ← hfN.image_convexHull hNsface]
    exact affine_image_intrinsic_interior f hfs hxs
  have hxint := M.mem_interior_union_of_paired_facet
    (by rw [hcard s hNsface, hs2]; simp [Module.finrank_prod])
    (hmem a hNa) (hmem b hNb)
    (by rw [hcard a hNa, ha3]; simp [Module.finrank_prod])
    (by rw [hcard b hNb, hb3]; simp [Module.finrank_prod])
    (Finset.image_subset_image hsa) (Finset.image_subset_image hsb) habf hximage
  have himages (u : Finset V3) (hu : u ∈ N.faces)
      (hut : convexHull ℝ (u : Set V3) ⊆ convexHull ℝ (t : Set V3)) :
      convexHull ℝ (u.image f : Set V2) ⊆ f '' convexHull ℝ (t : Set V3) := by
    rw [Finset.coe_image, ← hfN.image_convexHull hu]
    exact image_mono hut
  have hxintT : f x ∈ interior (f '' convexHull ℝ (t : Set V3)) :=
    interior_mono (union_subset (himages a hNa hat) (himages b hNb hbt)) hxint
  have hxf : x ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) :=
    (K.indep ht).convexHull_subset_intrinsicFrontier hrt hxr
  have hfT : InjOn f (affineSpan ℝ (convexHull ℝ (t : Set V3))) := by
    rwa [affineSpan_convexHull]
  have hxfront : f x ∈ frontier (f '' convexHull ℝ (t : Set V3)) := by
    apply intrinsicFrontier_subset_frontier (𝕜 := ℝ)
    have he : intrinsicFrontier ℝ (f '' convexHull ℝ (t : Set V3)) =
        f '' intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) :=
      f.toAffineMap.intrinsicFrontier_image_of_injOn _ hfT
    exact he.symm.subset (mem_image_of_mem f hxf)
  exact hxfront.2 hxintT

private theorem original_cofaces_from_marked_refinement
    (K R : SimplicialComplex ℝ V3) (hR : R.faces.Finite)
    (hRK : R.IsSubdivision K) (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {q : V3 → V2} (hq : R.AffineOnFaces q) (hi : InjOn q R.space)
    {s r : Finset V3} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    (hr : r ∈ R.faces) (hr2 : r.card = 2)
    {x : V3} (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)))
    (hxr : x ∈ intrinsicInterior ℝ (convexHull ℝ (r : Set V3)))
    (hint : q x ∈ interior (q '' R.space)) :
    ∃ A B : Finset V3, A ∈ K.faces ∧ B ∈ K.faces ∧
      A.card = 3 ∧ B.card = 3 ∧ s ⊆ A ∧ s ⊆ B ∧ A ≠ B ∧
      ∀ t ∈ K.faces, s ⊆ t → t ⊆ A ∨ t ⊆ B := by
  classical
  let N := hq.embeddedImage hi
  have hN : N.faces.Finite := hq.embeddedImage_finite hi hR
  have hrN : r.image q ∈ N.faces :=
    (hq.image_mem_embeddedImage_iff hi (R.subset_space hr)).mpr hr
  have hcard : (r.image q).card = Module.finrank ℝ V2 := by
    rw [Finset.card_image_iff.mpr (hi.mono (R.subset_space hr)), hr2]
    simp [Module.finrank_prod]
  have hqx : q x ∈ convexHull ℝ (r.image q : Set V2) := by
    rw [Finset.coe_image, ← hq.image_convexHull hr]
    exact mem_image_of_mem q (intrinsicInterior_subset hxr)
  have hqxint : q x ∈ interior N.space := by
    rw [hq.embeddedImage_space hi]
    exact hint
  have hcount := N.faceLink_ncard_eq_two_of_hull_meets_interior
    hN hrN hcard ⟨q x, hqx, hqxint⟩
  rw [hq.ncard_embeddedImage_faceLink hi hr,
    R.ncard_faceLink_vertices_eq_cofaces, hr2] at hcount
  obtain ⟨a, b, hab, hset⟩ := ncard_eq_two.mp hcount
  have ha : a ∈ R.faces ∧ a.card = 3 ∧ r ⊆ a := by
    change a ∈ {u | u ∈ R.faces ∧ u.card = 3 ∧ r ⊆ u}
    rw [hset]
    exact Or.inl rfl
  have hb : b ∈ R.faces ∧ b.card = 3 ∧ r ⊆ b := by
    change b ∈ {u | u ∈ R.faces ∧ u.card = 3 ∧ r ⊆ u}
    rw [hset]
    exact Or.inr rfl
  have hcofaces : ∀ u ∈ R.faces, r ⊆ u → u ⊆ a ∨ u ⊆ b := by
    intro u hu hru
    have hu3 : u.card ≤ 3 := by
      simpa [Module.finrank_prod] using hq.face_card_le_of_injOn hi hu
    have hu2 := Finset.card_le_card hru
    by_cases he : u.card = 2
    · have hru' : r = u := Finset.eq_of_subset_of_card_le hru (by omega)
      exact Or.inl (hru' ▸ ha.2.2)
    · have humem : u ∈ {v | v ∈ R.faces ∧ v.card = 3 ∧ r ⊆ v} :=
        ⟨hu, by omega, hru⟩
      rw [hset] at humem
      exact humem.elim (fun h => Or.inl (h ▸ Finset.Subset.rfl))
        (fun h => Or.inr (h ▸ Finset.Subset.rfl))
  obtain ⟨A, hA, haA⟩ := hRK.face_subset a ha.1
  obtain ⟨B, hB, hbB⟩ := hRK.face_subset b hb.1
  have hsA : s ⊆ A := K.subset_of_mem_intrinsicInterior_face hs hA hxs
    (haA (convexHull_mono ha.2.2 (intrinsicInterior_subset hxr)))
  have hsB : s ⊆ B := K.subset_of_mem_intrinsicInterior_face hs hB hxs
    (hbB (convexHull_mono hb.2.2 (intrinsicInterior_subset hxr)))
  have hA3 : A.card = 3 := by
    have hle := (R.indep ha.1).card_le_card_of_subset_affineSpan
      ((subset_convexHull ℝ (a : Set V3)).trans
        (haA.trans (convexHull_subset_affineSpan (s := (A : Set V3)))))
    have hupper := hbound A hA
    omega
  have hB3 : B.card = 3 := by
    have hle := (R.indep hb.1).card_le_card_of_subset_affineSpan
      ((subset_convexHull ℝ (b : Set V3)).trans
        (hbB.trans (convexHull_subset_affineSpan (s := (B : Set V3)))))
    have hupper := hbound B hB
    omega
  have hAB : A ≠ B := by
    intro he
    have hsA' : s ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨hsA, by
      intro h
      have hc := congrArg Finset.card h
      omega⟩
    exact fine_pair_not_in_one_triangle K R hr ha.1 hb.1 hr2 ha.2.1 hb.2.1
      ha.2.2 hb.2.2 hab hA hA3 hsA' haA (he.symm ▸ hbB) hxr
      (intrinsicInterior_subset hxs)
  obtain ⟨U, hU, hxU, hRU⟩ :=
    R.exists_open_two_coface_carrier_germ hR hr ha.1 hb.1 hcofaces hxr
  refine ⟨A, B, hA, hB, hA3, hB3, hsA, hsB, hAB, ?_⟩
  intro t ht hst
  obtain ⟨y, hyt, hyU⟩ :=
    (convex_convexHull ℝ (t : Set V3)).intrinsicInterior_inter_open_nonempty hU
      ⟨x, convexHull_mono hst (intrinsicInterior_subset hxs), hxU⟩
  have hyR : y ∈ R.space := hRK.space_eq.symm.subset
    (K.convexHull_subset_space ht (intrinsicInterior_subset hyt))
  rcases (hRU y hyU).mp hyR with hya | hyb
  · exact Or.inl (K.subset_of_mem_intrinsicInterior_face ht hA hyt (haA hya))
  · exact Or.inr (K.subset_of_mem_intrinsicInterior_face ht hB hyt (hbB hyb))

private theorem original_edge_point_avoiding_vertices
    (K R : SimplicialComplex ℝ V3) (hR : R.faces.Finite)
    {q : V3 → V2} (hq : ContinuousOn q K.space)
    {s : Finset V3} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    {p : V3} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)))
    (hint : q p ∈ interior (q '' K.space)) :
    ∃ x : V3, x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)) ∧
      x ∉ R.vertices ∧ q x ∈ interior (q '' K.space) := by
  classical
  have hpK := K.convexHull_subset_space hs (intrinsicInterior_subset hp)
  let U : Set K.space := (fun x : K.space => q x) ⁻¹' interior (q '' K.space)
  have hU : IsOpen U := isOpen_interior.preimage hq.domRestrict
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.mp hU
  have hpU : (⟨p, hpK⟩ : K.space) ∈ U := hint
  have hpW : p ∈ W := hWU.symm.subset hpU
  obtain ⟨u, v, huv, hsuv⟩ := Finset.card_eq_two.mp hs2
  have hex : ∃ w ∈ s, w ≠ p := by
    by_cases hup : u = p
    · refine ⟨v, hsuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
      intro hvp
      exact huv (hup.trans hvp.symm)
    · exact ⟨u, hsuv.symm ▸ Finset.mem_insert_self _ _, hup⟩
  obtain ⟨w, hw, hwp⟩ := hex
  let S := convexHull ℝ (s : Set V3)
  let P := affineSpan ℝ S
  let pP : P := ⟨p, subset_affineSpan ℝ S (intrinsicInterior_subset hp)⟩
  have hpP : pP ∈ interior (Subtype.val ⁻¹' S : Set P) := by
    obtain ⟨y, hy, he⟩ := mem_intrinsicInterior.mp hp
    have hyP : y = pP := Subtype.ext he
    exact hyP ▸ hy
  have hdir : w - p ∈ P.direction := P.vsub_mem_direction
    (subset_affineSpan ℝ S (subset_convexHull ℝ (s : Set V3) hw)) pP.property
  let line : ℝ → P := fun r =>
    ⟨r • (w - p) + p, P.vadd_mem_of_mem_direction (P.direction.smul_mem r hdir) pP.property⟩
  let raw : ℝ → V3 := fun r => r • (w - p) + p
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
  have hbad : (raw ⁻¹' R.vertices).Finite :=
    (R.finite_vertices_of_finite_faces hR).preimage hrawi.injOn
  obtain ⟨r, hr, hrbad⟩ := (Ioo_infinite hε).exists_notMem_finite hbad
  have hrV : r ∈ V := hball (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr.1]
      using hr.2)
  have hxS : raw r ∈ intrinsicInterior ℝ S := ⟨line r, hrV.1, rfl⟩
  refine ⟨raw r, hxS, hrbad, ?_⟩
  have hxK : raw r ∈ K.space := K.convexHull_subset_space hs (intrinsicInterior_subset hxS)
  exact hWU.subset (show (⟨raw r, hxK⟩ : K.space) ∈ Subtype.val ⁻¹' W from hrV.2)

private theorem original_edge_cofaces_of_finite_parameter
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {q : V3 → V2} (hq : FinitePiecewiseAffineOn q K.space) (hi : InjOn q K.space)
    {s : Finset V3} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    {p : V3} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V3)))
    (hint : q p ∈ interior (q '' K.space)) :
    ∃ A B : Finset V3, A ∈ K.faces ∧ B ∈ K.faces ∧
      A.card = 3 ∧ B.card = 3 ∧ s ⊆ A ∧ s ⊆ B ∧ A ≠ B ∧
      ∀ t ∈ K.faces, s ⊆ t → t ⊆ A ∨ t ⊆ B := by
  classical
  have hqcont := hq.continuousOn
  obtain ⟨T, hT, hTK, hqT⟩ := hq
  obtain ⟨N, hN, hNK, hNT⟩ := K.exists_common_finite_subdivision T hK hT hTK.symm
  let J : SimplicialComplex ℝ V3 :=
    { faces := {u | u ∈ K.faces ∧ u ⊆ s}
      indep := fun hu => K.indep hu.1
      isRelLowerSet_faces := by
        intro u hu
        exact ⟨K.nonempty_of_mem_faces hu.1, fun v hv hne =>
          ⟨K.down_closed hu.1 hv hne, hv.trans hu.2⟩⟩
      inter_subset_convexHull := fun hu hv => K.inter_subset_convexHull hu.1 hv.1 }
  have hJ : J.faces.Finite := hK.subset (fun _ hu => hu.1)
  have hJs : J.space = convexHull ℝ (s : Set V3) := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, hxu⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact convexHull_mono hu.2 hxu
    · intro hx
      exact SimplicialComplex.mem_space_iff.mpr ⟨s, ⟨hs, Finset.Subset.rfl⟩, hx⟩
  have hJN : J.space ⊆ N.space := fun x hx =>
    hNK.space_eq.symm.subset (K.convexHull_subset_space hs (hJs.subset hx))
  obtain ⟨R, L, hR, hRN, hLR, hLs⟩ :=
    N.exists_subdivision_with_polyhedron_subcomplex J hN hJ hJN
  have hRK : R.IsSubdivision K := hRN.trans hNK
  have hqR : R.AffineOnFaces q := hRN.affineOnFaces (hNT.affineOnFaces hqT)
  have hiR : InjOn q R.space := hi.mono hRK.space_eq.subset
  have hRbound (u : Finset V3) (hu : u ∈ R.faces) : u.card ≤ 3 := by
    simpa [Module.finrank_prod] using hqR.face_card_le_of_injOn hiR hu
  have hbound (u : Finset V3) (hu : u ∈ K.faces) : u.card ≤ 3 :=
    K.face_card_le_of_hull_subset_finite_carrier R hR hu
      ((K.convexHull_subset_space hu).trans hRK.space_eq.symm.subset) hRbound
  obtain ⟨x, hxs, hxnot, hxq⟩ :=
    original_edge_point_avoiding_vertices K R hR hqcont hs hs2 hp hint
  have hxL : x ∈ L.space := (hLs.trans hJs).symm.subset (intrinsicInterior_subset hxs)
  obtain ⟨r, hr, hxr⟩ := L.exists_face_intrinsicInterior_of_finite (hR.subset hLR) hxL
  have hrR : r ∈ R.faces := hLR hr
  have hrsub : convexHull ℝ (r : Set V3) ⊆ convexHull ℝ (s : Set V3) :=
    (L.convexHull_subset_space hr).trans (hLs.trans hJs).subset
  have hrle : r.card ≤ 2 := by
    have h := (R.indep hrR).card_le_card_of_subset_affineSpan
      ((subset_convexHull ℝ (r : Set V3)).trans
        (hrsub.trans (convexHull_subset_affineSpan (s := (s : Set V3)))))
    omega
  have hrpos : 0 < r.card := Finset.card_pos.mpr (L.nonempty_of_mem_faces hr)
  have hrone : r.card ≠ 1 := by
    intro hc
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    have hxv : x = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        intrinsicInterior_subset hxr
    have hvR : v ∈ R.vertices := hrR
    exact hxnot (hxv.symm ▸ hvR)
  exact original_cofaces_from_marked_refinement K R hR hRK hbound hqR hiR hs hs2
    hrR (by omega) hxs hxr (by rwa [hRK.space_eq])

private theorem actual_clipped_parameter
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ (Fin 2 → ℝ)) (hK : K.faces.Finite)
    {j : (Fin 2 → ℝ) → X} (hj : PolyhedralPLInCharts e j K.space)
    (hi : InjOn j K.space) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ k, (e k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J L : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hL : L.faces.Finite)
    (hJQ : J.space ⊆ Q.target)
    (hLs : L.space = Q '' (j '' K.space ∩ Q.source) ∩ J.space) :
    ∃ q : V3 → V2, FinitePiecewiseAffineOn q L.space ∧ InjOn q L.space ∧
      ∀ x ∈ interior K.space, j x ∈ Q.source → Q (j x) ∈ interior J.space →
        q (Q (j x)) = (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) x ∧
          q (Q (j x)) ∈ interior (q '' L.space) := by
  obtain ⟨P, q₀, _hP, hPs, hq₀, _hq₀K, hright, hleft⟩ :=
    hj.exists_finite_clipped_chart_inverse K hK hi Q hQ J hJ hJQ
  have hLP : L.space = P.space := hLs.trans hPs.symm
  let e₂ := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let q : V3 → V2 := e₂ ∘ q₀
  have hq : FinitePiecewiseAffineOn q L.space :=
    (locallyPiecewiseAffineOn_affine
      e₂.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp_finitePiecewiseAffineOn
        (hq₀.restrict L hL hLP.subset) (mapsTo_univ _ _)
  have hqi : InjOn q L.space := by
    intro z hz w hw heq
    have he : q₀ z = q₀ w := e₂.injective heq
    exact (hright z (hLP.subset hz)).2.symm.trans
      ((congrArg (Q ∘ j) he).trans (hright w (hLP.subset hw)).2)
  refine ⟨q, hq, hqi, ?_⟩
  intro x hx hxQ hxJ
  have hleftx : q₀ (Q (j x)) = x :=
    hleft x (interior_subset hx) hxQ (interior_subset hxJ)
  have hvalue : q (Q (j x)) = e₂ x := congrArg e₂ hleftx
  refine ⟨hvalue, ?_⟩
  let O := interior K.space ∩ j ⁻¹' Q.source
  have hO : IsOpen O :=
    (hj.continuousOn.mono interior_subset).isOpen_inter_preimage
      isOpen_interior Q.open_source
  have hcomp : ContinuousOn (Q ∘ j) O := Q.continuousOn.comp
    (hj.continuousOn.mono (fun _ hy => interior_subset hy.1)) (fun _ hy => hy.2)
  have hN : IsOpen (O ∩ (Q ∘ j) ⁻¹' interior J.space) :=
    hcomp.isOpen_inter_preimage hO isOpen_interior
  have hsub : O ∩ (Q ∘ j) ⁻¹' interior J.space ⊆ q₀ '' L.space := by
    intro y hy
    refine ⟨Q (j y), ?_, hleft y (interior_subset hy.1.1) hy.1.2
      (interior_subset hy.2)⟩
    rw [hLs]
    exact ⟨⟨j y, ⟨mem_image_of_mem j (interior_subset hy.1.1), hy.1.2⟩, rfl⟩,
      interior_subset hy.2⟩
  have hxint : x ∈ interior (q₀ '' L.space) :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hN.mem_nhds ⟨⟨hx, hxQ⟩, hxJ⟩) hsub)
  rw [hvalue]
  have himage : e₂.toHomeomorph '' (q₀ '' L.space) = q '' L.space :=
    image_image e₂ q₀ L.space
  exact interior_mono himage.subset ((e₂.toHomeomorph.image_interior _).subset
    (mem_image_of_mem e₂ hxint))

end PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

open PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

open Classical in

theorem FaceMotionData.exists_original_pair_incidence
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} (hK : K.faces.Finite)
    (hK₀ : K₀ ≤ K) (hK₁ : K₁ ≤ K)
    {face : Finset V2} (hface : face ∈ K.faces) (hface3 : face.card = 3)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V2))
    {j jfinal : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : InjOn j K.space) (hjfinal : PolyhedralPLInCharts t.charts jfinal K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hjQ : MapsTo j (convexHull ℝ (face : Set V2)) Q.source)
    {B : OpenPartialHomeomorph s.Carrier V3}
    (hB : ∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (hval : ∀ z, Q z = B (step.projection (step.inclusion z)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    {J : SimplicialComplex ℝ V3} {U : K.faces → Set t.Carrier} {R Fmark : Set M}
    {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (hboundary : boundary = false)
    (hold : EqOn jfinal j K₀.space)
    (hnext : EqOn jfinal (motion.ambient 1 ∘ j) K₁.space)
    (old : K₀.faces) (hold3 : old.val.card = 3)
    (hcell : InjOn ((step.projection ∘ step.inclusion) ∘ jfinal)
      (convexHull ℝ (old.val : Set V2)))
    {x y : V2} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (face : Set V2)))
    (hxold : x ∉ K₀.space)
    (hy : y ∈ intrinsicInterior ℝ (convexHull ℝ (old.val : Set V2)))
    (hxy : step.projection (step.inclusion (jfinal x)) =
      step.projection (step.inclusion (jfinal y))) :
    ∃ (A : SimplicialComplex ℝ V3) (qA qB : V3 → ℝ × ℝ) (a b : Finset V3),
      A.faces.Finite ∧
      A.faces = (fun v => v.image (motion.coordinates.map 1)) '' motion.freeComplex.faces ∧
      A.space = motion.coordinates.map 1 '' motion.source.space ∧
      FinitePiecewiseAffineOn qA A.space ∧ InjOn qA A.space ∧
      FinitePiecewiseAffineOn qB (motion.targets old).space ∧
      InjOn qB (motion.targets old).space ∧
      a ∈ A.faces ∧ b ∈ (motion.targets old).faces ∧
      Q (jfinal x) = B (step.projection (step.inclusion (jfinal y))) ∧
      Q (jfinal x) ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V3)) ∧
      Q (jfinal x) ∈ intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) ∧
      qA (Q (jfinal x)) = (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) x ∧
      qB (Q (jfinal x)) = (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) y ∧
      qA (Q (jfinal x)) ∈ interior (qA '' A.space) ∧
      qB (Q (jfinal x)) ∈ interior (qB '' (motion.targets old).space) ∧
      affineSpan ℝ ((a : Set V3) ∪ (b : Set V3)) = ⊤ ∧
      ((a.card = 3 ∧ b.card = 3) ∨ (a.card = 2 ∧ b.card = 3) ∨
        (a.card = 3 ∧ b.card = 2)) ∧
      (a.card = 2 → ∃ u v : Finset V3,
        u ∈ A.faces ∧ v ∈ A.faces ∧ u.card = 3 ∧ v.card = 3 ∧
        a ⊆ u ∧ a ⊆ v ∧ u ≠ v ∧
        (∀ z ∈ A.faces, a ⊆ z → z ⊆ u ∨ z ⊆ v) ∧
        ∃ W : Set V3, IsOpen W ∧ Q (jfinal x) ∈ W ∧
          ∀ p ∈ W, p ∈ A.space ↔
            p ∈ convexHull ℝ (u : Set V3) ∪ convexHull ℝ (v : Set V3)) ∧
      (b.card = 2 → ∃ u v : Finset V3,
        u ∈ (motion.targets old).faces ∧ v ∈ (motion.targets old).faces ∧
        u.card = 3 ∧ v.card = 3 ∧ b ⊆ u ∧ b ⊆ v ∧ u ≠ v ∧
        (∀ z ∈ (motion.targets old).faces, b ⊆ z → z ⊆ u ∨ z ⊆ v) ∧
        ∃ W : Set V3, IsOpen W ∧ Q (jfinal x) ∈ W ∧
          ∀ p ∈ W, p ∈ (motion.targets old).space ↔
            p ∈ convexHull ℝ (u : Set V3) ∪ convexHull ℝ (v : Set V3)) := by
  classical
  have hfree : motion.freeComplex.faces.Finite :=
    motion.subdivision_finite.subset motion.free_le
  have hHaff : motion.freeComplex.AffineOnFaces (motion.coordinates.map 1) :=
    fun u hu => motion.endpoint_affine u (motion.free_le hu)
  have hHi : InjOn (motion.coordinates.map 1) motion.freeComplex.space :=
    (motion.coordinates.map 1).injective.injOn
  let A := hHaff.embeddedImage hHi
  have hA : A.faces.Finite := hHaff.embeddedImage_finite hHi hfree
  have hAs : A.space = motion.coordinates.map 1 '' motion.freeComplex.space :=
    hHaff.embeddedImage_space hHi
  have hK₁finite : K₁.faces.Finite := hK.subset hK₁
  have hK₁K := SimplicialComplex.space_subset_of_le hK₁
  have hsource : motion.freeComplex.space =
      Q '' (j '' K₁.space ∩ Q.source) ∩ motion.support.space :=
    motion.free_space.trans motion.source_space
  obtain ⟨q₀, hq₀, hq₀i, hq₀interior⟩ := actual_clipped_parameter K₁ hK₁finite
    (hj.restrict_finite K₁ hK₁finite hK₁K) (hji.mono hK₁K) Q hQ
    motion.support motion.freeComplex motion.support_finite hfree
    motion.support_upper hsource
  have hback : MapsTo (motion.coordinates.map 1).symm A.space
      motion.freeComplex.space := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hAs.subset hz
    simpa only [(motion.coordinates.map 1).symm_apply_apply] using hw
  let qA : V3 → ℝ × ℝ := q₀ ∘ (motion.coordinates.map 1).symm
  have hqA : FinitePiecewiseAffineOn qA A.space := hq₀.comp
    (motion.coordinates.finitePiecewiseAffineOn_finite_polyhedron 1 A hA).2 hback
  have hqAi : InjOn qA A.space := by
    intro z hz w hw heq
    exact (motion.coordinates.map 1).symm.injective (hq₀i (hback hz) (hback hw) heq)
  have hqimage : qA '' A.space = q₀ '' motion.freeComplex.space := by
    rw [hAs, image_image]
    congr 1
    funext z
    exact congrArg q₀ ((motion.coordinates.map 1).symm_apply_apply z)
  let Kold := K.vertexSubcomplex (old.val : Set V2)
  have holdK : old.val ∈ K.faces := hK₀ old.property
  have hKold : Kold.faces.Finite := K.vertexSubcomplex_finite _ hK
  have hKoldK : Kold.space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (K.vertexSubcomplex_le _)
  have hKolds : Kold.space = convexHull ℝ (old.val : Set V2) :=
    K.vertexSubcomplex_face_space holdK
  let lower := (step.projection ∘ step.inclusion) ∘ jfinal
  have hlower : PolyhedralPLInCharts s.charts lower K.space :=
    hjfinal.project step.chartIndex (step.projection.continuous.comp step.inclusion.continuous)
      step.chart_source (fun k z _ => congrFun (step.chart_forward k) z)
  obtain ⟨qB, hqB, hqBi, hqBinterior⟩ := actual_clipped_parameter Kold hKold
    (hlower.restrict_finite Kold hKold hKoldK) (hcell.mono hKolds.subset) B hB
    motion.support (motion.targets old) motion.support_finite (motion.targets_finite old)
    motion.support_lower (by
      rw [hKolds]
      exact motion.targets_space_of_prefix_agreement hold old)
  have hxnext : x ∈ K₁.space := hsucc.symm.subset (Or.inr (intrinsicInterior_subset hx))
  have hxQ := hjQ (intrinsicInterior_subset hx)
  have hxC := motion.active_supported x hxnext hxold
  have hcoord := motion.coordinate_of_successor_agreement hnext hxnext hxQ (interior_subset hxC)
  have hwholeint : motion.coordinates.map 1 '' interior motion.support.space =
      interior motion.support.space :=
    ((motion.coordinates.map 1).image_interior _).trans
      (congrArg interior (motion.coordinates.carrier 1))
  have hwint : Q (jfinal x) ∈ interior motion.support.space := by
    rw [hcoord]
    exact hwholeint.subset (mem_image_of_mem (motion.coordinates.map 1) hxC)
  have hxint : x ∈ interior K₁.space := by
    let Kface := K.vertexSubcomplex (face : Set V2)
    have hKfaces : Kface.space = convexHull ℝ (face : Set V2) :=
      K.vertexSubcomplex_face_space hface
    have hxface : x ∈ interior Kface.space := Kface.mem_interior_space_of_full_face
      (show face ∈ Kface.faces from ⟨hface, fun _ hv => hv⟩)
      (by simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hface3) hx
    exact interior_mono (hKfaces.subset.trans (fun _ hz => hsucc.symm.subset (Or.inr hz)))
      hxface
  have hyint : y ∈ interior Kold.space := Kold.mem_interior_space_of_full_face
    (show old.val ∈ Kold.faces from ⟨holdK, fun _ hv => hv⟩)
    (by simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hold3) hy
  obtain ⟨_hxQfinal, hyB, hcommon, _hwC, _hwsource, _hwfree, _hwtarget⟩ :=
    motion.original_pair_chart_coordinates hK₀ hface hsucc hji hjQ hval hmaps hold hnext
      old (intrinsicInterior_subset hx) hxold (intrinsicInterior_subset hy) hxy
  obtain ⟨hq₀value, hq₀int⟩ := hq₀interior x hxint hxQ hxC
  have hqAvalue : qA (Q (jfinal x)) = (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) x := by
    change q₀ ((motion.coordinates.map 1).symm (Q (jfinal x))) = _
    rw [hcoord, (motion.coordinates.map 1).symm_apply_apply]
    exact hq₀value
  have hqAint : qA (Q (jfinal x)) ∈ interior (qA '' A.space) := by
    rw [hqimage]
    change q₀ ((motion.coordinates.map 1).symm (Q (jfinal x))) ∈ _
    rwa [hcoord, (motion.coordinates.map 1).symm_apply_apply]
  obtain ⟨hqBvalue, hqBint⟩ := hqBinterior y hyint hyB (hcommon ▸ hwint)
  have hqBvalue' : qB (Q (jfinal x)) = (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) y := by
    rw [hcommon]
    exact hqBvalue
  have hqBint' : qB (Q (jfinal x)) ∈ interior (qB '' (motion.targets old).space) := by
    rw [hcommon]
    exact hqBint
  obtain ⟨a, b, ha, _ha0, hb, hxa, hyb, hacard, hbcard, hspan, hrank⟩ :=
    motion.exists_final_intersection_faces hK hK₀ hface hsucc hj hji hQ hval hmaps hold hnext
      (intrinsicInterior_subset hx) hxold hxQ old (intrinsicInterior_subset hy) hxy
  have haA : a.image (motion.coordinates.map 1) ∈ A.faces :=
    (hHaff.image_mem_embeddedImage_iff hHi (motion.freeComplex.subset_space ha)).mpr ha
  have hac : (a.image (motion.coordinates.map 1)).card = a.card :=
    Finset.card_image_iff.mpr (motion.coordinates.map 1).injective.injOn
  have hxa' : Q (jfinal x) ∈ intrinsicInterior ℝ
      (convexHull ℝ (a.image (motion.coordinates.map 1) : Set V3)) := by
    simpa only [Finset.coe_image] using hxa
  have hxb : Q (jfinal x) ∈ intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) := by
    rw [hcommon]
    exact hyb
  have hplane3 : Module.finrank ℝ motion.plane.direction = 3 := by
    rw [motion.interior_plane hboundary, AffineSubspace.direction_top, finrank_top]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [hplane3] at hrank
  have hcases : (a.card = 3 ∧ b.card = 3) ∨ (a.card = 2 ∧ b.card = 3) ∨
      (a.card = 3 ∧ b.card = 2) := by omega
  refine ⟨A, qA, qB, a.image (motion.coordinates.map 1), b, hA,
    hHaff.embeddedImage_faces hHi, hAs.trans (congrArg _ motion.free_space),
    hqA, hqAi, hqB, hqBi, haA, hb, hcommon, hxa', hxb, hqAvalue, hqBvalue',
    hqAint, hqBint', ?_, ?_, ?_, ?_⟩
  · simpa only [Finset.coe_image, motion.interior_plane hboundary] using hspan
  · rwa [hac]
  · intro ha2
    obtain ⟨u, v, hu, hv, hu3, hv3, hau, hav, huv, hexhaust⟩ :=
      original_edge_cofaces_of_finite_parameter A hA hqA hqAi haA ha2 hxa' hqAint
    obtain ⟨W, hW, hxW, hwhole⟩ :=
      A.exists_open_two_coface_carrier_germ hA haA hu hv hexhaust hxa'
    exact ⟨u, v, hu, hv, hu3, hv3, hau, hav, huv, hexhaust, W, hW, hxW, hwhole⟩
  · intro hb2
    obtain ⟨u, v, hu, hv, hu3, hv3, hbu, hbv, huv, hexhaust⟩ :=
      original_edge_cofaces_of_finite_parameter (motion.targets old)
        (motion.targets_finite old) hqB hqBi hb hb2 hxb hqBint'
    obtain ⟨W, hW, hxW, hwhole⟩ := (motion.targets old).exists_open_two_coface_carrier_germ
      (motion.targets_finite old) hb hu hv hexhaust hxb
    exact ⟨u, v, hu, hv, hu3, hv3, hbu, hbv, huv, hexhaust, W, hW, hxW, hwhole⟩

end Geometry.OriginalPLTower
