import PoincareConjecture.Proofs.M76.Mathlib.SingleVertexTriangleCollar
import PoincareConjecture.Proofs.M76.Mathlib.SingleVertexSlabCollarGluing
import PoincareConjecture.Proofs.M76.Mathlib.NontrivialTriangleSectionCover
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSingleVertexRoof
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets
import PoincareConjecture.Proofs.M76.Mathlib.TriangleResidualCertificate
import PoincareConjecture.Proofs.M76.Mathlib.CrossTriangleResidualIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineSlabComplex
import PoincareConjecture.Proofs.M76.Mathlib.TrivialSectionPositiveSlab
import PoincareConjecture.Proofs.M76.Mathlib.PureTriangleClosedStar










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]














theorem exists_finitePL_singleVertexSlab_with_contacts [DecidableEq E]
    (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    (hq : q ∈ closure ((K.space ∩ {x | A x = 0}) \ {q}))
    {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z) :
    ∃ (upper : E → ℝ) (T R : Set E) (J : SimplicialComplex ℝ E)
      (G : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T),
      G.IsFinitePL ∧
      J.faces.Finite ∧ J.space = R ∧
      T ∪ R = K.space ∩ {x | A x ∈ Icc 0 β} ∧
      R ∩ {x | A x = 0} ⊆ {q} ∧
      (∀ p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)},
        (G p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1) ∧
      (∀ c ∈ Ioo 0 β, R ∩ {x | A x = c} =
        AffineMap.homothety q (c / β) '' ((K.closedStar q).space ∩ {x | A x = β})) ∧
      (∀ c ∈ Ioo 0 β, (T ∩ R) ∩ {x | A x = c} =
        AffineMap.homothety q (c / β) '' ((K.link q).space ∩ {x | A x = β})) ∧
      FinitePiecewiseAffineOn upper (K.space ∩ {x | A x = 0}) ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, upper x ∈ Icc 0 β) ∧
      upper q = 0 ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, x ≠ q → 0 < upper x) ∧
      (T ⊆ K.space ∩ {x | A x ∈ Icc 0 β}) ∧
      (∀ p, A (G p) = (p : E × ℝ).2) ∧
      (∀ p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).2 = 0 → (G p : E) = (p : E × ℝ).1) ∧
      K.space ∩ {x | A x = 0} ⊆ T := by
  classical
  let ι := {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
    ∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q}
  have hfinite : {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
      ∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q}.Finite :=
    hK.subset fun _ hs => hs.1
  let : Fintype ι := hfinite.fintype
  let B : ι → Set E := fun i => convexHull ℝ (i.val : Set E) ∩ {x | A x = 0}
  have hB : (⋃ i, B i) = K.space ∩ {x | A x = 0} :=
    K.iUnion_nontrivial_triangle_sections hK hpure A hq
  choose S T H hH hgeometry hsource hbound hbase hdown htarget hheight hbottom hcollapse hedge
    hpositive using
    fun i : ι => K.exists_singleVertex_triangle_collar_with_geometry A hqK hAq hβ hreg
      i.property.1 i.property.2.1 i.property.2.2
  have hone (z : E) (hz : z ∈ K.vertices) (hAz : A z ∈ Icc 0 β) : z = q := by
    by_contra hzq
    rcases hreg z hz hzq with h | h
    · exact h.not_ge hAz.1
    · exact h.not_ge hAz.2
  obtain ⟨F, hF, hFheight, hFbottom, hFres⟩ := K.exists_singleVertexSlab_collar_iUnion
    A hAq hβ.le hone (fun i : ι => i.val) (fun i => i.property.1)
    (fun i => i.property.2.1) Subtype.val_injective S T H hH
    (fun i p => (hbound i p.property).1.1)
    (fun i p => (hbound i p.property).1.2)
    (fun i p => (hbound i p.property).2)
    htarget hheight hbottom hcollapse hedge
  obtain ⟨upper, hupperPL, hupper, hband, hpieces⟩ :=
    K.exists_finitePL_singleVertex_source_roof_with_pieces
    hK A hqK hAq hβ hone (fun i : ι => i.val) (fun i => i.property.1)
    (fun i => i.property.2.1) Subtype.val_injective S hB hsource
  let G := (Homeomorph.setCongr hband.symm).trans
    (F.trans (Homeomorph.setCongr (rfl : (⋃ i, T i) = ⋃ i, T i)))
  have hGheight (p) : A (G p) = (p : E × ℝ).2 :=
    hFheight ⟨p, hband.symm ▸ p.property⟩
  have hGbottom (p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (upper p.1)}) (ht : (p : E × ℝ).2 = 0) :
      (G p : E) = (p : E × ℝ).1 :=
    hFbottom ⟨p, hband.symm ▸ p.property⟩ ht
  have hqzero : upper q = 0 := by
    have hqB : q ∈ K.space ∩ {x | A x = 0} :=
      ⟨K.vertices_subset_space hqK, hAq⟩
    have htop : (q, upper q) ∈ ⋃ i, S i := by
      rw [hband]
      exact ⟨hqB, (hupper q hqB).1, le_rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp htop
    exact hcollapse i ⟨(q, upper q), hi⟩ rfl
  choose a habound haband harestrict using hpieces
  choose R J hJ hJR hpartition hRzero hRtop hRmissing hRradial hRcontact hRboundary
    using fun i : ι =>
    A.exists_triangle_collar_residual_with_contacts hAq hβ (H i) (hH i)
      (hgeometry i) (hsource i) (hheight i)
  have hboundary (i : ι) (p : S i) :
      (H i p : E) ∈ R i ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
    rw [hRboundary i (a i) (habound i) (haband i) p,
      harestrict i (hbound i p.property).1]
  let κ := {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
    ¬∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q}
  have hκ : {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
      ¬∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q}.Finite :=
    hK.subset fun _ hs => hs.1
  let : Fintype κ := hκ.fintype
  obtain ⟨V, hV, hVs, _⟩ := exists_finite_triangulation_iUnion_convexHull
    (fun j : κ => j.val) (fun j => K.indep j.property.1)
  obtain ⟨U, hU, hUs⟩ := V.exists_finite_affineSlab_complex hV A 0 β
  have hUspace : U.space =
      (⋃ j : κ, convexHull ℝ (j.val : Set E)) ∩ {x | A x ∈ Icc 0 β} := by
    rw [hUs, hVs]
  have htrivial (j : κ) : convexHull ℝ (j.val : Set E) ∩ {x | A x = 0} ⊆ {q} := by
    intro x hx
    apply mem_singleton_iff.mpr
    by_contra hxq
    exact j.property.2.2 ⟨x, hx, hxq⟩
  obtain ⟨L, hL, hLs, _⟩ := exists_finite_triangulation_iUnion J hJ
  obtain ⟨Z, hZ, hZs⟩ := L.exists_finite_triangulation_union U hL hU
  have hZspace : Z.space = (⋃ i, R i) ∪ U.space := by
    simpa only [hLs, hJR] using hZs
  have hzero : Z.space ∩ {x | A x = 0} ⊆ {q} := by
    intro x hx
    rcases hZspace.subset hx.1 with hR | hU
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hR
      exact hRzero i ⟨hi, hx.2⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hUspace.subset hU).1
      exact htrivial j ⟨hj, hx.2⟩
  have hfull : (⋃ i, T i) ∪ Z.space = K.space ∩ {x | A x ∈ Icc 0 β} := by
    ext x
    constructor
    · rintro (hxT | hxR)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hxT
        have hx := (hpartition i).subset (Or.inl hi)
        exact ⟨K.convexHull_subset_space i.property.1 hx.1, hx.2⟩
      · rcases hZspace.subset hxR with hR | hU
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hR
          have hx := (hpartition i).subset (Or.inr hi)
          exact ⟨K.convexHull_subset_space i.property.1 hx.1, hx.2⟩
        · have hx := hUspace.subset hU
          obtain ⟨j, hj⟩ := mem_iUnion.mp hx.1
          exact ⟨K.convexHull_subset_space j.property.1 hj, hx.2⟩
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx.1
      obtain ⟨t, ht, htc, hst⟩ := hpure s hs
      have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono hst hxs
      by_cases hnontriv : ∃ z ∈ convexHull ℝ (t : Set E) ∩ {x | A x = 0}, z ≠ q
      · let i : ι := ⟨t, ht, htc, hnontriv⟩
        rcases (hpartition i).symm.subset ⟨hxt, hx.2⟩ with hi | hi
        · exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
        · exact Or.inr (hZspace.symm.subset (Or.inl (mem_iUnion.mpr ⟨i, hi⟩)))
      · let j : κ := ⟨t, ht, htc, hnontriv⟩
        exact Or.inr (hZspace.symm.subset (Or.inr
          (hUspace.symm.subset ⟨mem_iUnion.mpr ⟨j, hxt⟩, hx.2⟩)))
  have hinter (p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (upper p.1)}) :
      (G p : E) ∈ Z.space ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hband.symm.subset p.property)
    let pi : S i := ⟨p, hi⟩
    have hGval : (G p : E) = H i pi := hFres i pi
    have hxbound : A (H i pi) ∈ Icc 0 β := by
      rw [hheight]
      exact (hbound i pi.property).2
    have hcol : (pi : E × ℝ).1 = q → A (H i pi) = 0 :=
      fun h => (hheight i pi).trans (hcollapse i pi h)
    have hbot : A (H i pi) = 0 → (H i pi : E) = (pi : E × ℝ).1 :=
      fun h => hbottom i pi ((hheight i pi).symm.trans h)
    have hedge' (e : Finset E) (he : e.card = 2) (hes : e ⊆ i.val)
        (hxe : (H i pi : E) ∈ convexHull ℝ (e : Set E)) :
        (pi : E × ℝ).1 ∈ convexHull ℝ (e : Set E) := (hedge i e he hes pi).mpr hxe
    have hatq (hxq : (H i pi : E) = q) :
        (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
      have ht0 : (p : E × ℝ).2 = 0 :=
        (hheight i pi).symm.trans ((congrArg A hxq).trans hAq)
      have hpq : (p : E × ℝ).1 = q := (hbottom i pi ht0).symm.trans hxq
      rw [ht0, hpq, hqzero]
    rw [hGval, hZspace]
    constructor
    · rintro (hxR | hxU)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
        by_cases hij : i = j
        · subst j
          exact (hboundary i pi).mp hj
        have hxj := (hpartition j).subset (Or.inr hj)
        have hxcase := K.eq_vertex_or_top_of_collar_residual_intersection A hAq hone
          i.property.1 j.property.1 i.property.2.1 j.property.2.1
          (fun h => hij (Subtype.ext h)) (htarget i (H i pi).property) hxj.1 hxbound
          (hbound i pi.property).1.2 hcol hbot hedge'
          (fun e he hej hqe hxe => hRtop j e he hej hqe _ ⟨hj, hxe⟩)
        rcases hxcase with hxq | hxtop
        · exact hatq hxq
        · have ht : (p : E × ℝ).2 = β := (hheight i pi).symm.trans hxtop
          exact le_antisymm p.property.2.2 (by rw [ht]; exact (hupper _ p.property.1).2)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp (hUspace.subset hxU).1
        have hneq : i.val ≠ j.val := by
          intro heq
          apply j.property.2.2
          simpa only [← heq] using i.property.2.2
        apply hatq
        exact K.eq_vertex_of_collar_trivial_section_intersection A hone
          i.property.1 j.property.1 i.property.2.1 j.property.2.1 hneq
          (htarget i (H i pi).property) hj hxbound (hbound i pi.property).1.2
          hcol hbot hedge' (htrivial j)
    · intro ht
      exact Or.inl (mem_iUnion.mpr ⟨i, (hboundary i pi).mpr ht⟩)
  have hradial (c : ℝ) (hc : c ∈ Ioo 0 β) : Z.space ∩ {x | A x = c} =
      AffineMap.homothety q (c / β) '' ((K.closedStar q).space ∩ {x | A x = β}) := by
    ext x
    constructor
    · intro hx
      rcases hZspace.subset hx.1 with hxR | hxU
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hxR
        by_cases hqi : q ∈ i.val
        · obtain ⟨y, hy, hxy⟩ := (hRradial i hqi c ⟨hc.1, hc.2.le⟩).subset ⟨hi, hx.2⟩
          exact ⟨y, ⟨(K.mem_closedStar_space_iff_triangle hpure q y).mpr
            ⟨i.val, i.property.1, i.property.2.1, hqi, hy.1⟩, hy.2⟩, hxy⟩
        · exact (notMem_empty x ((hRmissing i hqi c hc).subset ⟨hi, hx.2⟩)).elim
      · obtain ⟨j, hj⟩ := mem_iUnion.mp (hUspace.subset hxU).1
        have hxpositive : A x ∈ Ioc 0 β := by rw [hx.2]; exact ⟨hc.1, hc.2.le⟩
        have hqj := (K.vertex_and_positive_others_of_trivial_section_slab_point
          A hqK hreg j.property.1 (htrivial j) hj hxpositive).1
        obtain ⟨y, hy, hxy⟩ := (K.trivial_section_triangle_level_homothety A hqK hAq hβ hreg
          j.property.1 j.property.2.1 (htrivial j) ⟨hc.1, hc.2.le⟩).subset ⟨hj, hx.2⟩
        exact ⟨y, ⟨(K.mem_closedStar_space_iff_triangle hpure q y).mpr
          ⟨j.val, j.property.1, j.property.2.1, hqj, hy.1⟩, hy.2⟩, hxy⟩
    · rintro ⟨y, ⟨hystar, hyβ⟩, rfl⟩
      obtain ⟨s, hs, hsc, hqs, hys⟩ := (K.mem_closedStar_space_iff_triangle hpure q y).mp hystar
      by_cases hnontriv : ∃ z ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, z ≠ q
      · let i : ι := ⟨s, hs, hsc, hnontriv⟩
        have hz := (hRradial i hqs c ⟨hc.1, hc.2.le⟩).symm.subset ⟨y, ⟨hys, hyβ⟩, rfl⟩
        exact ⟨hZspace.symm.subset (Or.inl (mem_iUnion.mpr ⟨i, hz.1⟩)), hz.2⟩
      · let j : κ := ⟨s, hs, hsc, hnontriv⟩
        have hz := (K.trivial_section_triangle_level_homothety A hqK hAq hβ hreg hs hsc
          (htrivial j) ⟨hc.1, hc.2.le⟩).symm.subset ⟨y, ⟨hys, hyβ⟩, rfl⟩
        refine ⟨hZspace.symm.subset (Or.inr (hUspace.symm.subset
          ⟨mem_iUnion.mpr ⟨j, hz.1⟩, ?_⟩)), hz.2⟩
        change A (AffineMap.homothety q (c / β) y) ∈ Icc 0 β
        rw [hz.2]
        exact ⟨hc.1.le, hc.2.le⟩
  have hcontact (c : ℝ) (hc : c ∈ Ioo 0 β) :
      ((⋃ i, T i) ∩ Z.space) ∩ {x | A x = c} =
        AffineMap.homothety q (c / β) '' ((K.link q).space ∩ {x | A x = β}) := by
    ext x
    constructor
    · intro hx
      let p := G.symm ⟨x, hx.1.1⟩
      have hGp : (G p : E) = x := congrArg Subtype.val (G.apply_symm_apply _)
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hband.symm.subset p.property)
      let pi : S i := ⟨p, hi⟩
      have hHpi : (H i pi : E) = x := (hFres i pi).symm.trans hGp
      have hxRi : x ∈ R i := by
        rw [← hHpi, hboundary]
        exact (hinter p).mp (hGp.symm ▸ hx.1.2)
      have hqi : q ∈ i.val := by
        by_contra h
        exact notMem_empty x ((hRmissing i h c hc).subset ⟨hxRi, hx.2⟩)
      have hxTi : x ∈ T i := hHpi ▸ (H i pi).property
      obtain ⟨y, hy, hxy⟩ := (hRcontact i hqi c ⟨hc.1, hc.2.le⟩).subset
        ⟨⟨hxTi, hxRi⟩, hx.2⟩
      exact ⟨y, ⟨(K.mem_link_space_iff_triangle hpure q y).mpr
        ⟨i.val, i.property.1, i.property.2.1, hqi, hy.1⟩, hy.2⟩, hxy⟩
    · rintro ⟨y, ⟨hylink, hyβ⟩, rfl⟩
      obtain ⟨s, hs, hsc, hqs, hys⟩ := (K.mem_link_space_iff_triangle hpure q y).mp hylink
      have hnontriv : ∃ z ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, z ≠ q := by
        by_contra h
        have hsection : convexHull ℝ (s : Set E) ∩ {x | A x = 0} ⊆ {q} := by
          intro z hz
          exact mem_singleton_iff.mpr (by by_contra hzq; exact h ⟨z, hz, hzq⟩)
        have hother := (K.vertex_and_positive_others_of_trivial_section_slab_point
          A hqK hreg hs hsection (convexHull_mono sdiff_subset hys)
          (show A y ∈ Ioc 0 β by rw [hyβ]; exact ⟨hβ, le_rfl⟩)).2
        have hyabove : β < A y := convexHull_min
          (fun z hz => hother z hz.1 hz.2) ((convex_Ioi β).affine_preimage A) hys
        exact hyabove.ne' hyβ
      let i : ι := ⟨s, hs, hsc, hnontriv⟩
      have hx := (hRcontact i hqs c ⟨hc.1, hc.2.le⟩).symm.subset ⟨y, ⟨hys, hyβ⟩, rfl⟩
      exact ⟨⟨mem_iUnion.mpr ⟨i, hx.1.1⟩,
        hZspace.symm.subset (Or.inl (mem_iUnion.mpr ⟨i, hx.1.2⟩))⟩, hx.2⟩
  refine ⟨upper, ⋃ i, T i, Z.space, Z, G, hF.setCongr hband rfl,
    hZ, rfl, hfull, hzero, hinter, hradial, hcontact, hupperPL, hupper, hqzero, ?_, ?_,
    hGheight, hGbottom, ?_⟩
  · intro x hx hxq
    have hxB : x ∈ ⋃ i, B i := hB.symm ▸ hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxB
    obtain ⟨t, ht, hxt⟩ := hpositive i x hi hxq
    have hp : (x, t) ∈ {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)} := hband ▸ mem_iUnion.mpr ⟨i, hxt⟩
    exact ht.trans_le hp.2.2
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    let p := (H i).symm ⟨x, hi⟩
    have hval : (H i p : E) = x := congrArg Subtype.val ((H i).apply_symm_apply _)
    refine ⟨K.convexHull_subset_space i.property.1 (htarget i hi), ?_⟩
    change A x ∈ Icc 0 β
    rw [← hval, hheight i p]
    exact (hbound i p.property).2
  · intro x hx
    let p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)} := ⟨(x, 0), hx, le_rfl, (hupper x hx).1⟩
    have hval : (G p : E) = x := hGbottom p rfl
    rw [← hval]
    exact (G p).property





theorem exists_finitePL_singleVertexSlab_with_radial_residual [DecidableEq E]
    (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    (hq : q ∈ closure ((K.space ∩ {x | A x = 0}) \ {q}))
    {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z) :
    ∃ (upper : E → ℝ) (T R : Set E) (J : SimplicialComplex ℝ E)
      (G : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T),
      G.IsFinitePL ∧
      J.faces.Finite ∧ J.space = R ∧
      T ∪ R = K.space ∩ {x | A x ∈ Icc 0 β} ∧
      R ∩ {x | A x = 0} ⊆ {q} ∧
      (∀ p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)},
        (G p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1) ∧
      (∀ c ∈ Ioo 0 β, R ∩ {x | A x = c} =
        AffineMap.homothety q (c / β) '' ((K.closedStar q).space ∩ {x | A x = β})) ∧
      FinitePiecewiseAffineOn upper (K.space ∩ {x | A x = 0}) ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, upper x ∈ Icc 0 β) ∧
      upper q = 0 ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, x ≠ q → 0 < upper x) ∧
      (T ⊆ K.space ∩ {x | A x ∈ Icc 0 β}) ∧
      (∀ p, A (G p) = (p : E × ℝ).2) ∧
      (∀ p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).2 = 0 → (G p : E) = (p : E × ℝ).1) ∧
      K.space ∩ {x | A x = 0} ⊆ T := by
  obtain ⟨upper, T, R, J, G, hG, hJ, hJR, hfull, hzero, hinter, hradial, _, hrest⟩ :=
    K.exists_finitePL_singleVertexSlab_with_contacts hK hpure A hqK hAq hq hβ hreg
  exact ⟨upper, T, R, J, G, hG, hJ, hJR, hfull, hzero, hinter, hradial, hrest⟩











theorem exists_finitePL_singleVertexSlab_with_residual (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    (hq : q ∈ closure ((K.space ∩ {x | A x = 0}) \ {q}))
    {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z) :
    ∃ (upper : E → ℝ) (T R : Set E) (J : SimplicialComplex ℝ E)
      (G : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T),
      G.IsFinitePL ∧
      J.faces.Finite ∧ J.space = R ∧
      T ∪ R = K.space ∩ {x | A x ∈ Icc 0 β} ∧
      R ∩ {x | A x = 0} ⊆ {q} ∧
      (∀ p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)},
        (G p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1) ∧
      FinitePiecewiseAffineOn upper (K.space ∩ {x | A x = 0}) ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, upper x ∈ Icc 0 β) ∧
      upper q = 0 ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, x ≠ q → 0 < upper x) ∧
      (T ⊆ K.space ∩ {x | A x ∈ Icc 0 β}) ∧
      (∀ p, A (G p) = (p : E × ℝ).2) ∧
      (∀ p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).2 = 0 → (G p : E) = (p : E × ℝ).1) ∧
      K.space ∩ {x | A x = 0} ⊆ T := by
  classical
  obtain ⟨upper, T, R, J, G, hG, hJ, hJR, hfull, hzero, hinter, _, hrest⟩ :=
    K.exists_finitePL_singleVertexSlab_with_radial_residual hK hpure A hqK hAq hq hβ hreg
  exact ⟨upper, T, R, J, G, hG, hJ, hJR, hfull, hzero, hinter, hrest⟩









theorem exists_finitePL_singleVertexSlab_with_roof (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    (hq : q ∈ closure ((K.space ∩ {x | A x = 0}) \ {q}))
    {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z) :
    ∃ (upper : E → ℝ) (T : Set E)
      (G : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T),
      G.IsFinitePL ∧
      FinitePiecewiseAffineOn upper (K.space ∩ {x | A x = 0}) ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, upper x ∈ Icc 0 β) ∧
      upper q = 0 ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, x ≠ q → 0 < upper x) ∧
      (T ⊆ K.space ∩ {x | A x ∈ Icc 0 β}) ∧
      (∀ p, A (G p) = (p : E × ℝ).2) ∧
      (∀ p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).2 = 0 → (G p : E) = (p : E × ℝ).1) ∧
      K.space ∩ {x | A x = 0} ⊆ T := by
  obtain ⟨upper, T, _, _, G, hG, _, _, _, _, _, hrest⟩ :=
    K.exists_finitePL_singleVertexSlab_with_residual hK hpure A hqK hAq hq hβ hreg
  exact ⟨upper, T, G, hG, hrest⟩








theorem exists_finitePL_singleVertexSlab (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    (hq : q ∈ closure ((K.space ∩ {x | A x = 0}) \ {q}))
    {β : ℝ} (hβ : 0 < β)
    (hreg : ∀ z ∈ K.vertices, z ≠ q → A z < 0 ∨ β < A z) :
    ∃ (upper : E → ℝ) (T : Set E)
      (G : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T),
      G.IsFinitePL ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, upper x ∈ Icc 0 β) ∧
      upper q = 0 ∧
      (∀ x ∈ K.space ∩ {x | A x = 0}, x ≠ q → 0 < upper x) ∧
      (T ⊆ K.space ∩ {x | A x ∈ Icc 0 β}) ∧
      (∀ p, A (G p) = (p : E × ℝ).2) ∧
      (∀ p : {p : E × ℝ | p.1 ∈ K.space ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).2 = 0 → (G p : E) = (p : E × ℝ).1) ∧
      K.space ∩ {x | A x = 0} ⊆ T := by
  obtain ⟨upper, T, G, hG, _, hrest⟩ :=
    K.exists_finitePL_singleVertexSlab_with_roof hK hpure A hqK hAq hq hβ hreg
  exact ⟨upper, T, G, hG, hrest⟩

end Geometry.SimplicialComplex
