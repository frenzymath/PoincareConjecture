import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexProducts
import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexExtension
import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBandGluing
import PoincareConjecture.Proofs.M76.Rigidity.OriginalLowerProductConstruction









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  {T : OriginalProperDiskTriangulation e R j}



theorem OriginalLowerProducts.exists_vertex_products_of_bands
    (P : OriginalLowerProducts T)
    (F : ∀ p : (T.marked 2).vertices, OriginalVertexBand P p) :
    Nonempty (OriginalVertexProducts T) := by
  classical
  let E := T.index → ℝ × V3
  choose H hH hcenter hside hproper using fun p => (F p).exists_product
  choose f hf hvalue using hH
  have hinj (p : (T.marked 2).vertices) :
      InjOn (f p) (T.diskDualBase {(p : E)} ×ˢ I) := by
    intro x hx y hy he
    have hxy : H p ⟨x, hx⟩ = H p ⟨y, hy⟩ :=
      Subtype.ext ((hvalue p ⟨x, hx⟩).trans (he.trans (hvalue p ⟨y, hy⟩).symm))
    exact congrArg Subtype.val ((H p).injective hxy)
  have himage (p : (T.marked 2).vertices) :
      f p '' (T.diskDualBase {(p : E)} ×ˢ I) = T.dualRegion {(p : E)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hvalue p ⟨y, hy⟩]
      exact (H p ⟨y, hy⟩).property
    · intro hx
      let y := (H p).symm ⟨x, hx⟩
      refine ⟨y, y.property, ?_⟩
      rw [← hvalue p y]
      exact congrArg Subtype.val ((H p).apply_symm_apply ⟨x, hx⟩)
  have hkeep (p : (T.marked 2).vertices) {s : Finset E}
      (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 2) (hps : (p : E) ∈ s)
      (x : E × ℝ) (hx : x ∈ T.diskDualBase s ×ˢ I) : f p x = P.map s x := by
    have hsingle : {(p : E)} ∈ (T.marked 2).faces := p.property
    have hstrict : ({(p : E)} : Finset E) ⊂ s := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.singleton_subset_iff.mpr hps, ?_⟩
      intro he
      have hc : 1 = 2 := by
        simpa only [Finset.card_singleton, hcard] using congrArg Finset.card he
      omega
    have hxq : x ∈ (T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) ×ˢ I :=
      ⟨⟨T.dualRegion_subset_rim_of_ssubset hsingle hstrict hx.1.1, hx.1.2⟩, hx.2⟩
    have hxB : x ∈ T.diskDualBase {(p : E)} ×ˢ I :=
      ⟨(T.vertex_base_ballPair p).1 hxq.1, hx.2⟩
    exact (hvalue p ⟨x, hxB⟩).symm.trans
      ((hside p x hxq).trans ((F p).keep_face s hs hcard.ge hps x hx))
  have hpairs (p q : (T.marked 2).vertices) :
      T.diskDualBase {(p : E)} ∩ T.diskDualBase {(q : E)} =
        T.diskDualBase {(p : E), (q : E)} ∧
      T.dualRegion {(p : E)} ∩ T.dualRegion {(q : E)} =
        T.dualRegion {(p : E), (q : E)} := by
    have he : T.dualRegion {(p : E)} ∩ T.dualRegion {(q : E)} =
        T.dualRegion {(p : E), (q : E)} := by
      simpa only [Finset.singleton_union] using T.dualRegion_inter {(p : E)} {(q : E)}
    refine ⟨?_, he⟩
    change (T.dualRegion {(p : E)} ∩ (T.marked 2).space) ∩
      (T.dualRegion {(q : E)} ∩ (T.marked 2).space) =
        T.dualRegion {(p : E), (q : E)} ∩ (T.marked 2).space
    rw [← he]
    ext x
    simp only [mem_inter_iff]
    tauto
  have hempty (p q : (T.marked 2).vertices)
      (hs : ({(p : E), (q : E)} : Finset E) ∉ (T.marked 2).faces) :
      T.dualRegion {(p : E), (q : E)} = ∅ := by
    apply T.dualRegion_eq_empty_of_not_disk_face
      ⟨p, Finset.mem_insert_self _ _⟩ ?_ hs
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact p.property
    · exact q.property
  refine ⟨{
    map := f
    piecewiseAffine := hf
    injective := hinj
    image_eq := himage
    central := ?_
    proper := ?_
    agrees := ?_
    overlap_image := ?_ }⟩
  · intro p x hx
    exact (hvalue p ⟨(x, 0), ⟨hx, by norm_num⟩⟩).symm.trans (hcenter p x hx)
  · intro p x hx
    rw [← hvalue p ⟨x, hx⟩]
    exact hproper p ⟨x, hx⟩
  · intro p q x hx
    by_cases hpq : p = q
    · subst q
      rfl
    have hpq' : (p : E) ≠ (q : E) := fun he => hpq (Subtype.ext he)
    have hcard : ({(p : E), (q : E)} : Finset E).card = 2 := Finset.card_pair hpq'
    by_cases hs : ({(p : E), (q : E)} : Finset E) ∈ (T.marked 2).faces
    · have hxs : x ∈ T.diskDualBase {(p : E), (q : E)} ×ˢ I :=
        ⟨(hpairs p q).1.subset hx.1, hx.2⟩
      exact (hkeep p hs hcard (Finset.mem_insert_self _ _) x hxs).trans
        (hkeep q hs hcard (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) x hxs).symm
    · have hxs := (hpairs p q).1.subset hx.1
      have hxN : x.1 ∈ T.dualRegion {(p : E), (q : E)} := hxs.1
      rw [hempty p q hs] at hxN
      exact False.elim hxN
  · intro p q
    by_cases hpq : p = q
    · subst q
      simpa only [inter_self] using himage p
    have hpq' : (p : E) ≠ (q : E) := fun he => hpq (Subtype.ext he)
    have hcard : ({(p : E), (q : E)} : Finset E).card = 2 := Finset.card_pair hpq'
    rw [(hpairs p q).1, (hpairs p q).2]
    by_cases hs : ({(p : E), (q : E)} : Finset E) ∈ (T.marked 2).faces
    · rw [← P.image_eq _ hs hcard.ge]
      exact image_congr (fun x hx => hkeep p hs hcard (Finset.mem_insert_self _ _) x hx)
    · have hbaseEmpty : T.diskDualBase {(p : E), (q : E)} = ∅ := by
        change T.dualRegion {(p : E), (q : E)} ∩ (T.marked 2).space = ∅
        rw [hempty p q hs, empty_inter]
      rw [hbaseEmpty, empty_prod, image_empty, hempty p q hs]



theorem OriginalLowerProducts.exists_vertex_products (P : OriginalLowerProducts T) :
    Nonempty (OriginalVertexProducts T) := by
  classical
  exact P.exists_vertex_products_of_bands
    (fun p => Classical.choice (P.exists_vertex_band p))



theorem OriginalProperDiskTriangulation.exists_vertex_products
    (T : OriginalProperDiskTriangulation e R j) : Nonempty (OriginalVertexProducts T) := by
  classical
  exact (Classical.choice T.exists_lower_products).exists_vertex_products

end PoincareConjecture.M76
