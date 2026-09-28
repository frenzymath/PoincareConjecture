import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Products.EdgeEndpoints
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Products.FaceProduct
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Regions.EdgeGeometry
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskSignedProduct



set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] {T : CoorientedSurfaceStars E}



theorem SurfaceTriangleFibers.exists_edge_product (F : SurfaceTriangleFibers T)
    {s : Finset E} (hs : s ∈ (T.marked 2).faces)
    (hcard : s.card = 2) :
    ∃ P : SurfaceFaceProduct T s,
      (∀ t ∈ (T.marked 2).faces, t.card = 3 → s ⊆ t →
        ∀ x ∈ (T.dualRegion t ∩ (T.marked 2).space) ×ˢ I, P.map x = F.map t x.2) ∧
      (s ∈ (T.marked 1).faces →
        (fun r : ℝ ↦ P.map (s.centroid ℝ id, r)) '' I =
          T.dualRegion s ∩ (T.marked 1).space) := by
  classical
  obtain ⟨endpoints⟩ := F.exists_edge_endpoints hs hcard
  obtain ⟨p0, hp0⟩ := (T.marked 2).nonempty_of_mem_faces hs
  let p : (T.marked 2).vertices := ⟨p0, (T.marked 2).face_subset_vertices hs hp0⟩
  have hps : (p : E) ∈ s := hp0
  let B := T.dualRegion s ∩ (T.marked 2).space
  have hN := T.edge_region_ball p hps hs hcard
  have hzero : T.dualRegion s ∩ {x | T.height p x = 0} = B := by
    ext x
    exact and_congr_right (fun hx ↦ T.height_eq_zero_iff_on_dualRegion p hps hx)
  have hqzero : T.dualRegionRim s ∩ {x | T.height p x = 0} =
      {endpoints.endpoint false, endpoints.endpoint true} := by
    rw [← endpoints.base_rim]
    ext x
    exact and_congr_right (fun hx ↦ T.height_eq_zero_iff_on_dualRegion p hps (hN.1 hx))
  obtain ⟨G, hG, hG0, hGF, hGrim, hGpos, hGneg⟩ :=
    PoincareConjecture.M76.HamiltonIndexOne.exists_signed_interval_product
      endpoints.endpoint hN endpoints.base
      endpoints.distinct (T.height p) (T.continuousOn_height_dualRegion p hps)
      hzero hqzero endpoints.fiber endpoints.piecewiseAffine endpoints.injective
      endpoints.central endpoints.image_subset endpoints.disjoint
      (fun i r hr ↦ endpoints.positive i p hps r hr)
      (fun i r hr ↦ endpoints.negative i p hps r hr)
  obtain ⟨g, hg, hval⟩ := hG
  have hi : InjOn g (B ×ˢ I) := by
    intro x hx y hy he
    have hxy : G ⟨x, hx⟩ = G ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (hval ⟨x, hx⟩).trans (he.trans (hval ⟨y, hy⟩).symm)
    exact congrArg Subtype.val (G.injective hxy)
  have him : g '' (B ×ˢ I) = T.dualRegion s := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hval ⟨x, hx⟩) ▸ (G ⟨x, hx⟩).property
    · intro y hy
      let x := G.symm ⟨y, hy⟩
      refine ⟨x, x.property, ?_⟩
      exact (hval x).symm.trans (congrArg Subtype.val (G.apply_symm_apply ⟨y, hy⟩))
  have haB (i : Bool) : endpoints.endpoint i ∈ B := by
    apply endpoints.base.1
    cases i <;> simp
  have hkeep (i : Bool) (r : ℝ) (hr : r ∈ I) :
      g (endpoints.endpoint i, r) = endpoints.fiber i r :=
    (hval ⟨(endpoints.endpoint i, r), haB i, hr⟩).symm.trans (hGF i ⟨r, hr⟩)
  have hboundary (hsB : s ∈ (T.marked 1).faces) :
      (fun r : ℝ ↦ g (s.centroid ℝ id, r)) '' I =
        T.dualRegion s ∩ (T.marked 1).space := by
    obtain ⟨i, hi0, hiF⟩ := endpoints.boundary hsB
    rw [← hiF]
    apply image_congr
    intro r hr
    simpa only [hi0] using hkeep i r hr
  have hproperG : ∀ x ∈ B ×ˢ I, g x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space := by
    intro x hx
    by_cases hsB : s ∈ (T.marked 1).faces
    · have hcontact := T.boundary_edge_base_contact hs hcard hsB
      have hcs : s.centroid ℝ id ∈ B ∩ (T.marked 1).space := hcontact.symm.subset rfl
      constructor
      · intro hgf
        obtain ⟨r, hr, he⟩ := (hboundary hsB).symm.subset
          ⟨him.subset (mem_image_of_mem g hx), hgf⟩
        have hxeq := hi ⟨hcs.1, hr⟩ hx he
        have hfirst := congrArg (fun z : E × ℝ ↦ z.1) hxeq
        exact hfirst ▸ hcs.2
      · intro hxf
        have hfirst : x.1 = s.centroid ℝ id := hcontact.subset ⟨hx.1, hxf⟩
        have hxval : g (s.centroid ℝ id, x.2) = g x :=
          congrArg g (Prod.ext hfirst.symm rfl)
        exact ((hboundary hsB).subset ⟨x.2, hx.2, hxval⟩).2
    · let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
      have hempty : T.dualRegion s ∩ (T.marked 1).space = ∅ := by
        rw [T.dualRegion_inter_boundary]
        exact (T.marked 1).barycentricDualBlock_space_eq_empty_of_not_face
          ((T.marked 2).nonempty_of_mem_faces hs) hsB
      exact iff_of_false
        (fun h ↦ hempty.subset ⟨him.subset (mem_image_of_mem g hx), h⟩)
        (fun h ↦ hempty.subset ⟨hx.1.1, h⟩)
  have hrimG : ∀ x ∈ B ×ˢ I,
      g x ∈ T.dualRegionRim s ↔ x.1 ∈ T.dualRegionRim s ∩ (T.marked 2).space ∨
        x.2 ∈ ({-1, 1} : Set ℝ) := by
    intro x hx
    rw [← hval ⟨x, hx⟩, hGrim, endpoints.base_rim]
  have hposG : ∀ q : (T.marked 2).vertices, (q : E) ∈ s →
      ∀ x ∈ B ×ˢ I, 0 ≤ T.height q (g x) ↔ 0 ≤ x.2 := by
    intro q hqs x hx
    have hxm := him.subset (mem_image_of_mem g hx)
    have heq := (T.dualRegion_halves_eq p q hps hqs).1
    have he : 0 ≤ T.height q (g x) ↔ 0 ≤ T.height p (g x) :=
      ⟨fun h ↦ (heq.symm.subset ⟨hxm, h⟩).2, fun h ↦ (heq.subset ⟨hxm, h⟩).2⟩
    rw [he, ← hval ⟨x, hx⟩]
    exact hGpos ⟨x, hx⟩
  have hnegG : ∀ q : (T.marked 2).vertices, (q : E) ∈ s →
      ∀ x ∈ B ×ˢ I, T.height q (g x) ≤ 0 ↔ x.2 ≤ 0 := by
    intro q hqs x hx
    have hxm := him.subset (mem_image_of_mem g hx)
    have heq := (T.dualRegion_halves_eq p q hps hqs).2
    have he : T.height q (g x) ≤ 0 ↔ T.height p (g x) ≤ 0 :=
      ⟨fun h ↦ (heq.symm.subset ⟨hxm, h⟩).2, fun h ↦ (heq.subset ⟨hxm, h⟩).2⟩
    rw [he, ← hval ⟨x, hx⟩]
    exact hGneg ⟨x, hx⟩
  let P : SurfaceFaceProduct T s :=
    { map := g
      piecewiseAffine := hg
      injective := hi
      image_eq := him
      central := fun x hx ↦
        (hval ⟨(x, 0), hx, by norm_num⟩).symm.trans (hG0 ⟨x, hx⟩)
      proper := hproperG
      rim := hrimG
      positive := hposG
      negative := hnegG }
  refine ⟨P, ?_, hboundary⟩
  intro t ht htc hst x hx
  obtain ⟨i, hi0, hieq⟩ := endpoints.coface t ht htc hst
  have hfirst : x.1 = endpoints.endpoint i :=
    ((T.triangle_base_eq_singleton ht htc).subset hx.1).trans hi0.symm
  calc
    P.map x = g (endpoints.endpoint i, x.2) := congrArg g (Prod.ext hfirst rfl)
    _ = endpoints.fiber i x.2 := hkeep i x.2 hx.2
    _ = F.map t x.2 := hieq hx.2

end Geometry.SimplicialComplex
