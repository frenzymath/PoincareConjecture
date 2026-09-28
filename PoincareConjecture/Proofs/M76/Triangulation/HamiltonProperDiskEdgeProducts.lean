import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskEdgeEndpoints
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskSignedProduct










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}
  {C : HamiltonProperDiskCoherentSides T c}




theorem HamiltonProperDiskTriangleFibers.exists_edge_product
    (F : HamiltonProperDiskTriangleFibers C) (h3 : Module.finrank ℝ E = 3)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 2) :
    ∃ P : HamiltonProperDiskFaceProduct C s,
      (∀ t ∈ T.disk.faces, t.card = 3 → s ⊆ t →
        ∀ x ∈ T.diskDualBase t ×ˢ I, P.map x = F.map t x.2) ∧
      (s ∈ T.boundary.faces →
        (fun t : ℝ => P.map (s.centroid ℝ id, t)) '' I =
          T.dualRegion s ∩ frontier R) := by
  classical
  obtain ⟨endpoints⟩ := F.exists_edge_endpoints h3 hproper hs hcard
  obtain ⟨p0, hp0⟩ := T.disk.nonempty_of_mem_faces hs
  let p : T.disk.vertices := ⟨p0, T.disk.face_subset_vertices hs hp0⟩
  have hps : (p : E) ∈ s := hp0
  have hN := T.edge_region_ball h3 p hps hs hcard
  have hsource := T.dualRegion_subset_chart_source p hps
  have hzero : T.dualRegion s ∩ {x | C.labels.height p x = 0} = T.diskDualBase s := by
    ext x
    exact and_congr_right (fun hx => C.labels.height_eq_zero_iff p (hsource hx) hx.2)
  have hqzero : T.dualRegionRim s ∩ {x | C.labels.height p x = 0} =
      {endpoints.endpoint false, endpoints.endpoint true} := by
    rw [← endpoints.base_rim]
    ext x
    exact and_congr_right (fun hx =>
      C.labels.height_eq_zero_iff p (hsource (hN.1 hx)) (hN.1 hx).2)
  obtain ⟨G, hG, hG0, hGF, hGrim, hGpos, hGneg⟩ := exists_signed_interval_product
    endpoints.endpoint hN endpoints.base endpoints.distinct (C.labels.height p)
    ((C.labels.continuousOn_height p).mono hsource) hzero hqzero endpoints.fiber
    endpoints.piecewiseAffine endpoints.injective endpoints.central endpoints.image_subset
    endpoints.disjoint (fun i t ht => endpoints.positive i p hps t ht)
    (fun i t ht => endpoints.negative i p hps t ht)
  obtain ⟨g, hg, hval⟩ := hG
  have hi : InjOn g (T.diskDualBase s ×ˢ I) := by
    intro x hx y hy he
    have hxy : G ⟨x, hx⟩ = G ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (hval ⟨x, hx⟩).trans (he.trans (hval ⟨y, hy⟩).symm)
    exact congrArg Subtype.val (G.injective hxy)
  have him : g '' (T.diskDualBase s ×ˢ I) = T.dualRegion s := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hval ⟨x, hx⟩) ▸ (G ⟨x, hx⟩).property
    · intro y hy
      let x := G.symm ⟨y, hy⟩
      refine ⟨x, x.property, ?_⟩
      exact (hval x).symm.trans (congrArg Subtype.val (G.apply_symm_apply ⟨y, hy⟩))
  have haB (i : Bool) : endpoints.endpoint i ∈ T.diskDualBase s := by
    apply endpoints.base.1
    cases i <;> simp
  have hkeep (i : Bool) (t : ℝ) (ht : t ∈ I) :
      g (endpoints.endpoint i, t) = endpoints.fiber i t :=
    (hval ⟨(endpoints.endpoint i, t), haB i, ht⟩).symm.trans (hGF i ⟨t, ht⟩)
  have hboundary (hsF : s ∈ T.boundary.faces) :
      (fun t : ℝ => g (s.centroid ℝ id, t)) '' I = T.dualRegion s ∩ frontier R := by
    obtain ⟨i, hi0, hiF⟩ := endpoints.boundary hsF
    rw [← hiF]
    apply image_congr
    intro t ht
    simpa only [hi0] using hkeep i t ht
  have hproperG : ∀ x ∈ T.diskDualBase s ×ˢ I,
      g x ∈ frontier R ↔ x.1 ∈ frontier R := by
    intro x hx
    by_cases hsF : s ∈ T.boundary.faces
    · have hcontact := T.boundary_edge_base_contact hproper hs hcard hsF
      have hcs : s.centroid ℝ id ∈ T.diskDualBase s ∩ frontier R :=
        hcontact.symm.subset rfl
      constructor
      · intro hgf
        obtain ⟨t, ht, he⟩ := (hboundary hsF).symm.subset
          ⟨him.subset (mem_image_of_mem g hx), hgf⟩
        have hxeq := hi ⟨hcs.1, ht⟩ hx he
        have hfirst := congrArg (fun z : E × ℝ => z.1) hxeq
        exact hfirst ▸ hcs.2
      · intro hxf
        have hfirst : x.1 = s.centroid ℝ id := hcontact.subset ⟨hx.1, hxf⟩
        have hxval : g (s.centroid ℝ id, x.2) = g x :=
          congrArg g (Prod.ext hfirst.symm rfl)
        exact ((hboundary hsF).subset ⟨x.2, hx.2, hxval⟩).2
    · let : Fintype T.ambient.faces := T.finite.fintype
      have hint : T.dualRegion s ⊆ interior R :=
        inter_subset_left.trans (T.dualBlock_subset_interior hs hsF)
      exact iff_of_false (fun h => h.2 (hint (him.subset (mem_image_of_mem g hx))))
        (fun h => h.2 (hint hx.1.1))
  have hrimG : ∀ x ∈ T.diskDualBase s ×ˢ I,
      g x ∈ T.dualRegionRim s ↔ x.1 ∈ T.dualRegionRim s ∩ D ∨
        x.2 ∈ ({-1, 1} : Set ℝ) := by
    intro x hx
    rw [← hval ⟨x, hx⟩, hGrim, endpoints.base_rim]
  have hposG : ∀ q : T.disk.vertices, (q : E) ∈ s → ∀ x ∈ T.diskDualBase s ×ˢ I,
      0 ≤ C.labels.height q (g x) ↔ 0 ≤ x.2 := by
    intro q hqs x hx
    have hxm := him.subset (mem_image_of_mem g hx)
    have he : 0 ≤ C.labels.height q (g x) ↔ 0 ≤ C.labels.height p (g x) :=
      ⟨fun h => ((C.agreement s hs p q hps hqs).symm.subset ⟨hxm, h⟩).2,
        fun h => ((C.agreement s hs p q hps hqs).subset ⟨hxm, h⟩).2⟩
    rw [he, ← hval ⟨x, hx⟩]
    exact hGpos ⟨x, hx⟩
  have hnegG : ∀ q : T.disk.vertices, (q : E) ∈ s → ∀ x ∈ T.diskDualBase s ×ˢ I,
      C.labels.height q (g x) ≤ 0 ↔ x.2 ≤ 0 := by
    intro q hqs x hx
    have hxm := him.subset (mem_image_of_mem g hx)
    have he : C.labels.height q (g x) ≤ 0 ↔ C.labels.height p (g x) ≤ 0 :=
      ⟨fun h => ((C.negative_agreement hs p q hps hqs).symm.subset ⟨hxm, h⟩).2,
        fun h => ((C.negative_agreement hs p q hps hqs).subset ⟨hxm, h⟩).2⟩
    rw [he, ← hval ⟨x, hx⟩]
    exact hGneg ⟨x, hx⟩
  let P : HamiltonProperDiskFaceProduct C s :=
    { map := g
      piecewiseAffine := hg
      injective := hi
      image_eq := him
      central := fun x hx =>
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

end PoincareConjecture.M76.HamiltonIndexOne
