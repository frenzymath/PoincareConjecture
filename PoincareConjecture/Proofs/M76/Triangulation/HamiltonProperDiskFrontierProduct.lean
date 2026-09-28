import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskFrontierZero
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskSignedProduct
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBoundaryEdges









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}
  {C : HamiltonProperDiskCoherentSides T c}




structure HamiltonProperDiskFrontierProduct
    (P : HamiltonProperDiskLowerProducts T C) (p : T.disk.vertices) where

  map : E × ℝ → E

  piecewiseAffine : FinitePiecewiseAffineOn map
    ((T.diskVertexBlock p ∩ frontier R) ×ˢ I)

  injective : InjOn map ((T.diskVertexBlock p ∩ frontier R) ×ˢ I)

  image_eq : map '' ((T.diskVertexBlock p ∩ frontier R) ×ˢ I) =
    (T.vertexBlock p).space ∩ frontier R

  central : ∀ x ∈ T.diskVertexBlock p ∩ frontier R, map (x, 0) = x

  rim : ∀ x ∈ (T.diskVertexBlock p ∩ frontier R) ×ˢ I,
    map x ∈ ((T.vertexBlock p).link p).space ↔
      x.1 ∈ ((T.vertexBlock p).link p).space ∨ x.2 ∈ ({-1, 1} : Set ℝ)

  positive : ∀ x ∈ (T.diskVertexBlock p ∩ frontier R) ×ˢ I,
    0 ≤ C.labels.height p (map x) ↔ 0 ≤ x.2

  negative : ∀ x ∈ (T.diskVertexBlock p ∩ frontier R) ×ˢ I,
    C.labels.height p (map x) ≤ 0 ↔ x.2 ≤ 0

  keep_edge : ∀ s ∈ T.disk.faces, s ∈ T.boundary.faces →
    (p : E) ∈ s → s.card = 2 → ∀ t ∈ I,
      map (s.centroid ℝ id, t) = P.map s (s.centroid ℝ id, t)





theorem HamiltonProperDiskLowerProducts.exists_frontier_vertex_product
    (P : HamiltonProperDiskLowerProducts T C)
    (hproper : ∀ x : closedBall (0 : V2) 1,
      (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    (p : T.disk.vertices) (hpfront : (p : E) ∈ frontier R) :
    Nonempty (HamiltonProperDiskFrontierProduct P p) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let A := T.diskVertexBlock p ∩ frontier R
  let F := (T.vertexBlock p).space ∩ frontier R
  let Q := F ∩ ((T.vertexBlock p).link p).space
  obtain ⟨a, ha, hA, hf, hzero, hqzero⟩ := T.frontier_vertex_zero_data C p hpfront
  have haA (i : Bool) : a i ∈ A := by
    apply hA.1
    cases i <;> simp
  have haQ (i : Bool) : a i ∈ Q := by
    apply (hqzero.symm.subset ?_).1
    cases i <;> simp
  have hsel (i : Bool) : ∃ s : Finset E, s ∈ T.disk.faces ∧ s ∈ T.boundary.faces ∧
      (p : E) ∈ s ∧ s.card = 2 ∧ s.centroid ℝ id = a i :=
    (T.mem_boundary_vertex_base_endpoints_iff hproper p (a i)).mp
      ⟨haA i, (haQ i).2⟩
  choose s hsD hsF hps hsc hsa using hsel
  have hscle (i : Bool) : 2 ≤ (s i).card := by rw [hsc i]
  have haBase (i : Bool) : a i ∈ T.diskDualBase (s i) := by
    rw [← hsa i]
    have hxD : (s i).centroid ℝ id ∈ D := T.disk_space.subset
      (T.disk.convexHull_subset_space (hsD i)
        ((s i).centroid_mem_convexHull (T.disk.nonempty_of_mem_faces (hsD i))))
    exact ⟨⟨(T.ambient.barycentricDualBlock (s i)).vertices_subset_space
      (T.ambient.faceCentroid_mem_barycentricDualBlock_vertices (T.disk_le (hsD i))),
      T.disk_subset_region hxD⟩, hxD⟩
  let fiber : Bool → ℝ → E := fun i t => P.map (s i) (a i, t)
  have hI := isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
  have hcopy := hI
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ := hcopy
  have hfiber (i : Bool) : FinitePiecewiseAffineOn (fiber i) I := by
    let j : ℝ →ᴬ[ℝ] E × ℝ :=
      (ContinuousAffineMap.const ℝ ℝ (a i)).prod (ContinuousAffineMap.id ℝ ℝ)
    have hj : FinitePiecewiseAffineOn j I := ⟨K, hK, hKI, K.affineOnFaces_affine j⟩
    exact (P.piecewiseAffine (s i) (hsD i) (hscle i)).comp hj
      (fun _ ht => ⟨haBase i, ht⟩)
  have hfi (i : Bool) : InjOn (fiber i) I := by
    intro x hx y hy he
    exact congrArg Prod.snd
      (P.injective (s i) (hsD i) (hscle i) ⟨haBase i, hx⟩ ⟨haBase i, hy⟩ he)
  have hfa (i : Bool) : fiber i 0 = a i :=
    P.central (s i) (hsD i) (hscle i) (a i) (haBase i)
  have hfimage (i : Bool) : fiber i '' I = T.dualRegion (s i) ∩ frontier R := by
    change (fun t => P.map (s i) (a i, t)) '' I = _
    rw [← hsa i]
    exact P.boundary_image (s i) (hsD i) (hsc i) (hsF i)
  have hfQ (i : Bool) : fiber i '' I ⊆ Q := by
    intro x hx
    have hxR := (hfimage i).subset hx
    have hxlink := T.edge_dual_subset_vertex_link p (hsD i) (hsc i) (hps i) hxR.1.1
    have hxN : x ∈ (T.vertexBlock p).space :=
      SimplicialComplex.space_subset_of_le
        (show (T.vertexBlock p).link p ≤ T.vertexBlock p from fun _ ht => ht.1) hxlink
    exact ⟨⟨hxN, hxR.2⟩, hxlink⟩
  have hdis : Disjoint (fiber false '' I) (fiber true '' I) := by
    apply disjoint_left.mpr
    rintro y ⟨t, ht, hty⟩ ⟨u, hu, huy⟩
    have hy0 : y ∈ T.dualRegion (s false) :=
      (P.image_eq _ (hsD false) (hscle false)).subset
        ⟨(a false, t), ⟨haBase false, ht⟩, hty⟩
    have hy1 : y ∈ T.dualRegion (s true) :=
      (P.image_eq _ (hsD true) (hscle true)).subset
        ⟨(a true, u), ⟨haBase true, hu⟩, huy⟩
    obtain ⟨x, hx, hxy⟩ :=
      (P.overlap_image _ (hsD false) (hscle false) _ (hsD true) (hscle true)).symm.subset
        ⟨hy0, hy1⟩
    have hx0 : x = (a false, t) :=
      P.injective _ (hsD false) (hscle false) ⟨hx.1.1, hx.2⟩ ⟨haBase false, ht⟩
        (hxy.trans hty.symm)
    have hx1 : x = (a true, u) :=
      P.injective _ (hsD true) (hscle true) ⟨hx.1.2, hx.2⟩ ⟨haBase true, hu⟩
        ((P.agrees _ (hsD false) (hscle false) _ (hsD true) (hscle true) x hx).symm.trans
          (hxy.trans huy.symm))
    exact ha (congrArg Prod.fst (hx0.symm.trans hx1))
  have hfpos (i : Bool) (t : ℝ) (ht : t ∈ I) :
      0 ≤ C.labels.height p (fiber i t) ↔ 0 ≤ t :=
    P.positive _ (hsD i) (hscle i) p (hps i) (a i, t) ⟨haBase i, ht⟩
  have hfneg (i : Bool) (t : ℝ) (ht : t ∈ I) :
      C.labels.height p (fiber i t) ≤ 0 ↔ t ≤ 0 :=
    P.negative _ (hsD i) (hscle i) p (hps i) (a i, t) ⟨haBase i, ht⟩
  obtain ⟨H, hH, hH0, hHF, hHQ, hHP, hHM⟩ := exists_signed_interval_product a
    (T.frontier_vertex_ballPair p hpfront) hA ha (C.labels.height p) hf hzero hqzero
    fiber hfiber hfi hfa hfQ hdis hfpos hfneg
  obtain ⟨g, hg, hgH⟩ := hH
  have hAend (x : E) (hx : x ∈ A) :
      x ∈ ((T.vertexBlock p).link p).space ↔ x ∈ ({a false, a true} : Set E) := by
    have hz := hzero.symm.subset hx
    constructor
    · exact fun hl => hqzero.subset ⟨⟨hz.1, hl⟩, hz.2⟩
    · exact fun he => (hqzero.symm.subset he).1.2
  refine ⟨{
    map := g
    piecewiseAffine := hg
    injective := ?_
    image_eq := ?_
    central := ?_
    rim := ?_
    positive := ?_
    negative := ?_
    keep_edge := ?_ }⟩
  · intro x hx y hy he
    have heH : H ⟨x, hx⟩ = H ⟨y, hy⟩ :=
      Subtype.ext ((hgH ⟨x, hx⟩).trans (he.trans (hgH ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective heH)
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hgH ⟨x, hx⟩]
      exact (H ⟨x, hx⟩).property
    · intro hy
      refine ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hgH, H.apply_symm_apply]
  · intro x hx
    exact (hgH ⟨(x, 0), hx, by norm_num⟩).symm.trans (hH0 ⟨x, hx⟩)
  · intro x hx
    rw [← hgH ⟨x, hx⟩]
    have hmem : (H ⟨x, hx⟩ : E) ∈ ((T.vertexBlock p).link p).space ↔
        (H ⟨x, hx⟩ : E) ∈ Q :=
      (and_iff_right (H ⟨x, hx⟩).property).symm
    exact hmem.trans ((hHQ ⟨x, hx⟩).trans (or_congr (hAend x.1 hx.1).symm Iff.rfl))
  · intro x hx
    rw [← hgH ⟨x, hx⟩]
    exact hHP ⟨x, hx⟩
  · intro x hx
    rw [← hgH ⟨x, hx⟩]
    exact hHM ⟨x, hx⟩
  · intro t htD htF hpt htc v hv
    have hend := (T.mem_boundary_vertex_base_endpoints_iff hproper p
      (t.centroid ℝ id)).mpr ⟨t, htD, htF, hpt, htc, rfl⟩
    have he := (hAend _ hend.1).mp hend.2
    have hkeep (i : Bool) (hi : t.centroid ℝ id = a i) :
        g (t.centroid ℝ id, v) = P.map t (t.centroid ℝ id, v) := by
      have hts : t = s i := by
        have h : (⟨t, T.disk_le htD⟩ : T.ambient.faces) =
            ⟨s i, T.disk_le (hsD i)⟩ := T.ambient.faceCentroid_injective
          (show (t.centroid ℝ id) = (s i).centroid ℝ id from hi.trans (hsa i).symm)
        exact congrArg Subtype.val h
      rw [hi, ← hgH ⟨(a i, v), haA i, hv⟩]
      exact (hHF i ⟨v, hv⟩).trans (by change P.map (s i) _ = P.map t _; rw [hts])
    rcases he with he | he
    · exact hkeep false he
    · exact hkeep true he

end PoincareConjecture.M76.HamiltonIndexOne
