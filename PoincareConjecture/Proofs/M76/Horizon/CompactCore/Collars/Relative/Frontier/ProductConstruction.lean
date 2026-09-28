import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Frontier.Product
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Frontier.Zero
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Frontier.Endpoints
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskSignedProduct



set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] {T : CoorientedSurfaceStars E}




theorem SurfaceLowerProducts.exists_frontier_vertex_product (P : SurfaceLowerProducts T)
    (p : (T.marked 2).vertices)
    (hpfront : (p : E) ∈ (T.marked 1).space) :
    Nonempty (SurfaceFrontierProduct P p) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let A := T.surfaceBase {(p : E)} ∩ (T.marked 1).space
  let F := (T.vertexBlock p).space ∩ (T.marked 1).space
  let Q := F ∩ ((T.vertexBlock p).link p).space
  obtain ⟨a, ha, hA, hf, hzero, hqzero⟩ := T.frontier_vertex_zero_data p hpfront
  have haA (i : Bool) : a i ∈ A := by
    apply hA.1
    cases i <;> simp
  have haQ (i : Bool) : a i ∈ Q := by
    apply (hqzero.symm.subset ?_).1
    cases i <;> simp
  have hsel (i : Bool) : ∃ s : Finset (E),
      s ∈ (T.marked 2).faces ∧ s ∈ (T.marked 1).faces ∧
      (p : E) ∈ s ∧ s.card = 2 ∧ s.centroid ℝ id = a i :=
    (T.mem_boundary_vertex_base_endpoints_iff p hpfront (a i)).mp
      ⟨haA i, (haQ i).2⟩
  choose s hsD hsF hps hsc hsa using hsel
  have hscle (i : Bool) : 2 ≤ (s i).card := by rw [hsc i]
  have haBase (i : Bool) : a i ∈ T.surfaceBase (s i) := by
    rw [← hsa i]
    have hxD : (s i).centroid ℝ id ∈ (T.marked 2).space :=
      (T.marked 2).convexHull_subset_space (hsD i)
        ((s i).centroid_mem_convexHull ((T.marked 2).nonempty_of_mem_faces (hsD i)))
    exact ⟨⟨(T.ambient.barycentricDualBlock (s i)).vertices_subset_space
      (T.ambient.faceCentroid_mem_barycentricDualBlock_vertices (T.marked_le 2 (hsD i))),
      T.surface_subset_region hxD⟩, hxD⟩
  let fiber : Bool → ℝ → (E) := fun i t => P.map (s i) (a i, t)
  have hI := isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
  have hcopy := hI
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ := hcopy
  have hfiber (i : Bool) : FinitePiecewiseAffineOn (fiber i) I := by
    let f : ℝ →ᴬ[ℝ] (E) × ℝ :=
      (ContinuousAffineMap.const ℝ ℝ (a i)).prod (ContinuousAffineMap.id ℝ ℝ)
    have hfpl : FinitePiecewiseAffineOn f I := ⟨K, hK, hKI, K.affineOnFaces_affine f⟩
    exact (P.piecewiseAffine (s i) (hsD i) (hscle i)).comp hfpl
      (fun _ ht => ⟨haBase i, ht⟩)
  have hfi (i : Bool) : InjOn (fiber i) I := by
    intro x hx y hy he
    exact congrArg Prod.snd
      (P.injective (s i) (hsD i) (hscle i) ⟨haBase i, hx⟩ ⟨haBase i, hy⟩ he)
  have hfa (i : Bool) : fiber i 0 = a i :=
    P.central (s i) (hsD i) (hscle i) (a i) (haBase i)
  have hfimage (i : Bool) : fiber i '' I = T.dualRegion (s i) ∩ (T.marked 1).space := by
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
      0 ≤ T.height p (fiber i t) ↔ 0 ≤ t :=
    P.positive _ (hsD i) (hscle i) p (hps i) (a i, t) ⟨haBase i, ht⟩
  have hfneg (i : Bool) (t : ℝ) (ht : t ∈ I) :
      T.height p (fiber i t) ≤ 0 ↔ t ≤ 0 :=
    P.negative _ (hsD i) (hscle i) p (hps i) (a i, t) ⟨haBase i, ht⟩
  obtain ⟨H, hH, hH0, hHF, hHQ, hHP, hHM⟩ :=
    PoincareConjecture.M76.HamiltonIndexOne.exists_signed_interval_product a
      (T.frontier_vertex_ballPair p hpfront) hA ha (T.height p) hf hzero hqzero
      fiber hfiber hfi hfa hfQ hdis hfpos hfneg
  obtain ⟨g, hg, hgH⟩ := hH
  have hAend (x : E) (hx : x ∈ A) :
      x ∈ ((T.vertexBlock p).link p).space ↔ x ∈ ({a false, a true} : Set (E)) := by
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
    have hend := (T.mem_boundary_vertex_base_endpoints_iff p hpfront
      (t.centroid ℝ id)).mpr ⟨t, htD, htF, hpt, htc, rfl⟩
    have he := (hAend _ hend.1).mp hend.2
    have hkeep (i : Bool) (hi : t.centroid ℝ id = a i) :
        g (t.centroid ℝ id, v) = P.map t (t.centroid ℝ id, v) := by
      have hts : t = s i := by
        have h : (⟨t, T.marked_le 2 htD⟩ : T.ambient.faces) =
            ⟨s i, T.marked_le 2 (hsD i)⟩ := T.ambient.faceCentroid_injective
          (show (t.centroid ℝ id) = (s i).centroid ℝ id from hi.trans (hsa i).symm)
        exact congrArg Subtype.val h
      rw [hi, ← hgH ⟨(a i, v), haA i, hv⟩]
      exact (hHF i ⟨v, hv⟩).trans (by change P.map (s i) _ = P.map t _; rw [hts])
    rcases he with he | he
    · exact hkeep false he
    · exact hkeep true he

end Geometry.SimplicialComplex

