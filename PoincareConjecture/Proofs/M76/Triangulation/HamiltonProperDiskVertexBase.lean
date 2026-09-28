import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBaseModel
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexProducts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexIncidence
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskEdgeRims
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarMarkedCutCharts
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}



theorem HamiltonProperDiskTriangulation.diskVertexBlock_eq_inter
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) :
    T.diskVertexBlock p = (T.vertexBlock p).space ∩ D := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  symm
  simpa only [HamiltonProperDiskTriangulation.diskVertexBlock,
    HamiltonProperDiskTriangulation.vertexBlock, T.disk_space] using
    T.ambient.barycentricDualBlock_space_inter_subcomplex T.disk T.disk_le {(p : E)}



theorem HamiltonProperDiskTriangulation.vertex_base_rim_eq
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) :
    T.dualRegionRim {(p : E)} ∩ D =
      (T.diskVertexBlock p ∩ ((T.vertexBlock p).link p).space) ∪
        (T.diskVertexBlock p ∩ frontier R) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.vertexBlock p
  have hlink : (N.link p).space ⊆ N.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hrim : T.dualRegionRim {(p : E)} =
      ((N.link p).space ∩ R) ∪ (N.space ∩ frontier R) := by
    dsimp only [HamiltonProperDiskTriangulation.dualRegionRim]
    rw [Finset.centroid_singleton]
    rfl
  rw [hrim, T.diskVertexBlock_eq_inter]
  change (((N.link p).space ∩ R) ∪ (N.space ∩ frontier R)) ∩ D =
    ((N.space ∩ D) ∩ (N.link p).space) ∪ ((N.space ∩ D) ∩ frontier R)
  ext x
  constructor
  · rintro ⟨hx | hx, hxD⟩
    · exact Or.inl ⟨⟨hlink hx.1, hxD⟩, hx.1⟩
    · exact Or.inr ⟨⟨hx.1, hxD⟩, hx.2⟩
  · rintro (hx | hx)
    · exact ⟨Or.inl ⟨hx.2, T.disk_subset_region hx.1.2⟩, hx.1.2⟩
    · exact ⟨Or.inr ⟨hx.1.1, hx.2⟩, hx.1.2⟩

variable [FiniteDimensional ℝ E]

private theorem vertex_base_convex_chart
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) :
    ∃ (C : Set V) (L : (Fin 3 ⊕ Fin 3) → V →ₗ[ℝ] ℝ)
      (G : (T.vertexBlock p).space ≃ₜ C),
      IsCompact C ∧ Convex ℝ C ∧ (0 : V) ∈ interior C ∧
      C = {x | ∀ i, L i x ≤ 1} ∧ G.IsFinitePL ∧
      (∀ x : (T.vertexBlock p).space,
        (x : E) ∈ ((T.vertexBlock p).link p).space ↔ (G x : V) ∈ frontier C) ∧
      ((p : E) ∉ frontier R → ∀ x : (T.vertexBlock p).space,
        ((x : E) ∈ D ↔ (G x : V).2 = 0) ∧ (x : E) ∉ frontier R) ∧
      ((p : E) ∈ frontier R → ∀ x : (T.vertexBlock p).space,
        ((x : E) ∈ D ↔ (G x : V).2 = 0 ∧ 0 ≤ (G x : V).1.1) ∧
        ((x : E) ∈ frontier R ↔ (G x : V).1.1 = 0)) := by
  classical
  let N := T.vertexBlock p
  let H := (T.pairChart p).chart
  obtain ⟨hN, hpN, hstar, hsource, f, hf, hinj, hfp, hint, hvalue⟩ :=
    T.vertexBlock_centered_chart p
  let J := hf.embeddedImage hinj
  have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hN
  have hJs : J.space = f '' N.space := hf.embeddedImage_space hinj
  have hJstar : (J.closedStar 0).space = f '' N.space := by
    have h := hf.embeddedImage_closedStar_space hinj hpN
    simpa only [hfp, hstar] using h
  have hJlink : (J.link 0).space = f '' (N.link p).space := by
    have h := hf.embeddedImage_link_space hinj hpN
    simpa only [hfp] using h
  have hzJ : (0 : V) ∈ J.vertices := by
    rw [hf.embeddedImage_vertices hinj]
    exact ⟨p, hpN, hfp⟩
  let c : V ≃L[ℝ] (Fin 3 → ℝ) := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Module.finrank_prod])
  let A : Bool → V →ₗ[ℝ] ℝ := fun j => if j then LinearMap.snd ℝ P2 ℝ else
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ P2 ℝ)
  obtain ⟨C, L, e, hC, hcv, hz, _, hrep, he, helink, hecuts⟩ :=
    J.exists_finitePL_closedStar_chart_preserving_cut_family hJ hzJ
      (hJs.symm ▸ hint) c A
  let u : N.space ≃ₜ (J.closedStar 0).space :=
    (hf.homeomorphImage hN hinj).trans (Homeomorph.setCongr hJstar.symm)
  have hu : u.IsFinitePL := ⟨f, hf.finitePiecewiseAffineOn hN, fun _ => rfl⟩
  let G := u.trans e
  have hG : G.IsFinitePL := hu.trans he
  have hlinksub : (N.link p).space ⊆ N.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hlink (x : N.space) : (x : E) ∈ (N.link p).space ↔
      (G x : V) ∈ frontier C := by
    have hfx : f x ∈ (J.link 0).space ↔ (x : E) ∈ (N.link p).space := by
      rw [hJlink]
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hyx := hinj (hlinksub hy) x.property hxy
        simpa only [hyx] using hy
      · exact fun hx => mem_image_of_mem f hx
    exact hfx.symm.trans (helink (u x))
  have hnormal (x : N.space) : (G x : V).2 = 0 ↔ (f x).2 = 0 :=
    (hecuts true (u x)).1
  have hfirstzero (x : N.space) : (G x : V).1.1 = 0 ↔ (f x).1.1 = 0 :=
    (hecuts false (u x)).1
  have hfirstnonneg (x : N.space) : 0 ≤ (G x : V).1.1 ↔ 0 ≤ (f x).1.1 :=
    (hecuts false (u x)).2
  have hpH : (p : E) ∈ H.source := hsource (N.vertices_subset_space hpN)
  have hpD : (p : E) ∈ D := T.disk_space.subset (T.disk.vertices_subset_space p.property)
  have hpnormal : (H p).2 = 0 := by
    rcases (T.pairChart p).model with ⟨_, hdisk⟩ | ⟨_, hdisk⟩
    · exact (hdisk p hpH).mp hpD
    · exact ((hdisk p hpH).mp hpD).2
  have hfnormal (x : E) : (f x).2 = (H x).2 := by
    rw [hvalue x]
    change (H x).2 - (H p).2 = (H x).2
    rw [hpnormal, sub_zero]
  refine ⟨C, L, G, hC, hcv, hz, hrep, hG, hlink, ?_, ?_⟩
  · intro hpfront x
    have hxint := T.vertexBlock_subset_interior p hpfront x.property
    have hdisk : (x : E) ∈ D ↔ (H x).2 = 0 := by
      rcases (T.pairChart p).model with ⟨_, hdisk⟩ | ⟨hregion, hdisk⟩
      · exact hdisk x (hsource x.property)
      · have hpos := (hregion x (hsource x.property)).mp (interior_subset hxint)
        exact (hdisk x (hsource x.property)).trans (and_iff_right hpos)
    refine ⟨hdisk.trans ?_, fun hx => hx.2 hxint⟩
    rw [← hfnormal x]
    exact (hnormal x).symm
  · intro hpfront
    have hhalf : ∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1 := by
      rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨hhalf, _⟩
      · exact False.elim (hpfront.2 (hinside hpH))
      · exact hhalf
    have hdisk : ∀ x ∈ H.source, x ∈ D ↔ 0 ≤ (H x).1.1 ∧ (H x).2 = 0 := by
      rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨_, hdisk⟩
      · exact False.elim (hpfront.2 (hinside hpH))
      · exact hdisk
    let ell : V →L[ℝ] ℝ :=
      { toFun := fun z => z.1.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        cont := by fun_prop }
    have hell : ell.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
      intro heq
      have h := congrArg (fun m : V →ₗ[ℝ] ℝ => m ((1, 0), 0)) heq
      exact one_ne_zero h
    have hfront := H.isImage_frontier_of_affine_nonneg ell.toContinuousAffineMap hell hhalf
    have hpfirst : (H p).1.1 = 0 := (hfront.apply_mem_iff hpH).mpr hpfront
    have hffirst (x : E) : (f x).1.1 = (H x).1.1 := by
      rw [hvalue x]
      change (H x).1.1 - (H p).1.1 = (H x).1.1
      rw [hpfirst, sub_zero]
    intro x
    constructor
    · rw [hdisk x (hsource x.property), hnormal x, hfirstnonneg x,
        hfnormal x, hffirst x, and_comm]
    · have hxfront : (x : E) ∈ frontier R ↔ (H x).1.1 = 0 :=
        (hfront.apply_mem_iff (hsource x.property)).symm
      rw [hxfront, hfirstzero x, hffirst x]

private theorem vertex_base_certificates
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) :
    IsFinitePLBallPair P2 (T.diskVertexBlock p) (T.dualRegionRim {(p : E)} ∩ D) ∧
    ((p : E) ∈ frontier R → ∃ a z : E, a ≠ z ∧
      IsFinitePLBallPair ℝ (T.diskVertexBlock p ∩ frontier R) {a, z} ∧
      IsFinitePLBallPair ℝ
        (T.diskVertexBlock p ∩ ((T.vertexBlock p).link p).space) {a, z} ∧
      (T.diskVertexBlock p ∩ frontier R) ∩
        (T.diskVertexBlock p ∩ ((T.vertexBlock p).link p).space) = {a, z}) := by
  classical
  let N := T.vertexBlock p
  let B := T.diskVertexBlock p
  have hBN : B ⊆ N.space := (T.diskVertexBlock_eq_inter p).subset.trans inter_subset_left
  have hBD (x : N.space) : (x : E) ∈ B ↔ (x : E) ∈ D := by
    change (x : E) ∈ T.diskVertexBlock p ↔ (x : E) ∈ D
    rw [T.diskVertexBlock_eq_inter]
    exact and_iff_right x.property
  obtain ⟨C, L, G, hC, hcv, hz, hrep, hG, hlink, hinter, hboundary⟩ :=
    vertex_base_convex_chart T p
  obtain ⟨hfull, hplus, q0, q1, hq, haxis, hcap, hmeet⟩ :=
    exists_convex_vertex_base_models hC hcv hz L hrep
  obtain ⟨g, hg, hgval⟩ := hG.symm
  have hginj : InjOn g C := by
    intro x hx y hy hxy
    have he : G.symm ⟨x, hx⟩ = G.symm ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hgval] using hxy
    exact congrArg Subtype.val (G.symm.injective he)
  have himage (U : Set V) (S : Set E) (hUC : U ⊆ C) (hSN : S ⊆ N.space)
      (hiff : ∀ x : N.space, (G x : V) ∈ U ↔ (x : E) ∈ S) : g '' U = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : (G.symm ⟨y, hUC hy⟩ : E) ∈ S := (hiff _).mp (by
        simpa only [G.apply_symm_apply] using hy)
      rwa [hgval] at h
    · intro hx
      refine ⟨G ⟨x, hSN hx⟩, (hiff _).mpr hx, ?_⟩
      rw [← hgval, G.symm_apply_apply]
  have houterC : frontier C ∩ {x : V | x.2 = 0 ∧ 0 ≤ x.1.1} ⊆ C :=
    fun _ hx => hC.isClosed.frontier_subset hx.1
  by_cases hpfront : (p : E) ∈ frontier R
  · have hbase : g '' (C ∩ {x : V | x.2 = 0 ∧ 0 ≤ x.1.1}) = B := by
      apply himage _ _ inter_subset_left hBN
      intro x
      exact ⟨fun hx => (hBD x).mpr (((hboundary hpfront x).1).mpr hx.2),
        fun hx => ⟨(G x).property, ((hboundary hpfront x).1).mp ((hBD x).mp hx)⟩⟩
    have houter : g '' (frontier C ∩ {x : V | x.2 = 0 ∧ 0 ≤ x.1.1}) =
        B ∩ (N.link p).space := by
      apply himage _ _ houterC (inter_subset_left.trans hBN)
      intro x
      constructor
      · intro hx
        exact ⟨(hBD x).mpr (((hboundary hpfront x).1).mpr hx.2), (hlink x).mpr hx.1⟩
      · intro hx
        exact ⟨(hlink x).mp hx.2, ((hboundary hpfront x).1).mp ((hBD x).mp hx.1)⟩
    have hfront : g '' (C ∩ {x : V | x.2 = 0 ∧ x.1.1 = 0}) =
        B ∩ frontier R := by
      apply himage _ _ inter_subset_left (inter_subset_left.trans hBN)
      intro x
      constructor
      · intro hx
        exact ⟨(hBD x).mpr (((hboundary hpfront x).1).mpr ⟨hx.2.1, hx.2.2.ge⟩),
          ((hboundary hpfront x).2).mpr hx.2.2⟩
      · intro hx
        exact ⟨(G x).property, (((hboundary hpfront x).1).mp ((hBD x).mp hx.1)).1,
          ((hboundary hpfront x).2).mp hx.2⟩
    have hball := hplus.image_of_subset hg inter_subset_left hginj
    rw [hbase, image_union, houter, hfront] at hball
    refine ⟨?_, fun _ => ?_⟩
    · rwa [T.vertex_base_rim_eq]
    · have hq0 : q0 ∈ C := (haxis.1 (by simp)).1
      have hq1 : q1 ∈ C := (haxis.1 (by simp)).1
      refine ⟨g q0, g q1, fun heq => hq (hginj hq0 hq1 heq), ?_, ?_, ?_⟩
      · have h := haxis.image_of_subset hg inter_subset_left hginj
        simpa only [hfront, image_pair] using h
      · have h := hcap.image_of_subset hg houterC hginj
        simpa only [houter, image_pair] using h
      · rw [← hfront, ← houter, ← hginj.image_inter inter_subset_left houterC,
          hmeet, image_pair]
  · have hbase : g '' (C ∩ {x : V | x.2 = 0}) = B := by
      apply himage _ _ inter_subset_left hBN
      intro x
      exact ⟨fun hx => (hBD x).mpr (((hinter hpfront x).1).mpr hx.2),
        fun hx => ⟨(G x).property, ((hinter hpfront x).1).mp ((hBD x).mp hx)⟩⟩
    have houter : g '' (frontier C ∩ {x : V | x.2 = 0}) =
        B ∩ (N.link p).space := by
      apply himage _ _ (fun _ hx => hC.isClosed.frontier_subset hx.1)
        (inter_subset_left.trans hBN)
      intro x
      constructor
      · intro hx
        exact ⟨(hBD x).mpr (((hinter hpfront x).1).mpr hx.2), (hlink x).mpr hx.1⟩
      · intro hx
        exact ⟨(hlink x).mp hx.2, ((hinter hpfront x).1).mp ((hBD x).mp hx.1)⟩
    have hfront : B ∩ frontier R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (hinter hpfront ⟨x, hBN hx.1⟩).2 hx.2
    have hball := hfull.image_of_subset hg inter_subset_left hginj
    rw [hbase, houter] at hball
    refine ⟨?_, fun hp => (hpfront hp).elim⟩
    rwa [T.vertex_base_rim_eq, hfront, union_empty]



theorem HamiltonProperDiskTriangulation.vertex_base_ballPair
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) :
    IsFinitePLBallPair P2 (T.diskVertexBlock p) (T.dualRegionRim {(p : E)} ∩ D) :=
  (vertex_base_certificates T p).1




theorem HamiltonProperDiskTriangulation.exists_boundary_vertex_base_intervals
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    (hpfront : (p : E) ∈ frontier R) :
    ∃ a z : E, a ≠ z ∧
      IsFinitePLBallPair ℝ (T.diskVertexBlock p ∩ frontier R) {a, z} ∧
      IsFinitePLBallPair ℝ
        (T.diskVertexBlock p ∩ ((T.vertexBlock p).link p).space) {a, z} ∧
      (T.diskVertexBlock p ∩ frontier R) ∩
        (T.diskVertexBlock p ∩ ((T.vertexBlock p).link p).space) = {a, z} :=
  (vertex_base_certificates T p).2 hpfront

end PoincareConjecture.M76.HamiltonIndexOne
