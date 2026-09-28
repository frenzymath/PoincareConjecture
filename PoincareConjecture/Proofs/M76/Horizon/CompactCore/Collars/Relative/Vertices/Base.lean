import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Vertices.Blocks
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Vertices.BaseCharts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBaseModel

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)

open Classical in

theorem vertex_base_certificates (p : (T.marked 2).vertices) :
    IsFinitePLBallPair P2 (T.surfaceBase {(p : E)})
      (T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) ∧
    ((p : E) ∈ (T.marked 1).space →
      ∃ a z : E, a ≠ z ∧
        IsFinitePLBallPair ℝ
          (T.surfaceBase {(p : E)} ∩ (T.marked 1).space) {a, z} ∧
        IsFinitePLBallPair ℝ
          (T.surfaceBase {(p : E)} ∩ ((T.vertexBlock p).link p).space)
          {a, z} ∧
        (T.surfaceBase {(p : E)} ∩ (T.marked 1).space) ∩
          (T.surfaceBase {(p : E)} ∩ ((T.vertexBlock p).link p).space) =
            {a, z}) := by
  classical
  let N := T.vertexBlock p
  let B := T.surfaceBase {(p : E)}
  have hBN : B ⊆ N.space := (T.vertex_base_eq_inter p).subset.trans inter_subset_left
  have hBD (x : N.space) : (x : E) ∈ B ↔
      (x : E) ∈ (T.marked 2).space := by
    change (x : E) ∈ T.surfaceBase {(p : E)} ↔ _
    rw [T.vertex_base_eq_inter]
    exact and_iff_right x.property
  obtain ⟨boundary, C, L, G, hC, hcv, hz, hrep, hG, hbp, hlink, _, _, hdisk, hfront⟩ :=
    T.exists_vertex_base_convex_chart p
  have hinter (hp : (p : E) ∉ (T.marked 1).space) (x : N.space) :
      ((x : E) ∈ (T.marked 2).space ↔ (G x : C3).2 = 0) ∧
        (x : E) ∉ (T.marked 1).space := by
    have hfalse : boundary ≠ true := fun h => hp (hbp.mp h)
    constructor
    · simpa only [hfalse, Bool.false_eq_true, false_implies, true_and] using hdisk x
    · exact fun h => hfalse ((hfront x).mp h).1
  have hboundary (hp : (p : E) ∈ (T.marked 1).space) (x : N.space) :
      ((x : E) ∈ (T.marked 2).space ↔
        (G x : C3).2 = 0 ∧ 0 ≤ (G x : C3).1.1) ∧
      ((x : E) ∈ (T.marked 1).space ↔ (G x : C3).1.1 = 0) := by
    have htrue := hbp.mpr hp
    constructor
    · simpa only [htrue, true_implies, and_comm] using hdisk x
    · simpa only [htrue, true_and] using hfront x
  obtain ⟨hfull, hplus, q0, q1, hq, haxis, hcap, hmeet⟩ :=
    PoincareConjecture.M76.HamiltonIndexOne.exists_convex_vertex_base_models hC hcv hz L hrep
  obtain ⟨g, hg, hgval⟩ := hG.symm
  have hginj : InjOn g C := by
    intro x hx y hy hxy
    have he : G.symm ⟨x, hx⟩ = G.symm ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hgval] using hxy
    exact congrArg Subtype.val (G.symm.injective he)
  have himage (U : Set C3) (S : Set (E))
      (hUC : U ⊆ C) (hSN : S ⊆ N.space)
      (hiff : ∀ x : N.space, (G x : C3) ∈ U ↔ (x : E) ∈ S) :
      g '' U = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : (G.symm ⟨y, hUC hy⟩ : E) ∈ S := (hiff _).mp (by
        simpa only [G.apply_symm_apply] using hy)
      rwa [hgval] at h
    · intro hx
      refine ⟨G ⟨x, hSN hx⟩, (hiff _).mpr hx, ?_⟩
      rw [← hgval, G.symm_apply_apply]
  have houterC : frontier C ∩ {x : C3 | x.2 = 0 ∧ 0 ≤ x.1.1} ⊆ C :=
    fun _ hx => hC.isClosed.frontier_subset hx.1
  by_cases hpfront : (p : E) ∈ (T.marked 1).space
  · have hbase : g '' (C ∩ {x : C3 | x.2 = 0 ∧ 0 ≤ x.1.1}) = B := by
      apply himage _ _ inter_subset_left hBN
      intro x
      exact ⟨fun hx => (hBD x).mpr (((hboundary hpfront x).1).mpr hx.2),
        fun hx => ⟨(G x).property, ((hboundary hpfront x).1).mp ((hBD x).mp hx)⟩⟩
    have houter : g '' (frontier C ∩ {x : C3 | x.2 = 0 ∧ 0 ≤ x.1.1}) =
        B ∩ (N.link p).space := by
      apply himage _ _ houterC (inter_subset_left.trans hBN)
      intro x
      constructor
      · intro hx
        exact ⟨(hBD x).mpr (((hboundary hpfront x).1).mpr hx.2), (hlink x).mpr hx.1⟩
      · intro hx
        exact ⟨(hlink x).mp hx.2, ((hboundary hpfront x).1).mp ((hBD x).mp hx.1)⟩
    have hfrontimage : g '' (C ∩ {x : C3 | x.2 = 0 ∧ x.1.1 = 0}) =
        B ∩ (T.marked 1).space := by
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
    rw [hbase, image_union, houter, hfrontimage] at hball
    refine ⟨?_, fun _ => ?_⟩
    · rwa [T.vertex_base_rim_eq]
    · have hq0 : q0 ∈ C := (haxis.1 (by simp)).1
      have hq1 : q1 ∈ C := (haxis.1 (by simp)).1
      refine ⟨g q0, g q1, fun heq => hq (hginj hq0 hq1 heq), ?_, ?_, ?_⟩
      · have h := haxis.image_of_subset hg inter_subset_left hginj
        simpa only [hfrontimage, image_pair] using h
      · have h := hcap.image_of_subset hg houterC hginj
        simpa only [houter, image_pair] using h
      · rw [← hfrontimage, ← houter, ← hginj.image_inter inter_subset_left houterC,
          hmeet, image_pair]
  · have hbase : g '' (C ∩ {x : C3 | x.2 = 0}) = B := by
      apply himage _ _ inter_subset_left hBN
      intro x
      exact ⟨fun hx => (hBD x).mpr (((hinter hpfront x).1).mpr hx.2),
        fun hx => ⟨(G x).property, ((hinter hpfront x).1).mp ((hBD x).mp hx)⟩⟩
    have houter : g '' (frontier C ∩ {x : C3 | x.2 = 0}) =
        B ∩ (N.link p).space := by
      apply himage _ _ (fun _ hx => hC.isClosed.frontier_subset hx.1)
        (inter_subset_left.trans hBN)
      intro x
      constructor
      · intro hx
        exact ⟨(hBD x).mpr (((hinter hpfront x).1).mpr hx.2), (hlink x).mpr hx.1⟩
      · intro hx
        exact ⟨(hlink x).mp hx.2, ((hinter hpfront x).1).mp ((hBD x).mp hx.1)⟩
    have hfrontempty : B ∩ (T.marked 1).space = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (hinter hpfront ⟨x, hBN hx.1⟩).2 hx.2
    have hball := hfull.image_of_subset hg inter_subset_left hginj
    rw [hbase, houter] at hball
    refine ⟨?_, fun hp => (hpfront hp).elim⟩
    rwa [T.vertex_base_rim_eq, hfrontempty, union_empty]

open Classical in

theorem vertex_base_ballPair (p : (T.marked 2).vertices) :
    IsFinitePLBallPair P2 (T.surfaceBase {(p : E)})
      (T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) :=
  (T.vertex_base_certificates p).1

open Classical in

theorem exists_boundary_vertex_base_intervals (p : (T.marked 2).vertices)
    (hpfront : (p : E) ∈ (T.marked 1).space) :
    ∃ a z : E, a ≠ z ∧
      IsFinitePLBallPair ℝ
        (T.surfaceBase {(p : E)} ∩ (T.marked 1).space) {a, z} ∧
      IsFinitePLBallPair ℝ
        (T.surfaceBase {(p : E)} ∩ ((T.vertexBlock p).link p).space)
        {a, z} ∧
      (T.surfaceBase {(p : E)} ∩ (T.marked 1).space) ∩
        (T.surfaceBase {(p : E)} ∩ ((T.vertexBlock p).link p).space) =
          {a, z} :=
  (T.vertex_base_certificates p).2 hpfront

end Geometry.SimplicialComplex.CoorientedSurfaceStars
