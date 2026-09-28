import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexHalfCharts
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarMarkedCutCharts
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)





theorem exists_vertex_base_convex_chart (p : (T.marked 2).vertices) :
    ∃ (boundary : Bool) (C : Set C3) (L : (Fin 3 ⊕ Fin 3) → C3 →ₗ[ℝ] ℝ)
      (G : (T.vertexBlock p).space ≃ₜ C),
      IsCompact C ∧ Convex ℝ C ∧ (0 : C3) ∈ interior C ∧
      C = {x | ∀ i, L i x ≤ 1} ∧ G.IsFinitePL ∧
      (boundary = true ↔ (p : T.index → ℝ × V3) ∈ (T.marked 1).space) ∧
      (∀ x : (T.vertexBlock p).space,
        (x : T.index → ℝ × V3) ∈ ((T.vertexBlock p).link p).space ↔
          (G x : C3) ∈ frontier C) ∧
      (∀ x : (T.vertexBlock p).space,
        ((G x : C3).2 = 0 ↔ T.height p x = 0) ∧
          (0 ≤ (G x : C3).2 ↔ 0 ≤ T.height p x)) ∧
      (∀ x : (T.vertexBlock p).space,
        (x : T.index → ℝ × V3) ∈ (T.marked 0).space ↔
          (boundary = true → 0 ≤ (G x : C3).1.1)) ∧
      (∀ x : (T.vertexBlock p).space,
        (x : T.index → ℝ × V3) ∈ (T.marked 2).space ↔
          (boundary = true → 0 ≤ (G x : C3).1.1) ∧ (G x : C3).2 = 0) ∧
      ∀ x : (T.vertexBlock p).space,
        (x : T.index → ℝ × V3) ∈ (T.marked 1).space ↔
          boundary = true ∧ (G x : C3).1.1 = 0 := by
  classical
  let N := T.vertexBlock p
  obtain ⟨hN, hpN, hstar, _⟩ := T.vertexBlock_centered_chart p
  obtain ⟨boundary, f, hf, hinj, hfp, hint, hheight, hregion, hdisk, hboundary⟩ :=
    T.exists_vertex_half_chart p (T.weight (T.chart_index p))
      (T.weight_nonzero (T.chart_index p))
  let J := hf.embeddedImage hinj
  have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hN
  have hJs : J.space = f '' N.space := hf.embeddedImage_space hinj
  have hJstar : (J.closedStar 0).space = f '' N.space := by
    have h := hf.embeddedImage_closedStar_space hinj hpN
    simpa only [hfp, hstar] using h
  have hJlink : (J.link 0).space = f '' (N.link p).space := by
    have h := hf.embeddedImage_link_space hinj hpN
    simpa only [hfp] using h
  have hzJ : (0 : C3) ∈ J.vertices := by
    rw [hf.embeddedImage_vertices hinj]
    exact ⟨p, hpN, hfp⟩
  let c : C3 ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Module.finrank_prod])
  let A : Bool → C3 →ₗ[ℝ] ℝ := fun k => if k then LinearMap.snd ℝ P2 ℝ else
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ P2 ℝ)
  obtain ⟨C, L, H, hC, hcv, hz, _, hrep, hH, hHlink, hcuts⟩ :=
    J.exists_finitePL_closedStar_chart_preserving_cut_family hJ hzJ
      (hJs.symm ▸ hint) c A
  let u : N.space ≃ₜ (J.closedStar 0).space :=
    (hf.homeomorphImage hN hinj).trans (Homeomorph.setCongr hJstar.symm)
  have hu : u.IsFinitePL := ⟨f, hf.finitePiecewiseAffineOn hN, fun _ => rfl⟩
  let G := u.trans H
  have hG : G.IsFinitePL := hu.trans hH
  have hlinksub : (N.link p).space ⊆ N.space :=
    SimplicialComplex.space_subset_of_le (show N.link p ≤ N from fun _ hs => hs.1)
  have hlink (x : N.space) : (x : T.index → ℝ × V3) ∈ (N.link p).space ↔
      (G x : C3) ∈ frontier C := by
    have hfx : f x ∈ (J.link 0).space ↔ (x : T.index → ℝ × V3) ∈ (N.link p).space := by
      rw [hJlink]
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hyx := hinj (hlinksub hy) x.property hxy
        simpa only [hyx] using hy
      · exact fun hx => mem_image_of_mem f hx
    exact hfx.symm.trans (hHlink (u x))
  have hnormal (x : N.space) : (G x : C3).2 = 0 ↔ (f x).2 = 0 :=
    (hcuts true (u x)).1
  have hnormalpos (x : N.space) : 0 ≤ (G x : C3).2 ↔ 0 ≤ (f x).2 :=
    (hcuts true (u x)).2
  have hfirstzero (x : N.space) : (G x : C3).1.1 = 0 ↔ (f x).1.1 = 0 :=
    (hcuts false (u x)).1
  have hfirstnonneg (x : N.space) : 0 ≤ (G x : C3).1.1 ↔ 0 ≤ (f x).1.1 :=
    (hcuts false (u x)).2
  have hboundaryp : boundary = true ↔
      (p : T.index → ℝ × V3) ∈ (T.marked 1).space := by
    have h := hboundary p (N.vertices_subset_space hpN)
    simpa only [hfp, Prod.zero_eq_mk, and_true] using h.symm
  refine ⟨boundary, C, L, G, hC, hcv, hz, hrep, hG, hboundaryp, hlink, ?_, ?_, ?_, ?_⟩
  · intro x
    have h0 := hnormal x
    have hpos := hnormalpos x
    rw [hheight] at h0 hpos
    exact ⟨h0, hpos⟩
  · intro x
    rw [hregion x x.property, hfirstnonneg x]
  · intro x
    rw [hdisk x x.property, hfirstnonneg x, hnormal x]
  · intro x
    rw [hboundary x x.property, hfirstzero x]

end PoincareConjecture.M76.OriginalProperDiskTriangulation
