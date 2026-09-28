


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Endpoints
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.VertexCaps








set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))



theorem exists_vertex_caps_matching_edges
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (x : D.vertices → Bool × Bool → M)
    (hchart : ∀ p i, (P p).closedSector i ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x p i)).source) :
    ∃ (ε : ℝ) (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
      (cut : D.EdgeIndex → Bool → ℝ),
      0 < ε ∧ (∀ p, (B p).scale = ε) ∧
      ∀ (a : D.EdgeIndex) (terminal : Bool), cut a terminal ∈ Ioo (0 : ℝ) (1 / 3) ∧
        ∃ (i j : Bool × Bool) (k : Fin 3), i ≠ j ∧ (k = 1 ∨ k = 2) ∧
          (((B (D.edgeEndpoint a terminal)).face i).boundary k).map '' Icc (0 : ℝ) 1 =
            D.edgeFromEndpoint a terminal '' Icc 0 (cut a terminal) ∧
          (((B (D.edgeEndpoint a terminal)).face j).boundary k).map '' Icc (0 : ℝ) 1 =
            D.edgeFromEndpoint a terminal '' Icc 0 (cut a terminal) ∧
          ∀ s, s = i ∨ s = j →
            (((B (D.edgeEndpoint a terminal)).face s).boundary k).map 0 =
              (D.edgeEndpoint a terminal : M) ∧
            (((B (D.edgeEndpoint a terminal)).face s).boundary k).map 1 =
              D.edgeFromEndpoint a terminal (cut a terminal) ∧
            ∃ A : OpenPartialHomeomorph ℝ ℝ,
              A (B (D.edgeEndpoint a terminal)).scale = cut a terminal ∧
              Icc 0 (B (D.edgeEndpoint a terminal)).scale ⊆ A.source ∧
              StrictMonoOn A A.source ∧ ContDiffOn ℝ ∞ A A.source ∧
              ContDiffOn ℝ ∞ A.symm A.target ∧
              ∀ u ∈ Icc 0 (B (D.edgeEndpoint a terminal)).scale,
                D.edgeFromEndpoint a terminal (A u) =
                  (P (D.edgeEndpoint a terminal)).sectorCoordinates s
                    (if k = 1 then (0, u) else (u, 0)) := by
  classical
  choose ρ hρ hcaps using fun p => (P p).exists_vertexCapFaces_at_scale (x p) (hchart p)
  have hparams (e : D.EdgeIndex × Bool) := D.exists_edgeVertexParameters
    (P (D.edgeEndpoint e.1 e.2)) (hlocal (D.edgeEndpoint e.1 e.2)) e.1
    (t₀ := if e.2 then 1 else 0) (d := if e.2 then -1 else 1)
    (by cases e.2 <;> norm_num)
    (by cases e.2 <;> rfl)
  choose horizontal sign δ A hsign hδ hwidth hzero hsource hmono hsmooth hinvsmooth
    hinverse hbound hpositive hside hend using hparams
  have hsmall (e : D.EdgeIndex × Bool) : ∀ᶠ t in 𝓝 (0 : ℝ), A e t < 1 / 3 := by
    have hA0 : 0 ∈ (A e).source := hsource e (left_mem_Icc.mpr (hδ e).le)
    have hcont := (A e).continuousAt hA0
    have hlt : A e 0 < 1 / 3 := by rw [hzero e]; norm_num
    exact hcont.eventually_lt continuousAt_const hlt
  have hnbhd : ∀ᶠ t in 𝓝 (0 : ℝ),
      (∀ p, t < ρ p) ∧ ∀ e, t < δ e ∧ A e t < 1 / 3 :=
    (eventually_all.mpr (fun p => Iio_mem_nhds (hρ p))).and
      (eventually_all.mpr (fun e =>
        (show ∀ᶠ t in 𝓝 (0 : ℝ), t < δ e from Iio_mem_nhds (hδ e)).and (hsmall e)))
  obtain ⟨l, r, h0, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnbhd
  let ε := r / 2
  have hε : 0 < ε := half_pos h0.2
  have hεsmall := hsub (show ε ∈ Ioo l r from
    ⟨h0.1.trans hε, half_lt_self h0.2⟩)
  choose B hscale using fun p => hcaps p ε hε (hεsmall.1 p)
  refine ⟨ε, B, (fun a b => A (a, b) ε), hε, hscale, ?_⟩
  intro a terminal
  let e : D.EdgeIndex × Bool := (a, terminal)
  have hu : ε ∈ Ioc 0 (δ e) := ⟨hε, (hεsmall.2 e).1.le⟩
  refine ⟨⟨(hpositive e ε hu).1, (hεsmall.2 e).2⟩, ?_⟩
  have himage (i : Bool × Bool)
      (hi : (if (if horizontal e then i.1 else i.2) then (1 : ℝ) else -1) = sign e) :
      D.edgeFromEndpoint a terminal '' Icc 0 (A e ε) =
        (fun v => (P (D.edgeEndpoint a terminal)).sectorCoordinates i
          (signedAxis (horizontal e) 1 v)) '' Icc 0 ε := by
    simpa only [e, ← D.edgeFromEndpoint_eq] using (hside e i hi).2 ε hu
  have hradial (i : Bool × Bool)
      (hi : (if (if horizontal e then i.1 else i.2) then (1 : ℝ) else -1) = sign e) :
      (((B (D.edgeEndpoint a terminal)).face i).boundary
        (if horizontal e then 2 else 1)).map '' Icc (0 : ℝ) 1 =
          D.edgeFromEndpoint a terminal '' Icc 0 (A e ε) := by
    rw [himage i hi]
    cases hk : horizontal e
    · simpa only [hk, Bool.false_eq_true, ite_false, signedAxis, one_mul, hscale,
        ChartCircleArrangementVertexPatch.secondSide] using
          (B (D.edgeEndpoint a terminal)).second_image i
    · simpa only [hk, ite_true, signedAxis, one_mul, hscale,
        ChartCircleArrangementVertexPatch.firstSide] using
          (B (D.edgeEndpoint a terminal)).first_image i
  have hendpoints (i : Bool × Bool)
      (hi : (if (if horizontal e then i.1 else i.2) then (1 : ℝ) else -1) = sign e) :
      (((B (D.edgeEndpoint a terminal)).face i).boundary
        (if horizontal e then 2 else 1)).map 0 = (D.edgeEndpoint a terminal : M) ∧
      (((B (D.edgeEndpoint a terminal)).face i).boundary
        (if horizontal e then 2 else 1)).map 1 = D.edgeFromEndpoint a terminal (A e ε) := by
    have hmap : D.edgeFromEndpoint a terminal (A e ε) =
        (P (D.edgeEndpoint a terminal)).sectorCoordinates i
          (signedAxis (horizontal e) 1 ε) := by
      simpa only [e, ← D.edgeFromEndpoint_eq] using (hside e i hi).1 ε ⟨hε.le, hu.2⟩
    cases hk : horizontal e
    · constructor
      · simpa only [hk, Bool.false_eq_true, ite_false, zero_mul, Prod.mk_zero_zero,
          ChartCircleArrangementVertexPatch.sectorCoordinates_zero] using
          (B (D.edgeEndpoint a terminal)).second_map i 0 (by norm_num)
      · simpa only [hk, Bool.false_eq_true, ite_false, one_mul, hscale,
          signedAxis] using
          ((B (D.edgeEndpoint a terminal)).second_map i 1 (by norm_num)).trans
            (by simpa only [hk, Bool.false_eq_true, ite_false, signedAxis, one_mul, hscale] using hmap.symm)
    · constructor
      · simpa only [hk, ite_true, zero_mul, Prod.mk_zero_zero,
          ChartCircleArrangementVertexPatch.sectorCoordinates_zero] using
          (B (D.edgeEndpoint a terminal)).first_map i 0 (by norm_num)
      · simpa only [hk, ite_true, one_mul, hscale, signedAxis] using
          ((B (D.edgeEndpoint a terminal)).first_map i 1 (by norm_num)).trans
            (by simpa only [hk, ite_true, signedAxis, one_mul, hscale] using hmap.symm)
  have hparameters (i : Bool × Bool)
      (hi : (if (if horizontal e then i.1 else i.2) then (1 : ℝ) else -1) = sign e) :
      ∃ A' : OpenPartialHomeomorph ℝ ℝ,
        A' (B (D.edgeEndpoint a terminal)).scale = A e ε ∧
        Icc 0 (B (D.edgeEndpoint a terminal)).scale ⊆ A'.source ∧
        StrictMonoOn A' A'.source ∧ ContDiffOn ℝ ∞ A' A'.source ∧
        ContDiffOn ℝ ∞ A'.symm A'.target ∧
        ∀ u ∈ Icc 0 (B (D.edgeEndpoint a terminal)).scale,
          D.edgeFromEndpoint a terminal (A' u) =
            (P (D.edgeEndpoint a terminal)).sectorCoordinates i
              (if (if horizontal e then (2 : Fin 3) else 1) = 1 then (0, u) else (u, 0)) := by
    have hinterval : Icc (0 : ℝ) (B (D.edgeEndpoint a terminal)).scale ⊆ Icc 0 (δ e) := by
      rw [hscale]
      exact Icc_subset_Icc_right hu.2
    refine ⟨A e, by rw [hscale], hinterval.trans (hsource e),
      hmono e, hsmooth e, hinvsmooth e, ?_⟩
    intro u hu
    have h := (hside e i hi).1 u (hinterval hu)
    cases hk : horizontal e <;>
      simpa only [e, ← D.edgeFromEndpoint_eq, hk, Bool.false_eq_true,
        ite_false, ite_true, signedAxis, one_mul,
        show (2 : Fin 3) ≠ 1 by decide] using h
  rcases hsign e with hsign | hsign <;> cases hk : horizontal e
  · refine ⟨(false, true), (true, true), 1, by decide, by decide,
      by simpa [hk] using hradial (false, true) (by simp [hk, hsign]),
      by simpa [hk] using hradial (true, true) (by simp [hk, hsign]), ?_⟩
    intro s hs
    rcases hs with rfl | rfl <;>
      exact ⟨by simpa [hk] using (hendpoints _ (by simp [hk, hsign])).1,
        by simpa [hk] using (hendpoints _ (by simp [hk, hsign])).2,
        by simpa [hk] using hparameters _ (by simp [hk, hsign])⟩
  · refine ⟨(true, false), (true, true), 2, by decide, by decide,
      by simpa [hk] using hradial (true, false) (by simp [hk, hsign]),
      by simpa [hk] using hradial (true, true) (by simp [hk, hsign]), ?_⟩
    intro s hs
    rcases hs with rfl | rfl <;>
      exact ⟨by simpa [hk] using (hendpoints _ (by simp [hk, hsign])).1,
        by simpa [hk] using (hendpoints _ (by simp [hk, hsign])).2,
        by simpa [hk] using hparameters _ (by simp [hk, hsign])⟩
  · refine ⟨(false, false), (true, false), 1, by decide, by decide,
      by simpa [hk] using hradial (false, false) (by simp [hk, hsign]),
      by simpa [hk] using hradial (true, false) (by simp [hk, hsign]), ?_⟩
    intro s hs
    rcases hs with rfl | rfl <;>
      exact ⟨by simpa [hk] using (hendpoints _ (by simp [hk, hsign])).1,
        by simpa [hk] using (hendpoints _ (by simp [hk, hsign])).2,
        by simpa [hk] using hparameters _ (by simp [hk, hsign])⟩
  · refine ⟨(false, false), (false, true), 2, by decide, by decide,
      by simpa [hk] using hradial (false, false) (by simp [hk, hsign]),
      by simpa [hk] using hradial (false, true) (by simp [hk, hsign]), ?_⟩
    intro s hs
    rcases hs with rfl | rfl <;>
      exact ⟨by simpa [hk] using (hendpoints _ (by simp [hk, hsign])).1,
        by simpa [hk] using (hendpoints _ (by simp [hk, hsign])).2,
        by simpa [hk] using hparameters _ (by simp [hk, hsign])⟩

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
