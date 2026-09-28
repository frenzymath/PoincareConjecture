import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.EmbeddedThreeSkeleton
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Sections.LocalGraphIncidence

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology NNReal

universe u

namespace Poincare.Topology

set_option maxHeartbeats 4000000 in

theorem exists_embedded_three_transverse_section_grid
    {N : Nat} (hN : 3 < N) {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    (e : C(M, EuclideanSpace Real (Fin N)))
    (hs : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e)
    (he : _root_.Topology.IsClosedEmbedding e)
    (hi : ∀ p : M, Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p))
    (epsilon : NNReal) (hepsilon : 0 < epsilon)
    (heps : (epsilon : Real) ≤ ambientGridGap N (N - 4) / (1000 * (N + 1)))
    (hmax : Real) (hhmax : 0 < hmax) :
    ∃ h : Real, 0 < h ∧ h < hmax ∧
    ∃ rho : Real, 0 < rho ∧ 6 * (N + 1 : Real) * h < rho ∧
    ∃ K : Geometry.SimplicialComplex Real (EuclideanSpace Real (Fin N)),
      Set.Finite K.faces ∧
      (∀ x, infDist x (Set.range e) ≤ 10 * (N + 1 : Real) * h → x ∈ K.space) ∧
      (∀ s ∈ K.faces, s.card ≤ N + 1 ∧
        diam (convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) ≤
          2 * (N + 1 : Real) * h ∧
        (2 ≤ s.card → ∀ v ∈ s,
          h / 4 ≤ infDist v
            (affineSpan Real ((s.erase v : Finset (EuclideanSpace Real (Fin N))) :
              Set (EuclideanSpace Real (Fin N))) : Set (EuclideanSpace Real (Fin N))))) ∧
      (∀ s ∈ K.faces, s.card + 3 ≤ N →
        ∀ x ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N))),
          ambientGridGap N (N - 4) * h < infDist x (Set.range e)) ∧
      (∀ p : M, ∃ g : OpenPartialHomeomorph (embeddedThreeTangent e p) M,
        g.source = ball 0 (2 * rho) ∧ g 0 = p ∧
        (∀ v ∈ g.source,
          (embeddedThreeTangent e p).orthogonalProjectionOnto (e (g v) - e p) = v) ∧
        LipschitzOnWith epsilon (fun v : embeddedThreeTangent e p =>
          e (g v) - e p - (v : EuclideanSpace Real (Fin N))) g.source ∧
        (∀ q : M, dist (e q) (e p) < rho → q ∈ g.target)) ∧
      (∀ (p : M) (s : Finset (EuclideanSpace Real (Fin N))), s ∈ K.faces →
        (∀ x ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N))),
          ‖x - e p‖ ≤ 6 * (N + 1 : Real) * h) →
        ((∃ q : M, e q ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) ↔
          ∃ x ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N))),
            normalAffineConstraint (embeddedThreeTangent e p) (e p) x = 0) ∧
        (∀ v ∈ s, (∃ q : M,
          e q ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) →
          ∃ t : Finset (EuclideanSpace Real (Fin N)), t ∈ K.faces ∧ t ⊆ s ∧
            v ∈ t ∧ t.card = N - 2 ∧
            ∃ x0 ∈ convexHull Real (t : Set (EuclideanSpace Real (Fin N))),
              normalAffineConstraint (embeddedThreeTangent e p) (e p) x0 = 0 ∧
              ∃ q : M, e q ∈ convexHull Real (t : Set (EuclideanSpace Real (Fin N))) ∧
                ‖e q - x0‖ ≤
                  (diam (t : Set (EuclideanSpace Real (Fin N))) /
                    (ambientGridGap N (N - 4) * h / 2)) *
                      ((epsilon : Real) * (6 * (N + 1 : Real) * h)) ∧
                ∀ q' : M,
                  e q' ∈ convexHull Real (t : Set (EuclideanSpace Real (Fin N))) → q' = q)) := by
  classical
  let E := EuclideanSpace Real (Fin N)
  let L : Real := N + 1
  let b : Real := ambientGridGap N (N - 4)
  have hL : 0 < L := by dsimp [L]; positivity
  have hb : 0 < b := by
    dsimp [b, ambientGridGap, ambientGridMoveRatio, ambientGridSlabRatio]
    positivity
  have heps' : (epsilon : Real) * (1000 * L) ≤ b :=
    (le_div_iff₀ (by positivity : (0 : Real) < 1000 * L)).mp heps
  obtain ⟨rho, hrho, hg⟩ := exists_uniform_embedded_three_graph e hs he hi epsilon hepsilon
  obtain ⟨h, hh, hhcut, B, hB, w, H, K, hwfinite, hwmove, hHw, hHdist,
      hHlip, hHaff, hKfaces, hKfinite, hKcover, hKgeom, hKstar, hKgap⟩ :=
    exists_embedded_three_avoiding_ambient_grid hN e hs he hi
      (min hmax (rho / (100 * L))) (by positivity)
  have hhhmax : h < hmax := hhcut.trans_le (min_le_left _ _)
  have hhrho : h * (100 * L) < rho :=
    (lt_div_iff₀ (by positivity : (0 : Real) < 100 * L)).mp
      (hhcut.trans_le (min_le_right _ _))
  have hRrho : 6 * L * h < rho := by nlinarith [mul_pos hL hh]
  have ha : 0 < b * h / 2 := by positivity
  have hepsR : (epsilon : Real) * (6 * L * h) < b * h / 2 := by
    have hmul := mul_le_mul_of_nonneg_right heps' hh.le
    nlinarith [mul_pos hb hh]
  have hgapbound : b * h / 2 + (epsilon : Real) * (6 * L * h) ≤ b * h := by
    linarith
  refine ⟨h, hh, hhhmax, rho, hrho, hRrho, K, hKfinite, hKcover,
    hKgeom, hKgap, hg, ?_⟩
  intro p s hsK hsize
  let T := embeddedThreeTangent e p
  have hdim : Module.finrank Real Tᗮ + 3 = N := by
    have h := T.finrank_add_finrank_orthogonal
    rw [show Module.finrank Real T = 3 from embeddedThreeTangent_finrank e p (hi p),
      finrank_euclideanSpace_fin] at h
    omega
  obtain ⟨g, hgs, hg0, hgproj, hglip, hgcover⟩ := hg p
  have hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real Tᗮ →
      ∀ x ∈ convexHull Real (t : Set E),
        b * h / 2 + (epsilon : Real) * (6 * L * h) ≤ infDist x (Set.range e) := by
    intro t hts htcard x hx
    have htne : t.Nonempty := by
      by_contra hn
      have ht : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [ht, Finset.coe_empty, convexHull_empty, Set.mem_empty_iff_false] at hx
    have htK : t ∈ K.faces := K.down_closed hsK hts htne
    exact hgapbound.trans (hKgap t htK (by omega) x hx).le
  have hdiam : diam (s : Set E) ≤ 2 * L * h := by
    exact (diam_mono (subset_convexHull Real (s : Set E))
      (s.finite_toSet.isCompact_convexHull Real).isBounded).trans (hKgeom s hsK).2.1
  have hcontract : (epsilon : Real) * (diam (s : Set E) / (b * h / 2)) < 1 := by
    have hnum : (epsilon : Real) * diam (s : Set E) < b * h / 2 := by
      have hmul := mul_le_mul_of_nonneg_right heps' hh.le
      have hd := mul_le_mul_of_nonneg_left hdiam epsilon.coe_nonneg
      nlinarith [mul_pos hb hh]
    rw [← mul_div_assoc]
    exact (div_lt_one ha).mpr hnum
  obtain ⟨hiff, hminimal⟩ := local_graph_section_incidence e he.injective p g
    rho (6 * L * h) (b * h / 2) epsilon hgs hg0 hgproj hglip hgcover s
      (K.nonempty_of_mem_faces hsK) ha hRrho hsize hgap hepsR hcontract
  refine ⟨hiff, ?_⟩
  intro v hv hmeet
  obtain ⟨t, hts, hvt, htcard, x0, hx0, hAx0, q, hq, herr, huniq⟩ :=
    hminimal v hv hmeet
  change t.card = Module.finrank Real Tᗮ + 1 at htcard
  exact ⟨t, K.down_closed hsK hts ⟨v, hvt⟩, hts, hvt, by omega,
    x0, hx0, hAx0, q, hq, herr, huniq⟩

end Poincare.Topology
