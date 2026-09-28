import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.EmbeddedThreeSections
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Sections.FiniteSectionCenters

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators Manifold ContDiff Topology NNReal

universe u

namespace Poincare.Topology

set_option maxHeartbeats 4000000 in

theorem exists_embedded_three_section_centers
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
      (∀ s ∈ K.faces,
        (∃ q : M, e q ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) →
        N - 2 ≤ s.card ∧
        (∀ v ∈ s, ∃ t ∈ minimalSectionFaces (Set.range e) (N - 2) s, v ∈ t) ∧
        ∃ w : EuclideanSpace Real (Fin N) → Real,
          (∀ v ∈ s, 0 ≤ w v) ∧ (∑ v ∈ s, w v) = 1 ∧
          (∑ v ∈ s, w v • v) = finiteSectionCenter (Set.range e) (N - 2) s ∧
          ∀ v ∈ s, ambientGridGap N (N - 4) /
            (2 * (N + 1 : Real) * (2 : Real) ^ (N + 1)) ≤ w v) ∧
      (∀ s ∈ K.faces, s.card = N - 2 →
        (∃ q : M, e q ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) →
        ∃! q : M, e q ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) := by
  classical
  let E := EuclideanSpace Real (Fin N)
  let L : Real := N + 1
  let b := ambientGridGap N (N - 4)
  have hL : 0 < L := by dsimp [L]; positivity
  have hb : 0 < b := by
    dsimp [b, ambientGridGap, ambientGridMoveRatio, ambientGridSlabRatio]
    positivity
  obtain ⟨h, hh, hhhmax, rho, hrho, hRrho, K, hKfinite, hKcover,
      hKgeom, hKgap, hg, hlocal⟩ :=
    exists_embedded_three_transverse_section_grid hN e hs he hi epsilon hepsilon heps hmax hhmax
  have hglobal (s : Finset E) (hsK : s ∈ K.faces)
      (hmeet : ∃ q : M, e q ∈ convexHull Real (s : Set E)) :
      ∀ v ∈ s, ∃ t : Finset E, t ∈ K.faces ∧ t ⊆ s ∧ v ∈ t ∧ t.card = N - 2 ∧
        ∃! q : M, e q ∈ convexHull Real (t : Set E) := by
    obtain ⟨q0, hq0⟩ := hmeet
    have hsize : ∀ x ∈ convexHull Real (s : Set E), ‖x - e q0‖ ≤ 6 * L * h := by
      intro x hx
      calc
        ‖x - e q0‖ = dist x (e q0) := (dist_eq_norm _ _).symm
        _ ≤ diam (convexHull Real (s : Set E)) :=
          dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull Real).isBounded hx hq0
        _ ≤ 2 * L * h := (hKgeom s hsK).2.1
        _ ≤ 6 * L * h := by nlinarith [mul_pos hL hh]
    intro v hv
    obtain ⟨t, htK, hts, hvt, htc, x0, hx0, hAx0, q, hq, herr, huniq⟩ :=
      (hlocal q0 s hsK hsize).2 v hv ⟨q0, hq0⟩
    exact ⟨t, htK, hts, hvt, htc, q, hq, huniq⟩
  refine ⟨h, hh, hhhmax, rho, hrho, hRrho, K, hKfinite, hKcover,
    hKgeom, hKgap, hg, ?_, ?_⟩
  · intro s hsK hmeet
    have hinc : ∀ v ∈ s, ∃ t : Finset E, t ⊆ s ∧ v ∈ t ∧ t.card = N - 2 ∧
        ∃ x ∈ convexHull Real (t : Set E), x ∈ Set.range e := by
      intro v hv
      obtain ⟨t, _, hts, hvt, htc, q, hq, _⟩ := hglobal s hsK hmeet v hv
      exact ⟨t, hts, hvt, htc, e q, hq, Set.mem_range_self q⟩
    have hlow : N - 2 ≤ s.card := by
      obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hsK
      obtain ⟨t, hts, _, htc, _⟩ := hinc v hv
      rw [← htc]
      exact Finset.card_le_card hts
    have hgap : ∀ t : Finset E, t ⊆ s → t.card < N - 2 →
        ∀ y ∈ convexHull Real (t : Set E), b * h ≤ infDist y (Set.range e) := by
      intro t hts htcard y hy
      have htne : t.Nonempty := by
        by_contra hn
        have ht := Finset.not_nonempty_iff_eq_empty.mp hn
        simp only [ht, Finset.coe_empty, convexHull_empty, Set.mem_empty_iff_false] at hy
      exact (hKgap t (K.down_closed hsK hts htne) (by omega) y hy).le
    obtain ⟨w, hw, hwsum, hwpoint, hwbound⟩ := finiteSectionCenter_coordinates
      (Set.range e) (N - 2) (by omega) s (K.nonempty_of_mem_faces hsK)
        (b * h) (2 * L * h) (mul_pos hb hh) (by positivity)
        (hKgeom s hsK).2.1 hgap hinc
    refine ⟨hlow, ?_, w, hw, hwsum, hwpoint, ?_⟩
    · intro v hv
      obtain ⟨t, hts, hvt, htc, htm⟩ := hinc v hv
      exact ⟨t, (mem_minimalSectionFaces (Set.range e) (N - 2) s t).mpr
        ⟨hts, htc, htm⟩, hvt⟩
    · intro v hv
      have hpow : (2 : Real) ^ s.card ≤ (2 : Real) ^ (N + 1) :=
        pow_le_pow_right₀ (by norm_num) (hKgeom s hsK).1
      calc
        b / (2 * L * (2 : Real) ^ (N + 1)) ≤ b / (2 * L * (2 : Real) ^ s.card) :=
          div_le_div_of_nonneg_left hb.le (by positivity)
            (mul_le_mul_of_nonneg_left hpow (by positivity))
        _ = b * h / ((2 * L * h) * (2 : Real) ^ s.card) := by
          field_simp
        _ ≤ w v := hwbound v hv
  · intro s hsK hcard hmeet
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hsK
    obtain ⟨t, htK, hts, hvt, htc, huniq⟩ := hglobal s hsK hmeet v hv
    have heq : t = s := Finset.eq_of_subset_of_card_le hts (by omega)
    simpa only [heq] using huniq

end Poincare.Topology
