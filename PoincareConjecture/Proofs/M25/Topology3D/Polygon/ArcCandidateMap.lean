import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcCandidate
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcAuxiliaryEdges

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsSimplePolygonalArc.exists_minimal_arc_candidate_map
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    {n : ℕ} {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (X : E →ₗ[ℝ] ℝ) (hLR : X (p 0) < X (p (Fin.last (n + 1))))
    (hX : ∀ i, i ≠ 0 → i ≠ Fin.last (n + 1) →
      X (p 0) < X (p i) ∧ X (p i) < X (p (Fin.last (n + 1)))) :
    let B := {k : Fin (n + 2) | k ≠ 0 ∧ k ≠ Fin.last (n + 1) ∧
      ¬ IsAdmissibleArcVertex p k}
    ∃ g : Fin (n + 2) → Fin (n + 2),
      (∀ k, k ∉ B → g k = k) ∧
      (∀ k ∈ B, ∃ f : E ≃ᴬ[ℝ] (ℝ × ℝ),
        f (p k) = (0, 0) ∧ f (p ((finRotate (n + 2)).symm k)) = (1, 0) ∧
        f (p (finRotate (n + 2) k)) = (0, 1) ∧
        g k ≠ 0 ∧ g k ≠ Fin.last (n + 1) ∧ g k ≠ k ∧
        g k ≠ (finRotate (n + 2)).symm k ∧ g k ≠ finRotate (n + 2) k ∧
        f (p (g k)) ∈ unitTriangle ∧ 0 < (f (p (g k))).1 ∧
        0 < (f (p (g k))).2 ∧
        (∀ l, l ≠ k → l ≠ (finRotate (n + 2)).symm k →
          l ≠ finRotate (n + 2) k → f (p l) ∈ unitTriangle →
          (f (p (g k))).1 + (f (p (g k))).2 ≤ (f (p l)).1 + (f (p l)).2) ∧
        Disjoint (openSegment ℝ (p k) (p (g k))) (polygonArcBoundary p)) ∧
      (∀ k ∈ B, g k ≠ k) ∧
      (∀ k ∈ B, g k ∈ B → g (g k) ≠ k) ∧
      (∀ k ∈ B, Disjoint (openSegment ℝ (p k) (p (g k))) (polygonArcBoundary p)) ∧
      (∀ k ∈ B, ∀ l ∈ B, k ≠ l →
        segment ℝ (p k) (p (g k)) ∩ segment ℝ (p l) (p (g l)) =
          {p k, p (g k)} ∩ {p l, p (g l)}) := by
  classical
  dsimp only
  let B := {k : Fin (n + 2) | k ≠ 0 ∧ k ≠ Fin.last (n + 1) ∧
    ¬ IsAdmissibleArcVertex p k}
  have hc (k : B) := hp.exists_internal_minimal_triangle_vertex hdim
    k.val k.property.1 k.property.2.1 k.property.2.2 X hLR hX
  choose f j hf using hc
  let g (k : Fin (n + 2)) := if h : k ∈ B then j ⟨k, h⟩ else k
  have hg (k : Fin (n + 2)) (hk : k ∈ B) :
      ∃ F : E ≃ᴬ[ℝ] (ℝ × ℝ),
        F (p k) = (0, 0) ∧ F (p ((finRotate (n + 2)).symm k)) = (1, 0) ∧
        F (p (finRotate (n + 2) k)) = (0, 1) ∧
        g k ≠ 0 ∧ g k ≠ Fin.last (n + 1) ∧ g k ≠ k ∧
        g k ≠ (finRotate (n + 2)).symm k ∧ g k ≠ finRotate (n + 2) k ∧
        F (p (g k)) ∈ unitTriangle ∧ 0 < (F (p (g k))).1 ∧
        0 < (F (p (g k))).2 ∧
        (∀ l, l ≠ k → l ≠ (finRotate (n + 2)).symm k →
          l ≠ finRotate (n + 2) k → F (p l) ∈ unitTriangle →
          (F (p (g k))).1 + (F (p (g k))).2 ≤ (F (p l)).1 + (F (p l)).2) ∧
        Disjoint (openSegment ℝ (p k) (p (g k))) (polygonArcBoundary p) := by
    refine ⟨f ⟨k, hk⟩, ?_⟩
    simpa only [g, dif_pos hk] using hf ⟨k, hk⟩
  refine ⟨g, ?_, hg, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact dif_neg hk
  · intro k hk
    obtain ⟨F, _, _, _, _, _, hne, _⟩ := hg k hk
    exact hne
  · intro k hk hj hback
    obtain ⟨F, hFk, hFp, hFs, hj0, hjl, hjk, hjp, hjs, hjT, _, _, hmin, _⟩ := hg k hk
    have hex := hp.base_not_mem_minimal_candidate_triangle k (g k) F
      hk.1 hk.2.1 hj0 hjl hFk hFp hFs hjk hjp hjs hjT hmin
    obtain ⟨H, hHj, hHp, hHs, _, _, _, _, _, hhT, _⟩ := hg (g k) hj
    have him : H '' polygonVertexTriangle p (g k) = unitTriangle := by
      have hh := H.toAffineEquiv.toAffineMap.image_convexHull
        {p (g k), p ((finRotate (n + 2)).symm (g k)), p (finRotate (n + 2) (g k))}
      change H '' polygonVertexTriangle p (g k) =
        convexHull ℝ (H '' {p (g k), p ((finRotate (n + 2)).symm (g k)),
          p (finRotate (n + 2) (g k))}) at hh
      rw [hh, image_insert_eq, image_insert_eq, image_singleton, hHj, hHp, hHs,
        ← unitTriangle_eq_convexHull]
    have hmem : p (g (g k)) ∈ polygonVertexTriangle p (g k) := by
      obtain ⟨x, hx, heq⟩ := him.symm ▸ hhT
      exact H.injective heq ▸ hx
    apply hex
    simpa only [hback] using hmem
  · intro k hk
    obtain ⟨F, _, _, _, _, _, _, _, _, _, _, _, _, hvis⟩ := hg k hk
    exact hvis
  · intro k hk l hl hkl
    obtain ⟨F, hFk, hFp, hFs, hj0, hjl, hjk, hjp, hjs, hjT, _, _, hmin, _⟩ := hg k hk
    obtain ⟨H, hHl, hHp, hHs, hm0, hml, hmk, hmp, hms, hmT, _, _, hminH, _⟩ := hg l hl
    exact hp.segments_inter_eq_of_minimal_arc_candidates k (g k) F
      hk.1 hk.2.1 hj0 hjl hFk hFp hFs hjk hjp hjs hjT hmin l (g l) H
      hl.1 hl.2.1 hm0 hml hHl hHp hHs hmk hmp hms hmT hminH hkl

end PoincareConjecture.M25.Topology3D
