import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.Flags.EmbeddedThreeFlagGrid
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Sections.LocalGraphCenters

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators Manifold ContDiff Topology NNReal

universe u

namespace Poincare.Topology

set_option maxHeartbeats 3000000 in

theorem EmbeddedThreeFlagGrid.local_centers
    {N : Nat} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {e : C(M, EuclideanSpace Real (Fin N))} {epsilon : NNReal}
    (G : EmbeddedThreeFlagGrid e epsilon) (p : M)
    (s : Finset (EuclideanSpace Real (Fin N))) (hsK : s ∈ G.K.faces)
    (hsize : ∀ x ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N))),
      ‖x - e p‖ ≤ 6 * (N + 1 : Real) * G.h) :
    ((∃ q : M, e q ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) ↔
      ∃ x ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N))),
        normalAffineConstraint (embeddedThreeTangent e p) (e p) x = 0) ∧
    ((∃ q : M, e q ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) →
      let P := {x | normalAffineConstraint (embeddedThreeTangent e p) (e p) x = 0}
      normalAffineConstraint (embeddedThreeTangent e p) (e p)
        (finiteSectionCenter P (N - 2) s) = 0 ∧
      (∃ w : EuclideanSpace Real (Fin N) → Real,
        (∀ v ∈ s, ambientGridGap N (N - 4) /
          (4 * (N + 1 : Real) * (2 : Real) ^ (N + 1)) ≤ w v) ∧
        (∑ v ∈ s, w v) = 1 ∧
        (∑ v ∈ s, w v • v) = finiteSectionCenter P (N - 2) s) ∧
      ‖finiteSectionCenter (Set.range e) (N - 2) s -
          finiteSectionCenter P (N - 2) s‖ ≤
        24 * (N + 1 : Real) ^ 2 * (epsilon : Real) * G.h /
          ambientGridGap N (N - 4)) := by
  classical
  let E := EuclideanSpace Real (Fin N)
  let T := embeddedThreeTangent e p
  let A := normalAffineConstraint T (e p)
  let P : Set E := {x | A x = 0}
  let L : Real := N + 1
  let b : Real := ambientGridGap N (N - 4)
  have hL : 0 < L := by dsimp [L]; positivity
  have hb : 0 < b := by
    dsimp [b, ambientGridGap, ambientGridMoveRatio, ambientGridSlabRatio]
    positivity
  have hdim : Module.finrank Real Tᗮ + 3 = N := by
    have h := T.finrank_add_finrank_orthogonal
    rw [show Module.finrank Real T = 3 from G.tangent_dimension p,
      finrank_euclideanSpace_fin] at h
    omega
  have hdimpos : 0 < Module.finrank Real Tᗮ := by
    have hN := G.ambient_dimension
    omega
  have hk : Module.finrank Real Tᗮ + 1 = N - 2 := by omega
  have heps : (epsilon : Real) * (1000 * L) ≤ b :=
    (le_div_iff₀ (by positivity : (0 : Real) < 1000 * L)).mp G.epsilon_small
  have hh : 0 < G.h := G.h_pos
  have ha : 0 < b * G.h / 2 := by positivity
  have hD : 0 < 2 * L * G.h := by positivity
  have hsmall : (epsilon : Real) * (6 * L * G.h) < b * G.h / 2 := by
    have hmul := mul_le_mul_of_nonneg_right heps G.h_pos.le
    nlinarith [mul_pos hb G.h_pos]
  have hgapbound : b * G.h / 2 + (epsilon : Real) * (6 * L * G.h) ≤ b * G.h := by
    linarith
  have hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real Tᗮ →
      ∀ x ∈ convexHull Real (t : Set E),
        b * G.h / 2 + (epsilon : Real) * (6 * L * G.h) ≤ infDist x (Set.range e) := by
    intro t hts htc x hx
    have htne : t.Nonempty := by
      by_contra hn
      have ht := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [ht, Finset.coe_empty, convexHull_empty, Set.mem_empty_iff_false] at hx
    exact hgapbound.trans
      (G.gap t (G.K.down_closed hsK hts htne) (by omega) x hx).le
  have hdiam : diam (s : Set E) ≤ 2 * L * G.h :=
    (diam_mono (subset_convexHull Real (s : Set E))
      (s.finite_toSet.isCompact_convexHull Real).isBounded).trans (G.geometry s hsK).2.1
  have hcontract : (epsilon : Real) * (diam (s : Set E) / (b * G.h / 2)) < 1 := by
    rw [← mul_div_assoc]
    apply (div_lt_one ha).mpr
    have hmul := mul_le_mul_of_nonneg_right heps G.h_pos.le
    have hd := mul_le_mul_of_nonneg_left hdiam epsilon.coe_nonneg
    nlinarith [mul_pos hb G.h_pos]
  obtain ⟨g, hgs, hg0, hgproj, hglip, hgcover⟩ := G.charts p
  obtain ⟨hiff, hminimal⟩ := local_graph_section_incidence e G.injective p g
    G.rho (6 * L * G.h) (b * G.h / 2) epsilon hgs hg0 hgproj hglip hgcover
    s (G.K.nonempty_of_mem_faces hsK) ha G.radius_lt hsize hgap hsmall hcontract
  refine ⟨hiff, ?_⟩
  intro hmeet
  change A (finiteSectionCenter P (N - 2) s) = 0 ∧ _
  obtain ⟨_, _, herr, w, _, hsum, hval, hbound⟩ :=
    local_graph_section_centers_comparison e G.injective p g G.rho
      (6 * L * G.h) (b * G.h / 2) (2 * L * G.h) epsilon
      hgs hg0 hgproj hglip hgcover s (G.K.nonempty_of_mem_faces hsK) ha hD
      G.radius_lt hdimpos hsize (G.geometry s hsK).2.1 hgap hsmall hcontract hmeet
  change ‖finiteSectionCenter (Set.range e) (Module.finrank Real Tᗮ + 1) s -
    finiteSectionCenter P (Module.finrank Real Tᗮ + 1) s‖ ≤ _ at herr
  change (∑ v ∈ s, w v • v) =
    finiteSectionCenter P (Module.finrank Real Tᗮ + 1) s at hval
  rw [hk] at herr hval
  have hFne : (minimalSectionFaces P (N - 2) s).Nonempty := by
    obtain ⟨v, hv⟩ := G.K.nonempty_of_mem_faces hsK
    obtain ⟨t, hts, _, htc, x0, hx0, hAx0, _⟩ := hminimal v hv hmeet
    refine ⟨t, (mem_minimalSectionFaces P (N - 2) s t).mpr
      ⟨hts, ?_, x0, hx0, hAx0⟩⟩
    change t.card = Module.finrank Real Tᗮ + 1 at htc
    exact htc.trans hk
  have hcenter : finiteSectionCenter P (N - 2) s ∈ P := by
    have hPconvex : Convex Real P := (convex_singleton (0 : Tᗮ)).affine_preimage A
    unfold finiteSectionCenter
    apply hPconvex.centerMass_mem (fun _ _ => zero_le_one)
    · simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hFne.card_pos
    · intro t ht
      exact (sectionFacePoint_mem P t
        ((mem_minimalSectionFaces P (N - 2) s t).mp ht).2.2).2
  refine ⟨hcenter, ⟨w, ?_, hsum, hval⟩, ?_⟩
  · intro v hv
    have hpow : (2 : Real) ^ s.card ≤ (2 : Real) ^ (N + 1) :=
      pow_le_pow_right₀ (by norm_num) (G.geometry s hsK).1
    calc
      b / (4 * L * (2 : Real) ^ (N + 1)) ≤ b / (4 * L * (2 : Real) ^ s.card) :=
        div_le_div_of_nonneg_left hb.le (by positivity)
          (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = (b * G.h / 2) / ((2 * L * G.h) * (2 : Real) ^ s.card) := by
        field_simp [ne_of_gt hh, ne_of_gt hb, ne_of_gt hL]
        ring
      _ ≤ w v := hbound v hv
  · apply herr.trans_eq
    change (2 * L * G.h / (b * G.h / 2)) *
      ((epsilon : Real) * (6 * L * G.h)) = 24 * L ^ 2 * (epsilon : Real) * G.h / b
    field_simp [ne_of_gt hh, ne_of_gt hb, ne_of_gt hL]
    ring

end Poincare.Topology
