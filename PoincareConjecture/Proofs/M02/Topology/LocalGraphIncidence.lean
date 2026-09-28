import PoincareConjecture.Proofs.M02.Topology.LocalGraphSection
import PoincareConjecture.Proofs.M02.Topology.FiniteAffineIncidence

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal Topology

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

theorem local_graph_normal_equation
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] {M : Type v} [TopologicalSpace M]
    {T : Submodule Real E} [T.HasOrthogonalProjection]
    (e : C(M, E)) (p : M) (g : OpenPartialHomeomorph T M)
    (hgproj : ∀ v ∈ g.source,
      T.orthogonalProjectionOnto (e (g v) - e p) = v)
    (q : M) (hq : q ∈ g.target) :
    normalAffineConstraint T (e p) (e q) =
      Tᗮ.orthogonalProjectionOnto
        (e (g (T.orthogonalProjectionOnto (e q - e p))) - e p -
          (T.orthogonalProjectionOnto (e q - e p) : E)) := by
  have hcoord : T.orthogonalProjectionOnto (e q - e p) = g.symm q := by
    simpa only [g.right_inv hq] using hgproj (g.symm q) (g.map_target hq)
  change Tᗮ.orthogonalProjectionOnto (e q - e p) = _
  have hzero : Tᗮ.orthogonalProjectionOnto (g.symm q : E) = 0 :=
    Tᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal
      (T.le_orthogonal_orthogonal (g.symm q).property)
  simp only [hcoord, g.right_inv hq, map_sub, hzero, sub_zero]

theorem local_graph_distance_comparison
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] {M : Type v} [TopologicalSpace M]
    {T : Submodule Real E} [T.HasOrthogonalProjection]
    (e : C(M, E)) (p : M) (g : OpenPartialHomeomorph T M)
    (rho R : Real) (epsilon : NNReal)
    (hR : 0 ≤ R) (hRrho : R < rho)
    (hgs : g.source = ball (0 : T) (2 * rho)) (hg0 : g 0 = p)
    (hgproj : ∀ v ∈ g.source,
      T.orthogonalProjectionOnto (e (g v) - e p) = v)
    (hglip : LipschitzOnWith epsilon
      (fun v : T => e (g v) - e p - (v : E)) g.source)
    (hgcover : ∀ q : M, dist (e q) (e p) < rho → q ∈ g.target) :
    (∀ x : E, ‖x - e p‖ ≤ R →
      infDist x (Set.range e) ≤ ‖normalAffineConstraint T (e p) x‖ +
        (epsilon : Real) * R) ∧
    (∀ q : M, ‖e q - e p‖ ≤ R →
      ‖normalAffineConstraint T (e p) (e q)‖ ≤ (epsilon : Real) * R) := by
  have hrho : 0 < rho := hR.trans_lt hRrho
  have hzero : (0 : T) ∈ g.source := by
    rw [hgs]
    exact mem_ball_self (by linarith)
  have hcoord_source (x : E) (hx : ‖x - e p‖ ≤ R) :
      T.orthogonalProjectionOnto (x - e p) ∈ g.source := by
    rw [hgs, mem_ball_zero_iff]
    have h := (T.norm_orthogonalProjectionOnto_apply_le (x - e p)).trans hx
    exact h.trans_lt (by linarith)
  have herror (x : E) (hx : ‖x - e p‖ ≤ R) :
      ‖e (g (T.orthogonalProjectionOnto (x - e p))) - e p -
        (T.orthogonalProjectionOnto (x - e p) : E)‖ ≤ (epsilon : Real) * R := by
    have h := hglip.dist_le_mul (T.orthogonalProjectionOnto (x - e p))
      (hcoord_source x hx) 0 hzero
    simp only [hg0, Submodule.coe_zero, sub_self,
      dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      ((T.norm_orthogonalProjectionOnto_apply_le (x - e p)).trans hx) epsilon.coe_nonneg)
  constructor
  · intro x hx
    let w : T := T.orthogonalProjectionOnto (x - e p)
    have hnormal : ‖x - e p - (w : E)‖ = ‖normalAffineConstraint T (e p) x‖ := by
      change ‖x - e p - (w : E)‖ = ‖Tᗮ.starProjection (x - e p)‖
      rw [Submodule.starProjection_orthogonal_val]
      rfl
    have hdiff : x - e (g w) = (x - e p - (w : E)) -
        (e (g w) - e p - (w : E)) := by abel
    calc
      infDist x (Set.range e) ≤ dist x (e (g w)) :=
        infDist_le_dist_of_mem (Set.mem_range_self (g w))
      _ = ‖x - e (g w)‖ := dist_eq_norm _ _
      _ ≤ ‖x - e p - (w : E)‖ + ‖e (g w) - e p - (w : E)‖ := by
        rw [hdiff]
        exact norm_sub_le _ _
      _ ≤ ‖normalAffineConstraint T (e p) x‖ + (epsilon : Real) * R :=
        add_le_add hnormal.le (herror x hx)
  · intro q hq
    have hqt : q ∈ g.target := hgcover q (by
      simpa only [dist_eq_norm] using hq.trans_lt hRrho)
    rw [local_graph_normal_equation e p g hgproj q hqt]
    exact (Tᗮ.norm_orthogonalProjectionOnto_apply_le _).trans (herror (e q) hq)

theorem local_graph_section_incidence
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] {M : Type v} [TopologicalSpace M]
    {T : Submodule Real E} [T.HasOrthogonalProjection]
    (e : C(M, E)) (he : Function.Injective e) (p : M)
    (g : OpenPartialHomeomorph T M) (rho R a : Real) (epsilon : NNReal)
    (hgs : g.source = ball (0 : T) (2 * rho)) (hg0 : g 0 = p)
    (hgproj : ∀ v ∈ g.source,
      T.orthogonalProjectionOnto (e (g v) - e p) = v)
    (hglip : LipschitzOnWith epsilon
      (fun v : T => e (g v) - e p - (v : E)) g.source)
    (hgcover : ∀ q : M, dist (e q) (e p) < rho → q ∈ g.target)
    (s : Finset E) (hsne : s.Nonempty) (ha : 0 < a) (hRrho : R < rho)
    (hsize : ∀ x ∈ convexHull Real (s : Set E), ‖x - e p‖ ≤ R)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real Tᗮ →
      ∀ x ∈ convexHull Real (t : Set E),
        a + (epsilon : Real) * R ≤ infDist x (Set.range e))
    (hsmall : (epsilon : Real) * R < a)
    (hcontract : (epsilon : Real) * (diam (s : Set E) / a) < 1) :
    ((∃ q : M, e q ∈ convexHull Real (s : Set E)) ↔
      ∃ x ∈ convexHull Real (s : Set E), normalAffineConstraint T (e p) x = 0) ∧
    (∀ v ∈ s, (∃ q : M, e q ∈ convexHull Real (s : Set E)) →
      ∃ t : Finset E, t ⊆ s ∧ v ∈ t ∧
        t.card = Module.finrank Real Tᗮ + 1 ∧
        ∃ x0 ∈ convexHull Real (t : Set E),
          normalAffineConstraint T (e p) x0 = 0 ∧
          ∃ q : M, e q ∈ convexHull Real (t : Set E) ∧
            ‖e q - x0‖ ≤ (diam (t : Set E) / a) * ((epsilon : Real) * R) ∧
            ∀ q' : M, e q' ∈ convexHull Real (t : Set E) → q' = q) := by
  classical
  let A := normalAffineConstraint T (e p)
  obtain ⟨v0, hv0⟩ := hsne
  have hR : 0 ≤ R := (norm_nonneg (v0 - e p)).trans
    (hsize v0 (subset_convexHull Real _ hv0))
  obtain ⟨hdist, hnorm⟩ := local_graph_distance_comparison e p g rho R epsilon hR hRrho
    hgs hg0 hgproj hglip hgcover
  have hAgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real Tᗮ →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖ := by
    intro t ht htc x hx
    have h1 := hgap t ht htc x hx
    have h2 := hdist x (hsize x (convexHull_mono ht hx))
    change a ≤ ‖normalAffineConstraint T (e p) x‖
    linarith
  have hforward : (∃ q : M, e q ∈ convexHull Real (s : Set E)) →
      ∃ x ∈ convexHull Real (s : Set E), A x = 0 := by
    rintro ⟨q, hq⟩
    apply exists_zero_of_small_affine_faces_gap A s a hAgap
    exact ⟨e q, hq, (hnorm q (hsize (e q) hq)).trans_lt hsmall⟩
  have hminimal (v : E) (hv : v ∈ s)
      (hzero : ∃ x ∈ convexHull Real (s : Set E), A x = 0) :
      ∃ t : Finset E, t ⊆ s ∧ v ∈ t ∧
        t.card = Module.finrank Real Tᗮ + 1 ∧
        ∃ x0 ∈ convexHull Real (t : Set E), A x0 = 0 ∧
          ∃ q : M, e q ∈ convexHull Real (t : Set E) ∧
            ‖e q - x0‖ ≤ (diam (t : Set E) / a) * ((epsilon : Real) * R) ∧
            ∀ q' : M, e q' ∈ convexHull Real (t : Set E) → q' = q := by
    obtain ⟨t, hts, hvt, htcard, x0, hx0, hAx0⟩ :=
      exists_minimal_affine_section_face_through_vertex A s a ha hAgap hzero v hv
    have htgap : ∀ r : Finset E, r ⊆ t → r.card ≤ Module.finrank Real Tᗮ →
        ∀ x ∈ convexHull Real (r : Set E), a ≤ ‖A x‖ :=
      fun r hr => hAgap r (hr.trans hts)
    have htsize : ∀ x ∈ convexHull Real (t : Set E), ‖x - e p‖ ≤ R :=
      fun x hx => hsize x (convexHull_mono hts hx)
    have htcontract : (epsilon : Real) * (diam (t : Set E) / a) < 1 :=
      (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (diam_mono hts s.finite_toSet.isBounded) ha.le)
        epsilon.coe_nonneg).trans_lt hcontract
    obtain ⟨q, hq, herr, huniq⟩ := exists_unique_local_graph_section e he p g rho R a epsilon
      hgs hg0 hgproj hglip hgcover ha hRrho A t rfl htcard htgap x0 hx0 hAx0
      htsize hsmall.le htcontract
    refine ⟨t, hts, hvt, htcard, x0, hx0, hAx0, q, hq, herr, ?_⟩
    intro q' hq'
    apply huniq q' hq'
    exact local_graph_normal_equation e p g hgproj q' (hgcover q' (by
      simpa only [dist_eq_norm] using (htsize (e q') hq').trans_lt hRrho))
  refine ⟨⟨hforward, ?_⟩, ?_⟩
  · intro hzero
    obtain ⟨t, hts, _, _, x0, _, _, q, hq, _, _⟩ := hminimal v0 hv0 hzero
    exact ⟨q, convexHull_mono hts hq⟩
  · intro v hv hmeet
    exact hminimal v hv (hforward hmeet)

end PoincareConjecture.Proofs.M02.Topology
