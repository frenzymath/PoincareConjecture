import PoincareConjecture.Proofs.M02.Topology.LocalGraphIncidence
import PoincareConjecture.Proofs.M02.Topology.FiniteSectionCenters

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators NNReal

universe u v w

namespace PoincareConjecture.Proofs.M02.Topology

private theorem norm_centerMass_sub_le
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    {I : Type w} (s : Finset I) (hs : s.Nonempty) (f g : I → E) (D : Real)
    (h : ∀ i ∈ s, ‖f i - g i‖ ≤ D) :
    ‖s.centerMass (fun _ => (1 : Real)) f - s.centerMass (fun _ => (1 : Real)) g‖ ≤ D := by
  have hsum : 0 < ∑ i ∈ s, (1 : Real) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast hs.card_pos
  have hc := (convex_closedBall (0 : E) D).centerMass_mem
    (t := s) (w := fun _ => (1 : Real)) (z := fun i => f i - g i)
      (fun _ _ => zero_le_one) hsum (fun i hi => mem_closedBall_zero_iff.mpr (h i hi))
  have heq : s.centerMass (fun _ => (1 : Real)) (fun i => f i - g i) =
      s.centerMass (fun _ => (1 : Real)) f - s.centerMass (fun _ => (1 : Real)) g := by
    simp only [Finset.centerMass, one_smul, Finset.sum_sub_distrib, smul_sub]
  rw [heq] at hc
  exact mem_closedBall_zero_iff.mp hc

set_option maxHeartbeats 3000000 in

theorem local_graph_section_centers_comparison
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] {M : Type v} [TopologicalSpace M]
    {T : Submodule Real E} [T.HasOrthogonalProjection]
    (e : C(M, E)) (he : Function.Injective e) (p : M)
    (g : OpenPartialHomeomorph T M) (rho R a D : Real) (epsilon : NNReal)
    (hgs : g.source = ball (0 : T) (2 * rho)) (hg0 : g 0 = p)
    (hgproj : ∀ v ∈ g.source,
      T.orthogonalProjectionOnto (e (g v) - e p) = v)
    (hglip : LipschitzOnWith epsilon
      (fun v : T => e (g v) - e p - (v : E)) g.source)
    (hgcover : ∀ q : M, dist (e q) (e p) < rho → q ∈ g.target)
    (s : Finset E) (hsne : s.Nonempty) (ha : 0 < a) (hD : 0 < D)
    (hRrho : R < rho) (hdim : 0 < Module.finrank Real Tᗮ)
    (hsize : ∀ x ∈ convexHull Real (s : Set E), ‖x - e p‖ ≤ R)
    (hdiam : diam (convexHull Real (s : Set E)) ≤ D)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real Tᗮ →
      ∀ x ∈ convexHull Real (t : Set E),
        a + (epsilon : Real) * R ≤ infDist x (Set.range e))
    (hsmall : (epsilon : Real) * R < a)
    (hcontract : (epsilon : Real) * (diam (s : Set E) / a) < 1)
    (hmeet : ∃ q : M, e q ∈ convexHull Real (s : Set E)) :
    minimalSectionFaces (Set.range e) (Module.finrank Real Tᗮ + 1) s =
      minimalSectionFaces {x | normalAffineConstraint T (e p) x = 0}
        (Module.finrank Real Tᗮ + 1) s ∧
    (∀ t ∈ minimalSectionFaces (Set.range e) (Module.finrank Real Tᗮ + 1) s,
      ‖sectionFacePoint (Set.range e) t -
          sectionFacePoint {x | normalAffineConstraint T (e p) x = 0} t‖ ≤
        (diam (t : Set E) / a) * ((epsilon : Real) * R)) ∧
    ‖finiteSectionCenter (Set.range e) (Module.finrank Real Tᗮ + 1) s -
        finiteSectionCenter {x | normalAffineConstraint T (e p) x = 0}
          (Module.finrank Real Tᗮ + 1) s‖ ≤ (D / a) * ((epsilon : Real) * R) ∧
    ∃ w : E → Real, (∀ v ∈ s, 0 ≤ w v) ∧ (∑ v ∈ s, w v) = 1 ∧
      (∑ v ∈ s, w v • v) =
        finiteSectionCenter {x | normalAffineConstraint T (e p) x = 0}
          (Module.finrank Real Tᗮ + 1) s ∧
      ∀ v ∈ s, a / (D * (2 : Real) ^ s.card) ≤ w v := by
  classical
  let A := normalAffineConstraint T (e p)
  let P : Set E := {x | A x = 0}
  let k := Module.finrank Real Tᗮ + 1
  obtain ⟨v0, hv0⟩ := hsne
  have hR : 0 ≤ R := (norm_nonneg (v0 - e p)).trans
    (hsize v0 (subset_convexHull Real _ hv0))
  obtain ⟨hdist, _⟩ := local_graph_distance_comparison e p g rho R epsilon hR hRrho
    hgs hg0 hgproj hglip hgcover
  have hAgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real Tᗮ →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖ := by
    intro t hts htc x hx
    have h1 := hgap t hts htc x hx
    have h2 := hdist x (hsize x (convexHull_mono hts hx))
    change a ≤ ‖normalAffineConstraint T (e p) x‖
    linarith
  have htsize (t : Finset E) (hts : t ⊆ s) :
      ∀ x ∈ convexHull Real (t : Set E), ‖x - e p‖ ≤ R :=
    fun x hx => hsize x (convexHull_mono hts hx)
  have htcontract (t : Finset E) (hts : t ⊆ s) :
      (epsilon : Real) * (diam (t : Set E) / a) < 1 :=
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (diam_mono hts s.finite_toSet.isBounded) ha.le)
      epsilon.coe_nonneg).trans_lt hcontract
  have hlocal (t : Finset E) (hts : t ⊆ s) (htne : t.Nonempty) :=
    local_graph_section_incidence e he p g rho R a epsilon hgs hg0 hgproj hglip hgcover
      t htne ha hRrho (htsize t hts)
      (fun r hr => hgap r (hr.trans hts)) hsmall (htcontract t hts)
  have hmeetiff (t : Finset E) (hts : t ⊆ s) (htc : t.card = k) :
      (∃ x ∈ convexHull Real (t : Set E), x ∈ Set.range e) ↔
        ∃ x ∈ convexHull Real (t : Set E), x ∈ P := by
    have htne : t.Nonempty := Finset.card_pos.mp (by dsimp [k] at htc; omega)
    have h := (hlocal t hts htne).1
    constructor
    · rintro ⟨x, hx, q, rfl⟩
      exact h.mp ⟨q, hx⟩
    · intro hzero
      obtain ⟨q, hq⟩ := h.mpr hzero
      exact ⟨e q, hq, Set.mem_range_self q⟩
  have hfamilies : minimalSectionFaces (Set.range e) k s = minimalSectionFaces P k s := by
    ext t
    rw [mem_minimalSectionFaces, mem_minimalSectionFaces]
    constructor
    · rintro ⟨hts, htc, htm⟩
      exact ⟨hts, htc, (hmeetiff t hts htc).mp htm⟩
    · rintro ⟨hts, htc, htm⟩
      exact ⟨hts, htc, (hmeetiff t hts htc).mpr htm⟩
  have hpoints (t : Finset E) (ht : t ∈ minimalSectionFaces (Set.range e) k s) :
      ‖sectionFacePoint (Set.range e) t - sectionFacePoint P t‖ ≤
        (diam (t : Set E) / a) * ((epsilon : Real) * R) := by
    obtain ⟨hts, htc, htm⟩ := (mem_minimalSectionFaces (Set.range e) k s t).mp ht
    have htp := (hmeetiff t hts htc).mp htm
    obtain ⟨hx0, hAx0⟩ := sectionFacePoint_mem P t htp
    obtain ⟨hxM, hxMS⟩ := sectionFacePoint_mem (Set.range e) t htm
    obtain ⟨qM, hqM⟩ := hxMS
    have hqMhull : e qM ∈ convexHull Real (t : Set E) := hqM.symm ▸ hxM
    obtain ⟨q, hq, herr, huniq⟩ := exists_unique_local_graph_section e he p g rho R a epsilon
      hgs hg0 hgproj hglip hgcover ha hRrho A t rfl htc
      (fun r hr => hAgap r (hr.trans hts)) (sectionFacePoint P t) hx0 hAx0
      (htsize t hts) hsmall.le (htcontract t hts)
    have hqMeq : qM = q := huniq qM hqMhull
      (local_graph_normal_equation e p g hgproj qM (hgcover qM (by
        simpa only [dist_eq_norm] using (htsize t hts (e qM) hqMhull).trans_lt hRrho)))
    rw [← hqM, hqMeq]
    exact herr
  have hincP : ∀ v ∈ s, ∃ t : Finset E, t ⊆ s ∧ v ∈ t ∧ t.card = k ∧
      ∃ x ∈ convexHull Real (t : Set E), x ∈ P := by
    intro v hv
    obtain ⟨t, hts, hvt, htc, x0, hx0, hAx0, _⟩ :=
      (hlocal s (Finset.Subset.refl s) ⟨v0, hv0⟩).2 v hv hmeet
    exact ⟨t, hts, hvt, htc, x0, hx0, hAx0⟩
  have hFne : (minimalSectionFaces (Set.range e) k s).Nonempty := by
    obtain ⟨t, hts, hvt, htc, htp⟩ := hincP v0 hv0
    exact ⟨t, (mem_minimalSectionFaces (Set.range e) k s t).mpr
      ⟨hts, htc, (hmeetiff t hts htc).mpr htp⟩⟩
  have hcenters : ‖finiteSectionCenter (Set.range e) k s - finiteSectionCenter P k s‖ ≤
      (D / a) * ((epsilon : Real) * R) := by
    unfold finiteSectionCenter
    rw [← hfamilies]
    apply norm_centerMass_sub_le _ hFne
    intro t ht
    have hts := ((mem_minimalSectionFaces (Set.range e) k s t).mp ht).1
    have htdiam : diam (t : Set E) ≤ D :=
      (diam_mono (show (t : Set E) ⊆ convexHull Real (s : Set E) from
        fun x hx => subset_convexHull Real _ (hts hx))
          (s.finite_toSet.isCompact_convexHull Real).isBounded).trans hdiam
    exact (hpoints t ht).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right htdiam ha.le) (mul_nonneg epsilon.coe_nonneg hR))
  have hPne : P.Nonempty := by
    refine ⟨e p, ?_⟩
    change Tᗮ.orthogonalProjectionOnto (e p - e p) = 0
    simp
  have hPgap : ∀ t : Finset E, t ⊆ s → t.card < k →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ infDist x P := by
    intro t hts htc x hx
    apply (le_infDist hPne).mpr
    intro y hy
    have hyzero : A y = 0 := hy
    calc
      a ≤ ‖A x‖ := hAgap t hts (by dsimp [k] at htc; omega) x hx
      _ = ‖A x - A y‖ := by rw [hyzero, sub_zero]
      _ ≤ dist x y := by
        change ‖Tᗮ.orthogonalProjectionOnto (x - e p) -
          Tᗮ.orthogonalProjectionOnto (y - e p)‖ ≤ dist x y
        rw [← map_sub, sub_sub_sub_cancel_right, dist_eq_norm]
        exact Tᗮ.norm_orthogonalProjectionOnto_apply_le (x - y)
  obtain ⟨w, hw, hsum, hpoint, hbound⟩ := finiteSectionCenter_coordinates P k
    (by dsimp [k]; omega) s ⟨v0, hv0⟩ a D ha hD hdiam hPgap hincP
  exact ⟨hfamilies, hpoints, hcenters, w, hw, hsum, hpoint, hbound⟩

end PoincareConjecture.Proofs.M02.Topology
