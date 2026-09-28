import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.Depth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.ClosedSet

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_smooth_exhaustion_approx_on_compact
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {T : Set M} (hT : IsCompact T) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    letI := g.toMetricSpace
    ∃ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧ u p ≤ ε ∧
      (∀ x ∈ T, u x ≤ busemannExhaustion p x + ε) ∧
      (∀ x ∈ T, 0 < busemannExhaustion p x →
        |u x - busemannExhaustion p x| ≤ ε) ∧
      (∀ x ∈ T, g.tangentNorm x (D.gradient u x) ≤ 1 + η) ∧
      ∀ x ∈ T, ∀ v : TangentSpace (𝓡 n) x,
        -η * g.inner x v v ≤ D.hessian u x v v := by
  letI := g.toMetricSpace
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  letI : ProperSpace M := g.properSpace_of_complete hc hdist
  have hsegments := g.hasMinimizingSegments_of_complete hc hdist
  let T' := insert p T
  have hT' : IsCompact T' := hT.insert p
  obtain ⟨B, hB⟩ := hT'.bddAbove_image (lipschitz_busemannExhaustion p).continuous.continuousOn
  let r := 8 / (3 * η)
  have hr : 0 < r := by dsimp [r]; positivity
  let c := max B 0 + r + 1
  have hcpos : 0 < c := by dsimp [c]; linarith [le_max_right B 0]
  let C := horoballIntersection p c
  have hCcompact : IsCompact C :=
    g.isCompact_horoballIntersection_of_nonnegativeSectional D hc hsec hdist p hcpos.le
  have hpC : p ∈ C := closedBall_subset_horoballIntersection p c
    (by simpa only [mem_closedBall, dist_self] using hcpos.le)
  have hCclosed : IsClosed C := isClosed_horoballIntersection p c
  have hcompl : Cᶜ.Nonempty := nonempty_compl.mpr hCcompact.ne_univ
  have hfront : (frontier C).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨p, hpC⟩, hCcompact.ne_univ⟩
  have hfupper (x : M) (hx : x ∈ T') : busemannExhaustion p x ≤ max B 0 :=
    (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hmem (x : M) (hx : x ∈ T') : x ∈ C :=
    (busemannExhaustion_le_iff hcpos.le).mp (by
      have := hfupper x hx
      dsimp [c]
      linarith)
  have hdepth (x : M) (hx : x ∈ T') :
      c - busemannExhaustion p x ≤ infDist x (frontier C) := by
    rw [g.infDist_frontier_eq_infDist_compl hc hCclosed hfront hcompl (hmem x hx)]
    apply le_infDist_compl_of_busemann hcompl
    intro ray hray hray0
    have := neg_busemann_le_exhaustion hray hray0 x
    linarith
  have hlower (x : M) (hx : x ∈ T') : r ≤ infDist x (frontier C) := by
    have h := hdepth x hx
    have hf := hfupper x hx
    dsimp [c] at h
    linarith
  obtain ⟨R, hR⟩ := hT'.bddAbove_image (continuous_infDist_pt (frontier C)).continuousOn
  have hsec0 (x : M) (v w : TangentSpace (𝓡 n) x) :
      -(0 : ℝ) ≤ D.sectionalCurvature x v w := by
    rw [neg_zero]
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    apply div_nonneg (hsec x v w)
    change 0 ≤ inner ℝ v v * inner ℝ w w - (inner ℝ v w) ^ 2
    simpa only [pow_two] using sub_nonneg.mpr (real_inner_mul_inner_self_le v w)
  obtain ⟨rho, hrho, herr, hgrad, hhess⟩ :=
    g.exists_infDist_smoothing_on_compact D hc (K := 0) le_rfl hsec0
      (frontier C) isClosed_frontier hfront hT' hr hε (half_pos hη)
      hlower (fun x hx => hR (mem_image_of_mem _ hx))
  let u : M → ℝ := fun x => c + (-rho x)
  have hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u := contMDiff_const.add hrho.neg
  have huupper (x : M) (hx : x ∈ T') : u x ≤ busemannExhaustion p x + ε := by
    have he := (abs_le.mp (herr x hx)).1
    have hd := hdepth x hx
    dsimp [u]
    linarith
  refine ⟨u, hu, ?_, fun x hx => huupper x (mem_insert_of_mem p hx), ?_, ?_, ?_⟩
  · simpa only [busemannExhaustion_self, zero_add] using huupper p (mem_insert p T)
  · intro x hx hpos
    have hd : infDist x (frontier C) = c - busemannExhaustion p x := by
      rw [g.infDist_frontier_eq_infDist_compl hc hCclosed hfront hcompl
        (hmem x (mem_insert_of_mem p hx))]
      exact infDist_compl_horoball_eq_sub_exhaustion hsegments hcompl
        ((busemannExhaustion_le_iff hcpos.le).mpr (hmem x (mem_insert_of_mem p hx))) hpos
    have he := herr x (mem_insert_of_mem p hx)
    rw [hd] at he
    have heq : u x - busemannExhaustion p x = -(rho x - (c - busemannExhaustion p x)) := by
      dsimp [u]; ring
    rwa [heq, abs_neg]
  · intro x hx
    have he : D.gradient u x = -(D.gradient rho x) := by
      have hd : mvfderiv (𝓡 n) (fun y => -rho y) x = -mvfderiv (𝓡 n) rho x := mvfderiv_neg
      rw [show u = (fun y => c + (-rho y)) from rfl,
        D.gradient_const_add_at ((hrho x).neg.mdifferentiableAt (by simp)) c]
      simp only [LeviCivitaData.gradient, hd, map_neg]
    rw [he]
    have hn : g.tangentNorm x (-(D.gradient rho x)) = g.tangentNorm x (D.gradient rho x) := by
      simp only [RiemannianMetric.tangentNorm, map_neg, neg_apply, neg_neg]
    rw [hn]
    exact (hgrad x (mem_insert_of_mem p hx)).trans (by linarith)
  · intro x hx v
    have he : D.hessian u x v v = -D.hessian rho x v v := by
      rw [show u = (fun y => c + (-rho y)) from rfl,
        D.hessian_const_add_at (hrho x).neg c]
      simpa only [neg_one_mul] using D.hessian_const_mul (-1) rho x v v
    have hconstant : 4 / (3 * r) + 0 * R / 4 + η / 2 = η := by
      dsimp [r]
      field_simp
      <;> ring
    have hb := hhess x (mem_insert_of_mem p hx) v
    rw [hconstant] at hb
    rw [he, neg_mul]
    exact neg_le_neg hb

end PoincareConjecture.RiemannianMetric
