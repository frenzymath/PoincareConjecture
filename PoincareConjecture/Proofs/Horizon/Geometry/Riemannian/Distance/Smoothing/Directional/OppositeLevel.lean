import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.ClosedSet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient.LevelDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Oscillation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

private theorem opposite_level_numerics {s δ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16) :
    0 < 1 - 2 * δ ^ 2 ∧ 9 / 10 ≤ 1 - 2 * δ ^ 2 ∧
      0 < δ * s / 8 ∧ δ * s / 8 ≤ s / 4 ∧
      16 / (9 * s) + 3 * s / 4 + δ ^ 2 ≤ 3 / s ∧
      (7 * δ ^ 2 * s) / (δ * s / 8) +
        (4 / s) * (δ * s / 8) / 2 ≤ 64 * δ := by
  have hd2 : δ ^ 2 ≤ 1 / 256 := by nlinarith
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hd2s : δ ^ 2 * s ≤ 1 / 256 := by
    exact (mul_le_mul_of_nonneg_left hs1 (sq_nonneg δ)).trans (by simpa using hd2)
  refine ⟨by nlinarith, by nlinarith, by positivity, by nlinarith, ?_, ?_⟩
  · apply (mul_le_mul_iff_right₀ hs).mp
    have hleft : s * (16 / (9 * s) + 3 * s / 4 + δ ^ 2) =
        16 / 9 + 3 * s ^ 2 / 4 + δ ^ 2 * s := by field_simp
    have hright : s * (3 / s) = 3 := by field_simp
    rw [hleft, hright]
    nlinarith
  · have heq : (7 * δ ^ 2 * s) / (δ * s / 8) +
        (4 / s) * (δ * s / 8) / 2 = 56 * δ + δ / 4 := by
      field_simp
      ring
    rw [heq]
    linarith

private theorem upper_level_distance_control
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {T : Set M} (hT : IsCompact T) {t s δ : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hc0 : 0 < 1 - 2 * δ ^ 2) (hc9 : 9 / 10 ≤ 1 - 2 * δ ^ 2)
    (hgap : ∀ x ∈ T, s ≤ t - f x ∧ t - f x ≤ 2 * s) :
    letI := g.toMetricSpace
    (∀ x ∈ T, ∀ y ∈ Metric.closedBall x (4 * s),
      1 - δ ^ 2 ≤ g.tangentNorm y (D.gradient f y) ∧
        g.tangentNorm y (D.gradient f y) ≤ 1) →
    ∀ y ∈ Metric.cthickening (s / 4) T,
      (f ⁻¹' {t}).Nonempty ∧
      t - f y ≤ Metric.infDist y (f ⁻¹' {t}) ∧
      3 * s / 4 ≤ Metric.infDist y (f ⁻¹' {t}) ∧
      Metric.infDist y (f ⁻¹' {t}) ≤ 3 * s ∧
      Metric.infDist y (f ⁻¹' {t}) - (t - f y) ≤ 5 * δ ^ 2 * s := by
  let := g.toMetricSpace
  intro hgrad y hy
  have hy' : y ∈ ⋃ a ∈ T, Metric.closedBall a (s / 4) := by
    rw [← hT.cthickening_eq_biUnion_closedBall (by positivity : 0 ≤ s / 4)]
    exact hy
  obtain ⟨a, ha, hay⟩ := mem_iUnion₂.mp hy'
  have hay' : dist y a ≤ s / 4 := hay
  have hdistay : (g.edist a y).toReal ≤ s / 4 := by
    change dist a y ≤ s / 4
    simpa only [dist_comm] using hay'
  have hvalue := g.abs_sub_le_mul_toReal_edist_of_gradient_bound_closedBall hc hf a y
    (L := 1) (by
      intro z hz
      apply (hgrad a ha z ?_).2
      apply Metric.mem_closedBall.mpr
      have hz' : dist z a ≤ (g.edist a y).toReal := hz
      linarith)
  simp only [NNReal.coe_one, one_mul] at hvalue
  have habs : |f y - f a| ≤ s / 4 := hvalue.trans hdistay
  have hgapy : 3 * s / 4 ≤ t - f y ∧ t - f y ≤ 9 * s / 4 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    obtain ⟨ha1, ha2⟩ := hgap a ha
    constructor <;> linarith
  have hquot : (t - f y) / (1 - 2 * δ ^ 2) ≤ 5 * s / 2 := by
    apply (div_le_iff₀ hc0).mpr
    nlinarith
  obtain ⟨hne, hupper⟩ := g.infDist_level_le_of_gradient_lower_bound hc hf y (t := t) hc0
    (by linarith [hgapy.1]) (by
      intro z hz _
      have hz' : dist z y < (t - f y) / (1 - 2 * δ ^ 2) := hz
      have hza : dist z a ≤ 4 * s := by
        have htri := dist_triangle z y a
        linarith
      have hlow := (hgrad a ha z (Metric.mem_closedBall.mpr hza)).1
      change 1 - 2 * δ ^ 2 < g.tangentNorm z (D.gradient f z)
      nlinarith [sq_pos_of_pos hδ])
  have hdmax := hupper.trans hquot
  have hlower := g.sub_le_mul_infDist_level_of_gradient_upper_bound hc hf hne y
    (L := 1) (by
      intro z hz
      have hz' : dist z y ≤ Metric.infDist y (f ⁻¹' {t}) := hz
      apply (hgrad a ha z (Metric.mem_closedBall.mpr ?_)).2
      have htri := dist_triangle z y a
      linarith)
  simp only [NNReal.coe_one, one_mul] at hlower
  have hmul := (le_div_iff₀ hc0).mp hupper
  have hdefect := mul_le_mul_of_nonneg_left hdmax (show 0 ≤ 2 * δ ^ 2 by positivity)
  refine ⟨hne, hlower, hgapy.1.trans hlower, by linarith, ?_⟩
  nlinarith

theorem exists_near_opposite_smoothing_of_upper_level
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      -1 ≤ D.sectionalCurvature x v w)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {T : Set M} (hT : IsCompact T) {t s δ H : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16)
    (hH : 0 ≤ H) (hHs : H * s ≤ 1)
    (hgap : ∀ x ∈ T, s ≤ t - f x ∧ t - f x ≤ 2 * s) :
    letI := g.toMetricSpace
    (∀ x ∈ T, ∀ y ∈ Metric.closedBall x (4 * s),
      1 - δ ^ 2 ≤ g.tangentNorm y (D.gradient f y) ∧
      g.tangentNorm y (D.gradient f y) ≤ 1 ∧
      ∀ v : TangentSpace (𝓡 n) y, D.hessian f y v v ≤ H * g.inner y v v) →
    ∃ rho : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      ∀ x ∈ T,
        |rho x - Metric.infDist x (f ⁻¹' {t})| ≤ δ ^ 2 * s ∧
        g.tangentNorm x (D.gradient rho x) ≤ 1 + δ ^ 2 ∧
        (∀ v : TangentSpace (𝓡 n) x,
          D.hessian rho x v v ≤ (3 / s) * g.inner x v v) ∧
        g.tangentNorm x (D.gradient f x + D.gradient rho x) ≤ 64 * δ := by
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hc
  intro hbuffer
  rcases eq_empty_or_nonempty T with hTempty | hTne
  · refine ⟨fun _ => 0, contMDiff_const, ?_⟩
    simp only [hTempty, mem_empty_iff_false, false_implies, implies_true]
  obtain ⟨hc0, hc9, hR, hRsmall, hcoef, hnum⟩ :=
    opposite_level_numerics hs hs1 hδ hδ16
  let B := Metric.cthickening (s / 4) T
  have hTB : T ⊆ B := Metric.self_subset_cthickening T
  have hB : IsCompact B := hT.cthickening
  have hcontrol := upper_level_distance_control g D hc hf hT hs hδ hc0 hc9 hgap
    (fun x hx y hy => ⟨(hbuffer x hx y hy).1, (hbuffer x hx y hy).2.1⟩)
  obtain ⟨x0, hx0⟩ := hTne
  have hSne : (f ⁻¹' {t}).Nonempty := (hcontrol x0 (hTB hx0)).1
  have hclosed : IsClosed (f ⁻¹' {t}) := isClosed_singleton.preimage hf.continuous
  obtain ⟨rho, hrho, herr, hgrad, hhess⟩ :=
    g.exists_infDist_smoothing_on_compact D hc (by norm_num : (0 : ℝ) ≤ 1)
      hsec (f ⁻¹' {t}) hclosed hSne hB (by positivity : 0 < 3 * s / 4)
      (by positivity : 0 < δ ^ 2 * s) (by positivity : 0 < δ ^ 2)
      (fun y hy => (hcontrol y hy).2.2.1) (fun y hy => (hcontrol y hy).2.2.2.1)
  have hcoefficient : 4 / (3 * (3 * s / 4)) + 1 * (3 * s) / 4 + δ ^ 2 ≤ 3 / s := by
    have heq : 4 / (3 * (3 * s / 4)) + 1 * (3 * s) / 4 + δ ^ 2 =
        16 / (9 * s) + 3 * s / 4 + δ ^ 2 := by ring
    rw [heq]
    exact hcoef
  have hinner (y : M) (v : TangentSpace (𝓡 n) y) : 0 ≤ g.inner y v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos y v hv).le
  have hhess3 (y : M) (hy : y ∈ B) (v : TangentSpace (𝓡 n) y) :
      D.hessian rho y v v ≤ (3 / s) * g.inner y v v :=
    (hhess y hy v).trans (mul_le_mul_of_nonneg_right hcoefficient (hinner y v))
  have hsum_lower (y : M) (hy : y ∈ B) :
      t - δ ^ 2 * s ≤ f y + rho y := by
    have hlevel := (hcontrol y hy).2.1
    have he := (abs_le.mp (herr y hy)).1
    linarith
  have hsum_upper (y : M) (hy : y ∈ B) :
      f y + rho y ≤ t + 6 * δ ^ 2 * s := by
    have hlevel := (hcontrol y hy).2.2.2.2
    have he := (abs_le.mp (herr y hy)).2
    linarith
  have hHbound : H ≤ 1 / s := (le_div_iff₀ hs).mpr hHs
  have hHtotal : 0 ≤ 4 / s :=
    hH.trans (hHbound.trans (div_le_div_of_nonneg_right (by norm_num) hs.le))
  refine ⟨rho, hrho, ?_⟩
  intro x hx
  refine ⟨herr x (hTB hx), hgrad x (hTB hx), hhess3 x (hTB hx), ?_⟩
  have hballB (y : M) (hxy : g.edist x y ≤ ENNReal.ofReal (δ * s / 8)) :
      y ∈ B ∧ y ∈ Metric.closedBall x (4 * s) := by
    have hdist : dist y x ≤ δ * s / 8 := by
      rw [dist_comm]
      change (g.edist x y).toReal ≤ δ * s / 8
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hxy).trans_eq
        (ENNReal.toReal_ofReal hR.le)
    refine ⟨Metric.closedBall_subset_cthickening hx (s / 4)
      (Metric.mem_closedBall.mpr (hdist.trans hRsmall)), ?_⟩
    apply Metric.mem_closedBall.mpr
    linarith
  have hosc := D.gradient_norm_le_of_lower_oscillation_hessian (f := fun y => f y + rho y) hc x hR
    (by positivity : 0 ≤ 7 * δ ^ 2 * s) hHtotal
    isOpen_univ (fun _ _ => mem_univ _) (hf.add hrho).contMDiffOn
    (by
      intro y hy
      have hlow := hsum_lower y (hballB y hy).1
      have hhigh := hsum_upper x (hTB hx)
      linarith)
    (by
      intro y hy v
      rw [D.hessian_add hf hrho]
      have hfH := (hbuffer x hx y (hballB y hy).2).2.2 v
      have hrhoH := hhess3 y (hballB y hy).1 v
      have hbound := mul_le_mul_of_nonneg_right hHbound (hinner y v)
      calc
        _ ≤ (1 / s) * g.inner y v v + (3 / s) * g.inner y v v :=
          add_le_add (hfH.trans hbound) hrhoH
        _ = (4 / s) * g.inner y v v := by ring)
  rw [D.gradient_add ((hf x).mdifferentiableAt (by simp))
    ((hrho x).mdifferentiableAt (by simp))] at hosc
  exact hosc.trans hnum

end PoincareConjecture.RiemannianMetric
