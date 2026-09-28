import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RayApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.MetricComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_uniform_sublinear_ray_approximation
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : M, L ≤ (g.edist p x).toReal →
      ∃ ray : ℝ → M, ray 0 = p ∧
        (∀ s, 0 ≤ s → ∀ t, 0 ≤ t →
          g.edist (ray s) (ray t) = ENNReal.ofReal |s - t|) ∧
        (g.edist x (ray ((g.edist p x).toReal))).toReal / (g.edist p x).toReal < ε := by
  classical
  by_contra! hnot
  have hbad : ∀ k : ℕ, ∃ x : M, (k : ℝ) + 1 ≤ (g.edist p x).toReal ∧
      ∀ ray : ℝ → M, ray 0 = p →
        (∀ s, 0 ≤ s → ∀ t, 0 ≤ t →
          g.edist (ray s) (ray t) = ENNReal.ofReal |s - t|) →
        ε ≤ (g.edist x (ray ((g.edist p x).toReal))).toReal / (g.edist p x).toReal := by
    intro k
    exact hnot ((k : ℝ) + 1) (by positivity)
  choose x hfar hbad using hbad
  have hescape : Tendsto (fun k => (g.edist p (x k)).toReal) atTop atTop :=
    tendsto_atTop_mono (fun k => (show (k : ℝ) ≤ (k : ℝ) + 1 by linarith).trans (hfar k))
      tendsto_natCast_atTop_atTop
  obtain ⟨ray, hray0, hray, σ, _, hlim⟩ :=
    g.exists_minimizing_ray_approximating_escaping_sequence hc p x hescape
      (fun a ha α β hα0 hβ0 hα hβ =>
        g.toponogov_equal_radius_of_edist_segments D hc hsec ha hα0 hβ0 hα hβ)
  obtain ⟨k, hk⟩ := (hlim.eventually_lt_const hε).exists
  exact (not_lt_of_ge (hbad (σ k) ray hray0 hray)) hk

theorem exists_uniform_ray_approximation_on_annuli
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M)
    {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ r : ℝ, L ≤ r → ∀ x : M,
      a * r ≤ (g.edist p x).toReal → (g.edist p x).toReal ≤ b * r →
      ∃ ray : ℝ → M, ray 0 = p ∧
        (∀ s, 0 ≤ s → ∀ t, 0 ≤ t →
          g.edist (ray s) (ray t) = ENNReal.ofReal |s - t|) ∧
        (g.edist x (ray ((g.edist p x).toReal))).toReal / r < ε := by
  obtain ⟨L, hL, happrox⟩ := g.exists_uniform_sublinear_ray_approximation D hc hsec p
    (div_pos hε hb)
  refine ⟨max (L / a) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro r hr x hlo hhi
  have hrpos : 0 < r := zero_lt_one.trans_le ((le_max_right _ _).trans hr)
  have hLr : L ≤ a * r := by
    have hh : L / a ≤ r := (le_max_left _ _).trans hr
    exact (div_le_iff₀ ha).mp hh |>.trans_eq (mul_comm r a)
  have hdx : 0 < (g.edist p x).toReal := (mul_pos ha hrpos).trans_le hlo
  obtain ⟨ray, hray0, hray, herror⟩ := happrox x (hLr.trans hlo)
  refine ⟨ray, hray0, hray, (div_lt_iff₀ hrpos).mpr ?_⟩
  calc
    _ < (ε / b) * (g.edist p x).toReal := (div_lt_iff₀ hdx).mp herror
    _ ≤ (ε / b) * (b * r) := mul_le_mul_of_nonneg_left hhi (div_pos hε hb).le
    _ = ε * r := by field_simp

end PoincareConjecture.RiemannianMetric
