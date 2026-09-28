import PoincareConjecture.Proofs.M28.Generalized.IndexedSourceGeometry
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.EventualNormalCovers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem CounterexampleSourceGeometry.exists_normalized_source_partial_metric_limit
    {epsilon C A : ℝ}
    {E : ∀ k : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((k : ℝ) + 1) ((k : ℝ) + 1)}
    {H : CounterexampleNeckFamily E} (G : CounterexampleSourceGeometry H)
    (v : ℕ → ℝ)
    (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper) :
    Nonempty (PartialPointedMetricConvergence
      (fun k => (H.normalizedSourceFlow v hv k).metric 0)
      (fun k => (H.normalizedSourceNeck v hv k).center)
      (epsilon⁻¹ / 16)) := by
  classical
  let B : ℝ := epsilon⁻¹ / 16
  have hepsilon : 0 < epsilon := (H.selectedOriginalNeck v hv 0).epsilon_pos
  have hB : 0 < B := div_pos (inv_pos.mpr hepsilon) (by norm_num)
  let r : ℕ → ℝ := fun j => B * ((j : ℝ) + 1) / ((j : ℝ) + 2)
  have hr (j : ℕ) : 0 < r j := by
    dsimp only [r]
    exact div_pos (mul_pos hB (by positivity)) (by positivity)
  have hrB (j : ℕ) : r j < B := by
    dsimp only [r]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 2)).2
    nlinarith only [hB]
  have hcofinal : ∀ b : ℝ, b < B → ∃ j, b < r j := by
    intro b hb
    have hgap : 0 < B - b := sub_pos.mpr hb
    obtain ⟨j, hj⟩ := exists_nat_gt (B / (B - b))
    have hj' : B / (B - b) < (j : ℝ) + 2 := by linarith
    have hmul : B < ((j : ℝ) + 2) * (B - b) := (div_lt_iff₀ hgap).mp hj'
    refine ⟨j, ?_⟩
    dsimp only [r]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 2)).2
    nlinarith only [hmul]
  choose R ρ n hρ hρR hRmargin _hRsmall hcover using
    fun j => G.normal_covers (r j) (hr j) (hrB j)
  have hmargin (j : ℕ) : r j + R j < B := by
    have h1 := hRmargin j
    have h2 := hrB j
    change R j < (B - r j) / 8 at h1
    linarith
  let M : ℕ → Type u := fun k => H.selectedSourceOpen v hv k
  let : ∀ k, MetricSpace (M k) := fun k =>
    (H.normalizedSourceMetricSpace v hv k).replaceTopology
      (H.normalizedSourceMetricSpace_topology v hv k)
  let : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k) := fun k =>
    TopologicalSpace.Opens.instChartedSpace (H.selectedSourceOpen v hv k)
  let : ∀ k, IsManifold (𝓡 3) ∞ (M k) := fun k => inferInstance
  let g : ∀ k, ℝ → RiemannianMetric 3 (M k) :=
    fun k _ => (H.normalizedSourceFlow v hv k).metric 0
  let D : ∀ k, LeviCivitaData (g k 0) :=
    fun k => (H.normalizedSourceFlow v hv k).connection 0
  let p : ∀ k, M k := fun k => (H.normalizedSourceNeck v hv k).center
  have hdist (k : ℕ) (x y : M k) : edist x y = (g k 0).edist x y :=
    H.normalizedSourceMetricSpace_edist v hv k x y
  have hcurv : ∀ j l, ∃ Cₗ : ℝ, 0 ≤ Cₗ ∧ ∀ᶠ k in atTop,
      ∀ x ∈ (g k 0).ball (p k) (r j + R j),
        (D k).curvatureDerivativeNorm l x ≤ Cₗ := by
    intro j l
    refine ⟨G.derivativeBound l, (G.derivativeBound_pos l).le,
      Filter.Eventually.of_forall ?_⟩
    intro k x hx
    apply G.derivative_bound v hv l k x
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (hmargin j).le)
  have hcovers : ∀ j, ∀ᶠ k in atTop,
      Nonempty (NormalChartCover (g k) (p k) (-1) 1
        (r j) (R j) (ρ j) (1 / 4) (9 / 4) (n j)) := by
    intro j
    exact Filter.Eventually.of_forall (fun k => hcover j v hv k)
  exact exists_partial_metric_limit_of_eventual_normal_covers (g := g) (p := p)
    D hr hρ (fun j => by have := hρR j; have := hρ j; linarith)
    (fun _ => by norm_num) (by constructor <;> norm_num) hdist hB
    hmargin hcofinal hcurv hcovers

theorem exists_counterexample_source_metric_limit_accuracy
    (P : RicciFlowCurvatureTheory.{u}) (T : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 256 : ℝ) ∧
      ∀ (epsilon C A : ℝ), 0 < epsilon → epsilon ≤ epsilon₀ → 0 < C →
        ∀ E : ∀ k : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((k : ℝ) + 1) ((k : ℝ) + 1),
          ∃ H : CounterexampleNeckFamily E, Nonempty (CounterexampleSourceGeometry H) ∧
            ∀ (v : ℕ → ℝ)
              (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper),
              Nonempty (PartialPointedMetricConvergence
                (fun k => (H.normalizedSourceFlow v hv k).metric 0)
                (fun k => (H.normalizedSourceNeck v hv k).center)
                (epsilon⁻¹ / 16)) := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hfamily⟩ :=
    exists_counterexample_source_family_accuracy P T
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro epsilon C A hepsilon hbound hC E
  obtain ⟨H, ⟨G⟩⟩ := hfamily epsilon C A hepsilon hbound hC E
  exact ⟨H, ⟨G⟩, fun v hv => G.exists_normalized_source_partial_metric_limit v hv⟩

end PoincareConjecture.M28
