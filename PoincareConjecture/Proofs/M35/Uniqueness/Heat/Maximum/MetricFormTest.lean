import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricTestBounds
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.NonlinearCompletion









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def metricEntropySupportedTests {K : Set V} (hK : IsCompact K)
    (g : RiemannianMetric n V) (η : V → ℝ) (hη : ContDiff ℝ ∞ η) (Q : ℝ)
    (f : Fin n → supportedTests K) : Fin n → supportedTests K := fun j =>
  nonlinearSupportedTest hK (metricEntropyTest g η Q (EuclideanSpace.single j 1))
    (metricEntropyTest_contDiff g hη Q (EuclideanSpace.single j 1))
    (metricEntropyTest_zero g η Q (EuclideanSpace.single j 1)) f

private theorem metric_entropy_component_limit {K : Set V} (hK : IsCompact K)
    (g : RiemannianMetric n V) (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (Q : ℝ)
    (u : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (f : ℕ → Fin n → supportedTests K)
    (hflim : Tendsto (fun k => vectorTestForm K (f k)) atTop (𝓝 u)) (j : Fin n) :
    ∃ v : dirichletForm K,
      Tendsto (fun k => intoDirichletForm K (metricEntropySupportedTests hK g η hη Q (f k) j))
        atTop (𝓝 v) ∧
      (dirichletInclusion K v : L2) =ᵐ[volume] fun x =>
        metricEntropyTest g η Q (EuclideanSpace.single j 1) (x, dirichletFieldValue K u x) := by
  let e : V := EuclideanSpace.single j 1
  refine (metricEntropyTest_jet_bounds g hη hc Q e).elim ?_
  intro C hC
  refine (nonlinearSupportedTest_graph_limit hK (metricEntropyTest g η Q e)
    (metricEntropyTest_contDiff g hη Q e) (metricEntropyTest_zero g η Q e)
    hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1 hC.2.2.2.2 u f hflim).elim ?_
  intro v hv
  refine ⟨v, hv.1, ?_⟩
  rw [hv.2]
  exact nonlinearFieldLp_coe _ _ _ hC.2.1 (dirichletFieldValue K u)



theorem exists_metric_entropy_form_test {K : Set V} (hK : IsCompact K)
    (g : RiemannianMetric n V) (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (Q : ℝ)
    (u : PiLp 2 (fun _ : Fin n => dirichletForm K)) :
    ∃ f : ℕ → Fin n → supportedTests K,
    ∃ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      Tendsto (fun k => vectorTestForm K (f k)) atTop (𝓝 u) ∧
      Tendsto (fun k => vectorTestForm K (metricEntropySupportedTests hK g η hη Q (f k)))
        atTop (𝓝 z) ∧
      ∀ j : Fin n, (dirichletInclusion K (z j) : L2) =ᵐ[volume]
        fun x => metricEntropyTest g η Q (EuclideanSpace.single j 1)
          (x, dirichletFieldValue K u x) := by
  have hu : u ∈ closure (Set.range (vectorTestForm (m := n) K)) := vectorTestForm_denseRange K u
  obtain ⟨s, hs, hslim⟩ := mem_closure_iff_seq_limit.mp hu
  choose f hf using hs
  have hflim : Tendsto (fun k => vectorTestForm K (f k)) atTop (𝓝 u) :=
    hslim.congr' (Eventually.of_forall fun k => (hf k).symm)
  choose z hzlim hzval using
    fun j => metric_entropy_component_limit hK g η hη hc Q u f hflim j
  refine ⟨f, WithLp.toLp 2 z, hflim, ?_, hzval⟩
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => dirichletForm K)).continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr hzlim)

end PoincareConjecture.M35.Uniqueness.Heat
