import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Step
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Intervals
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Diffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RiemannianMetric

theorem eq_of_inner_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g h : RiemannianMetric n M} (heq : ∀ x v w, g.inner x v w = h.inner x v w) : g = h := by
  have hi : g.inner = h.inner := by funext x; ext v w; exact heq x v w
  cases g
  cases h
  cases hi
  rfl

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

noncomputable def chosenWindowExtension (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) (Q : S.FiniteWindowLimit P j) :
    S.WindowExtension P j Q := Classical.choice (S.exists_windowExtension P j Q)

noncomputable def nestedWindowLimit (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) : ∀ j, S.FiniteWindowLimit P j
  | 0 => Classical.choice (S.finiteCompactness P 0)
  | j + 1 => (S.chosenWindowExtension P j (S.nestedWindowLimit P j)).next

noncomputable def nextWindowEquiv (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) :
    Diffeomorph (𝓡 n) (𝓡 n) (S.nestedWindowLimit P j).geometric_limit.limitCarrier.carrier
      (S.nestedWindowLimit P (j + 1)).geometric_limit.limitCarrier.carrier ∞ :=
  (S.chosenWindowExtension P j (S.nestedWindowLimit P j)).equiv

noncomputable def initialWindowIdentification (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) : ∀ j,
    Diffeomorph (𝓡 n) (𝓡 n) (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier
      (S.nestedWindowLimit P j).geometric_limit.limitCarrier.carrier ∞
  | 0 => Diffeomorph.refl _ _ ∞
  | j + 1 => (S.initialWindowIdentification P j).trans (S.nextWindowEquiv P j)

theorem initialWindowIdentification_base (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) :
    S.initialWindowIdentification P j (S.nestedWindowLimit P 0).geometric_limit.limitFlow.base =
      (S.nestedWindowLimit P j).geometric_limit.limitFlow.base := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change S.nextWindowEquiv P j (S.initialWindowIdentification P j
      (S.nestedWindowLimit P 0).geometric_limit.limitFlow.base) = _
    rw [ih]
    exact (S.chosenWindowExtension P j (S.nestedWindowLimit P j)).base_eq

noncomputable def identifiedWindowFlow (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) :
    RicciFlow n (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier
      (Ioo (compactnessLower j + 1) (compactnessUpper j + 1)) :=
  (S.nestedWindowLimit P j).geometric_limit.limitFlow.flow.pullbackDiffeomorph
    (S.initialWindowIdentification P j)

theorem identifiedWindowFlow_succ_metric (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) (t : ℝ)
    (ht : t ∈ Ioo (compactnessLower j + 1) (compactnessUpper j + 1))
    (ht' : t ∈ Ioo (compactnessLower (j + 1) + 1) (compactnessUpper (j + 1) + 1)) :
    (S.identifiedWindowFlow P (j + 1)).metric t = (S.identifiedWindowFlow P j).metric t := by
  apply RiemannianMetric.eq_of_inner_eq
  intro x v w
  simp only [identifiedWindowFlow, RicciFlow.pullbackDiffeomorph_inner]
  have hd := mfderiv_comp x
    ((S.nextWindowEquiv P j).contMDiff.mdifferentiable (by simp)
      (S.initialWindowIdentification P j x))
    ((S.initialWindowIdentification P j).contMDiff.mdifferentiable (by simp) x)
  have hm := (S.chosenWindowExtension P j (S.nestedWindowLimit P j)).metric_inner_eq t ht ht'
    (S.initialWindowIdentification P j x)
    (mfderiv (𝓡 n) (𝓡 n) (S.initialWindowIdentification P j) x v)
    (mfderiv (𝓡 n) (𝓡 n) (S.initialWindowIdentification P j) x w)
  change ((S.nestedWindowLimit P (j + 1)).geometric_limit.limitFlow.metricAt t).inner
      ((S.nextWindowEquiv P j ∘ S.initialWindowIdentification P j) x)
      (mfderiv (𝓡 n) (𝓡 n) (S.nextWindowEquiv P j ∘ S.initialWindowIdentification P j) x v)
      (mfderiv (𝓡 n) (𝓡 n) (S.nextWindowEquiv P j ∘ S.initialWindowIdentification P j) x w) = _
  rw [hd]
  exact hm

theorem identifiedWindowFlow_metric_of_le (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) {i j : ℕ} (hij : i ≤ j)
    {t : ℝ} (ht : t ∈ shiftedCompactnessWindow i) :
    (S.identifiedWindowFlow P j).metric t = (S.identifiedWindowFlow P i).metric t := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    have htj := shiftedCompactnessWindow_mono hij ht
    exact (S.identifiedWindowFlow_succ_metric P j t htj
      (shiftedCompactnessWindow_mono (Nat.le_succ j) htj)).trans ih

theorem identifiedWindowFlow_metric_compatible (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (i j : ℕ)
    {t : ℝ} (hti : t ∈ shiftedCompactnessWindow i) (htj : t ∈ shiftedCompactnessWindow j) :
    (S.identifiedWindowFlow P i).metric t = (S.identifiedWindowFlow P j).metric t :=
  (S.identifiedWindowFlow_metric_of_le P (le_max_left i j) hti).symm.trans
    (S.identifiedWindowFlow_metric_of_le P (le_max_right i j) htj)

theorem identifiedWindowFlow_complete (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ)
    {t : ℝ} (ht : t ∈ shiftedCompactnessWindow j) :
    MetricComplete ((S.identifiedWindowFlow P j).metric t) := by
  exact ((S.nestedWindowLimit P j).geometric_limit.limitFlow.flow.pullbackDiffeomorph_metricComplete_iff
    (S.initialWindowIdentification P j) t).2 ((S.nestedWindowLimit P j).complete_interior t ht)

end PoincareConjecture.AncientRescalingSequence
