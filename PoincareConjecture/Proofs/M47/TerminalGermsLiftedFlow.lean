import PoincareConjecture.Proofs.M47.TerminalGermsDiffeomorphCharts
import PoincareConjecture.Proofs.M47.TerminalGermsPrecompactFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

theorem terminalGerms_lifted_precompact_flow
    {n : ℕ} {ι : Type*} {P : ι → Type*} {Q : Type u}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace Q] [T3Space Q]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ Q]
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow n (P i) (Icc (-tau i) 0))
    (q : ∀ i, P i → Q)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinv : ∀ i j t, t ∈ Icc (-tau i) 0 → t ∈ Icc (-tau j) 0 →
      ∀ (x : P i) (y : P j), q i x = q j y →
      ∀ (a b : TangentSpace (𝓡 n) x) (c d : TangentSpace (𝓡 n) y),
        mfderiv (𝓡 n) (𝓡 n) (q i) x a = mfderiv (𝓡 n) (𝓡 n) (q j) y c →
        mfderiv (𝓡 n) (𝓡 n) (q i) x b = mfderiv (𝓡 n) (𝓡 n) (q j) y d →
        ((F i).metric t).inner x a b = ((F j).metric t).inner y c d)
    (g0 : RiemannianMetric n Q) (hcomplete : MetricComplete g0)
    (hterminal : ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
      ((F i).metric 0).inner x a b = g0.inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{v} Q) :=
      Poincare.Manifold.uliftChartedSpace _ Q
    letI : IsManifold (𝓡 n) ∞ (ULift.{v} Q) :=
      Poincare.Manifold.uliftIsManifold (𝓡 n) Q
    let d := Poincare.Manifold.uliftDiffeomorph (𝓡 n) Q
    let gL := g0.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
    let qL : ∀ i, P i → ULift.{v} Q := fun i x => ULift.up (q i x)
    MetricComplete gL ∧
      (∀ x y : ULift.{v} Q, gL.edist x y = g0.edist x.down y.down) ∧
      ∀ V : Opens (ULift.{v} Q), (V : Set (ULift.{v} Q)).Nonempty →
        IsCompact (closure (V : Set (ULift.{v} Q))) →
        ∃ s : Finset ι, s.Nonempty ∧
          closure (V : Set (ULift.{v} Q)) ⊆ ⋃ i ∈ s, range (qL i) ∧
          ∃ delta : ℝ, 0 < delta ∧ (∀ i ∈ s, delta < tau i) ∧
            ∃ G : RicciFlow n V (Icc (-delta) 0),
              G.metric 0 = gL.pullbackOfLocalDiffeomorph Subtype.val
                (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V) ∧
              ∀ t ∈ Icc (-delta) 0, ∀ i, t ∈ Icc (-tau i) 0 →
                ∀ (x : P i) (hx : qL i x ∈ V) (a b : TangentSpace (𝓡 n) x),
                  ((F i).metric t).inner x a b = (G.metric t).inner ⟨qL i x, hx⟩
                    (mfderiv (𝓡 n) (𝓡 n) (qL i) x a)
                    (mfderiv (𝓡 n) (𝓡 n) (qL i) x b) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{v} Q) :=
    Poincare.Manifold.uliftChartedSpace _ Q
  let : IsManifold (𝓡 n) ∞ (ULift.{v} Q) :=
    Poincare.Manifold.uliftIsManifold (𝓡 n) Q
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 n) Q
  let gL := g0.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
  let qL : ∀ i, P i → ULift.{v} Q := fun i x => ULift.up (q i x)
  obtain ⟨hc, hd⟩ := terminalGerms_lifted_complete_metric g0 hcomplete
  obtain ⟨hql, hcoverl⟩ := terminalGerms_lifted_chart_cover q hq hcover
  refine ⟨hc, hd, ?_⟩
  intro V hne hcompact
  apply terminalGerms_precompact_flow tau htau F qL hql hcoverl ?_ gL ?_ V hne hcompact
  · intro i j t hi hj x y hxy a b c e ha hb
    exact terminalGerms_diffeomorph_fibre_compatibility d (q i) (q j) (hq i) (hq j)
      ((F i).metric t) ((F j).metric t) (hinv i j t hi hj) x y hxy a b c e ha hb
  · intro i x a b
    exact terminalGerms_diffeomorph_chart_metric d (q i) (hq i) ((F i).metric 0) g0
      (hterminal i) x a b

end PoincareConjecture.M47
