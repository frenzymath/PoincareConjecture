import PoincareConjecture.Proofs.M47.TerminalGermsExhaustionOperator
import PoincareConjecture.Proofs.M47.TerminalCurvatureFiniteGermsBound











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem terminalCurvature_bound_of_original_chart_flows
    {epsilon1 epsilon A H : ℝ} (hM45 : M45SmallNeckScaleBound.{u} epsilon1)
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ epsilon1)
    (hcalibrated : epsilon ≤ 1 / 200) (hA : 0 < A)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hC : RicciFlowCurvatureTheory.{u}) (hcomplete : MetricComplete g)
    (p : M) (hscalar : D.scalarCurvature p ≠ 0)
    {ι : Type*} {P : ι → Type*}
    [∀ i, TopologicalSpace (P i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i)]
    [∀ i, IsManifold (𝓡 3) ∞ (P i)]
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow 3 (P i) (Icc (-tau i) 0))
    (q : ∀ i, P i → M)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinv : ∀ i j t, t ∈ Icc (-tau i) 0 → t ∈ Icc (-tau j) 0 →
      ∀ (x : P i) (y : P j), q i x = q j y →
      ∀ (a b : TangentSpace (𝓡 3) x) (c d : TangentSpace (𝓡 3) y),
        mfderiv (𝓡 3) (𝓡 3) (q i) x a = mfderiv (𝓡 3) (𝓡 3) (q j) y c →
        mfderiv (𝓡 3) (𝓡 3) (q i) x b = mfderiv (𝓡 3) (𝓡 3) (q j) y d →
        ((F i).metric t).inner x a b = ((F j).metric t).inner y c d)
    (hterminal : ∀ i (x : P i) (a b : TangentSpace (𝓡 3) x),
      ((F i).metric 0).inner x a b = g.inner (q i x)
        (mfderiv (𝓡 3) (𝓡 3) (q i) x a)
        (mfderiv (𝓡 3) (𝓡 3) (q i) x b))
    (hchartOperator : ∀ i t, t ∈ Icc (-tau i) 0 → ∀ x,
      ((F i).connection t).NonnegativeCurvatureOperator x)
    (E : ℕ → Set M) (hE : ∀ j, IsOpen (E j))
    (hconnected : ∀ j, IsConnected (E j))
    (hcompact : ∀ j, IsCompact (closure (E j)))
    (hnested : ∀ j, closure (E j) ⊆ E (j + 1))
    (hexhaust : (⋃ j, E j) = univ)
    (hreadout : ∀ x, H ≤ D.scalarCurvature x →
      (∃ N : EpsilonNeck g, N.connection = D ∧ N.epsilon = epsilon ∧
        D.scalarCurvature x ≤ A * D.scalarCurvature N.center) ∨ IsCompact (univ : Set M)) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ x, D.curvatureTensorNorm x ≤ B0 := by
  let U : ℕ → Opens M := fun j => ⟨E j, hE j⟩
  let : ∀ j, ConnectedSpace (U j) := fun j =>
    isConnected_iff_connectedSpace.mp (hconnected j)
  obtain ⟨s, delta, _hsne, hs, hdelta, htime, G, hmetric, hread, _hcompat, htriple⟩ :=
    terminalGerms_exists_exhaustion_flows tau htau F q hq hcover hinv g hterminal
      E hE hconnected hcompact hnested hexhaust
  have hlocal : ∀ j t, t ∈ Icc (-delta j) 0 → ∀ y,
      ((G j).connection t).NonnegativeCurvatureOperator y := by
    intro j
    apply terminalGerms_descended_operator tau F q hq (U j) (s j) ?_
      (htime j) (G j) (hread j) hchartOperator
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs j (subset_closure hy))
    obtain ⟨his, x, hx⟩ := mem_iUnion.mp hi
    exact ⟨i, his, x, hx⟩
  have hoperator : ∀ x, D.NonnegativeCurvatureOperator x :=
    terminalGerms_ambient_operator_of_exhaustion D U delta hdelta G hmetric hlocal (by
      intro y
      obtain ⟨j, _, _, hy⟩ := htriple p p y
      exact ⟨j, hy⟩)
  exact terminalCurvature_bound_of_finite_germs hM45 hepsilon hsmall hcalibrated hA
    D hC hcomplete hoperator p hscalar U delta hdelta G hmetric hlocal htriple hreadout

end PoincareConjecture.M47
