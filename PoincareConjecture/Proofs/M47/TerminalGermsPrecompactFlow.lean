import PoincareConjecture.Proofs.M47.TerminalGermsFiniteDescent
import PoincareConjecture.Proofs.M47.TerminalGermsAdditionalChart
import PoincareConjecture.Proofs.M47.TerminalGermsOpenMetrics
import PoincareConjecture.Proofs.M47.TerminalGermsOpenReadout
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

theorem terminalGerms_precompact_flow
    {n : ℕ} {ι : Type*} {P : ι → Type*} {N : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace N]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ N]
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow n (P i) (Icc (-tau i) 0))
    (q : ∀ i, P i → N)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinv : ∀ i j t, t ∈ Icc (-tau i) 0 → t ∈ Icc (-tau j) 0 →
      ∀ (x : P i) (y : P j), q i x = q j y →
      ∀ (a b : TangentSpace (𝓡 n) x) (c d : TangentSpace (𝓡 n) y),
        mfderiv (𝓡 n) (𝓡 n) (q i) x a = mfderiv (𝓡 n) (𝓡 n) (q j) y c →
        mfderiv (𝓡 n) (𝓡 n) (q i) x b = mfderiv (𝓡 n) (𝓡 n) (q j) y d →
        ((F i).metric t).inner x a b = ((F j).metric t).inner y c d)
    (g0 : RiemannianMetric n N)
    (hterminal : ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
      ((F i).metric 0).inner x a b = g0.inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b))
    (V : Opens N) (hne : (V : Set N).Nonempty)
    (hcompact : IsCompact (closure (V : Set N))) :
    ∃ s : Finset ι, s.Nonempty ∧ closure (V : Set N) ⊆ ⋃ i ∈ s, range (q i) ∧
      ∃ delta : ℝ, 0 < delta ∧ (∀ i ∈ s, delta < tau i) ∧
        ∃ G : RicciFlow n V (Icc (-delta) 0),
          G.metric 0 = g0.pullbackOfLocalDiffeomorph Subtype.val
            (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V) ∧
          ∀ t ∈ Icc (-delta) 0, ∀ i, t ∈ Icc (-tau i) 0 →
            ∀ (x : P i) (hx : q i x ∈ V) (a b : TangentSpace (𝓡 n) x),
              ((F i).metric t).inner x a b = (G.metric t).inner ⟨q i x, hx⟩
                (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
                (mfderiv (𝓡 n) (𝓡 n) (q i) x b) := by
  classical
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover (fun i => range (q i))
    (fun i => (hq i).isOpen_range) (by
      intro y _
      obtain ⟨i, x, rfl⟩ := hcover y
      exact mem_iUnion.mpr ⟨i, mem_range_self x⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (subset_closure hy))
    obtain ⟨hi, _⟩ := mem_iUnion.mp hi
    exact ⟨i, hi⟩
  let : Nonempty s := by
    obtain ⟨i, hi⟩ := hsne
    exact ⟨⟨i, hi⟩⟩
  let Fpart : ∀ i : s,
      RicciFlow n (terminalGermsOpenChartSource (q i) (hq i) V) (Icc (-tau i) 0) :=
    fun i => (F i).restrictToOpen (terminalGermsOpenChartSource (q i) (hq i) V)
  have hpartCover : ∀ y : V, ∃ i : s,
      ∃ x : terminalGermsOpenChartSource (q i) (hq i) V,
        terminalGermsOpenChartMap (q i) (hq i) V x = y := by
    intro y
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs (subset_closure y.property))
    obtain ⟨his, hi⟩ := mem_iUnion.mp hi
    obtain ⟨x, hx⟩ := hi
    have hxV : q i x ∈ V := by rw [hx]; exact y.property
    exact ⟨⟨i, his⟩, ⟨x, hxV⟩, Subtype.ext hx⟩
  obtain ⟨delta, hd, hdi, G, hgzero, hpres⟩ := terminalGerms_finite_flow_descent
    (fun i : s => tau i) (fun i => htau i) Fpart
    (fun i => terminalGermsOpenChartMap (q i) (hq i) V)
    (fun i => terminalGerms_openChartMap_localDiffeomorph (q i) (hq i) V)
    hpartCover (by
      intro i j t hit hjt x y hxy a b c d ha hb
      exact terminalGerms_open_metric_compatibility (q i) (q j) (hq i) (hq j)
        ((F i).metric t) ((F j).metric t) (hinv i j t hit hjt) V x y hxy a b c d ha hb)
    (g0.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V)) (by
      intro i x a b
      exact terminalGerms_open_terminal_metric (q i) (hq i) ((F i).metric 0) g0
        (hterminal i) V x a b)
  refine ⟨s, hsne, hs, delta, hd, (fun i hi => hdi ⟨i, hi⟩), G, hgzero, ?_⟩
  intro t ht j hj x hx a b
  apply terminalGerms_open_metric_readout (q j) (hq j) V ((F j).metric t)
    (G.metric t) ?_ x hx a b
  intro y c d
  exact terminalGerms_metric_additional_chart
    (fun i : s => (Fpart i).metric t)
    (((F j).metric t).pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n)
        (terminalGermsOpenChartSource (q j) (hq j) V)))
    (G.metric t) (fun i => terminalGermsOpenChartMap (q i) (hq i) V)
    (fun i => terminalGerms_openChartMap_localDiffeomorph (q i) (hq i) V)
    hpartCover (hpres t ht) (terminalGermsOpenChartMap (q j) (hq j) V) (by
      intro i y z hyz c d e f hc hd
      have hit : t ∈ Icc (-tau i) 0 :=
        ⟨(neg_le_neg (hdi i).le).trans ht.1, ht.2⟩
      exact terminalGerms_open_metric_compatibility (q j) (q i) (hq j) (hq i)
        ((F j).metric t) ((F i).metric t) (hinv j i t hj hit) V
        y z hyz c d e f hc hd) y c d

end PoincareConjecture.M47
