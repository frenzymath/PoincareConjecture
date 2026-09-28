import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePartitionAt
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeWeakPartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem exists_anchored_weak_minimum (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau s : ℝ} {x y : G.Point} (hs : s ∈ Ioo 0 (Real.sqrt tau))
    (p : ℕ → M14BackwardPath G T 0 tau x y)
    (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformlyOn (fun k r => (p k).curve (r ^ 2)) gamma atTop (Icc 0 (Real.sqrt tau)))
    {D L : ℝ} (henergy : ∀ k,
      IntervalIntegrable (M14.pathSquareKinetic (p k)) volume 0 (Real.sqrt tau) ∧
      (∫ r in 0..Real.sqrt tau, M14.pathSquareKinetic (p k) r) ≤ D)
    (haction : Tendsto (fun k => M14BackwardLAction G (p k)) atTop (𝓝 L)) :
    ∃ R : GaugePrimitivePartition gamma 0 (Real.sqrt tau), R.action ≤ L ∧
      ∃ j : Fin R.count, R.node j.castSucc < s ∧ s < R.node j.succ := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  obtain ⟨m, t, e, l, r, K, N, j, ht, hta, htb, hp, htail, hanchor⟩ :=
    exists_compact_gauge_partition_at hs gamma hgamma (fun k r => (p k).curve (r ^ 2)) hlim
  have hbig (i : Fin m) : Icc (l i) (r i) ⊆ Icc 0 (Real.sqrt tau) :=
    Icc_subset_Icc (hp i).1 (hp i).2.2.1
  have hcore (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc (l i) (r i) :=
    Icc_subset_Icc (hp i).2.2.2.1 (hp i).2.2.2.2.1
  have hK (i : Fin m) : IsCompact (K i) := (hp i).2.2.2.2.2.1
  have hgammaK (i : Fin m) : MapsTo gamma (Icc (l i) (r i)) (K i) :=
    fun z hz => interior_subset ((hp i).2.2.2.2.2.2.1 (mem_image_of_mem gamma hz))
  have hKU (i : Fin m) : K i ⊆ (e i).source := (hp i).2.2.2.2.2.2.2.1
  let q (k : ℕ) := p (k + N)
  have hlimq : TendstoUniformlyOn (fun k r => (q k).curve (r ^ 2)) gamma atTop
      (Icc 0 (Real.sqrt tau)) := by
    intro U hU
    exact (tendsto_add_atTop_nat N).eventually (hlim U hU)
  obtain ⟨w, hprimitive, hweak⟩ := exists_gauge_weak_partition hM12 q gamma hgamma
    t ht hta htb e K hK hKU
    (fun i k z hz => htail (k + N) (Nat.le_add_left N k) i (hcore i hz))
    (fun i z hz => hgammaK i (hcore i hz)) hlimq (fun k => henergy (k + N))
    (haction.comp (tendsto_add_atTop_nat N))
  let R : GaugePrimitivePartition gamma 0 (Real.sqrt tau) := {
    count := m
    node := t
    monotone := ht
    first := hta
    last := htb
    gauge := e
    left := l
    right := r
    big_subset := hbig
    core_subset := hcore
    near := fun i => (hp i).2.2.2.2.2.2.2.2
    source := fun i z hz => hKU i (hgammaK i hz)
    velocity := w
    primitive := hprimitive }
  exact ⟨R, hweak, j, hanchor.2.1, hanchor.2.2.1⟩

end PoincareConjecture.Proofs.M46
