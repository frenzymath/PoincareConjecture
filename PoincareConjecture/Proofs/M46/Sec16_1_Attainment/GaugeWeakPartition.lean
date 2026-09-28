import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeAction
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePrimitivePartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem exists_gauge_weak_partition (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} {x y : G.Point} (p : ℕ → M14BackwardPath G T 0 tau x y)
    (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = 0) (htb : t (Fin.last m) = Real.sqrt tau)
    (e : Fin m → AttainmentGauge G) (K : Fin m → Set G.Point)
    (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ (e i).source)
    (hpaths : ∀ i k, MapsTo (fun s => (p k).curve (s ^ 2))
      (Icc (t i.castSucc) (t i.succ)) (K i))
    (hgammaK : ∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ)) (K i))
    (hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformlyOn (fun k s => (p k).curve (s ^ 2)) gamma atTop (Icc 0 (Real.sqrt tau)))
    {D L : ℝ} (henergy : ∀ k,
      IntervalIntegrable (M14.pathSquareKinetic (p k)) volume 0 (Real.sqrt tau) ∧
      (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic (p k) s) ≤ D)
    (haction : Tendsto (fun k => M14BackwardLAction G (p k)) atTop (𝓝 L)) :
    ∃ w : ∀ i : Fin m, M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (t i.castSucc) (t i.succ),
      (∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
        ((e i).lift (gamma s)).2.val = ((e i).lift (gamma (t i.castSucc))).2.val +
          ∫ r in t i.castSucc..s, w i r) ∧
      (∑ i, gaugePieceAction (e i) gamma (w i)) ≤ L := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  have ha (i : Fin m) : 0 ≤ t i.castSucc := hta ▸ ht (Fin.zero_le _)
  have hb (i : Fin m) : t i.succ ≤ Real.sqrt tau := htb ▸ ht (Fin.le_last _)
  have hab (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc 0 (Real.sqrt tau) :=
    Icc_subset_Icc (ha i) (hb i)
  obtain ⟨v, w, B, phi, hphi, hv, hw, hprimitive, hweak⟩ := finite_gauge_weak_limit
    e (fun i => t i.castSucc) (fun i => t i.succ) ha hb hab K hK hKU p gamma
    hpaths hgammaK (fun i s hs => hlim.tendsto_at (hsub i hs)) henergy
  refine ⟨w, hprimitive, ?_⟩
  have hC (i : Fin m) : 0 ≤ B i := (norm_nonneg (w i)).trans (hw i)
  have hlimsub (i : Fin m) : TendstoUniformlyOn
      (fun k s => (p (phi k)).curve (s ^ 2)) gamma atTop
        (Icc (t i.castSucc) (t i.succ)) := by
    intro U hU
    exact hphi.tendsto_atTop.eventually ((hlim.mono (hsub i)) U hU)
  apply finite_gauge_action_le hM12 e (fun i => t i.castSucc) (fun i => t i.succ)
    hab K hK hKU (fun k s => (p (phi k)).curve (s ^ 2)) gamma
    (fun i k => (M14.squarePath_continuousOn (p (phi k))).mono
      (by simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using hsub i))
    (fun _ => hgamma.continuousOn) (fun i k => hpaths i (phi k)) hgammaK hlimsub
    (fun i k => v i (phi k)) w B hC (fun i k => (hv i (phi k)).1) hweak
    (fun k => M14BackwardLAction G (p (phi k))) L (haction.comp hphi.tendsto_atTop)
  intro k
  exact (gauge_partition_action_eq hM12 (p (phi k)) t ht hta htb e
    (fun i s hs => hKU i (hpaths i (phi k) hs)) (fun i => v i (phi k))
    (fun i => (hv i (phi k)).2)).le

end PoincareConjecture.Proofs.M46
