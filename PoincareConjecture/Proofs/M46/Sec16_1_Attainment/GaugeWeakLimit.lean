import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeVelocity
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePartition










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T tau : ℝ} {x y : G.Point}




theorem finite_gauge_weak_limit {iota : Type*} [Finite iota]
    (e : iota → AttainmentGauge G) (a b : iota → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ Real.sqrt tau) (hab : ∀ i, a i ≤ b i)
    (K : iota → Set G.Point) (hK : ∀ i, IsCompact (K i))
    (hKU : ∀ i, K i ⊆ (e i).source)
    (p : ℕ → M14BackwardPath G T 0 tau x y) (gamma : ℝ → G.Point)
    (hpaths : ∀ i k, MapsTo (fun s => (p k).curve (s ^ 2)) (Icc (a i) (b i)) (K i))
    (hgamma : ∀ i, MapsTo gamma (Icc (a i) (b i)) (K i))
    (hpoint : ∀ i s, s ∈ Icc (a i) (b i) →
      Tendsto (fun k => (p k).curve (s ^ 2)) atTop (𝓝 (gamma s)))
    {D : ℝ} (henergy : ∀ k,
      IntervalIntegrable (M14.pathSquareKinetic (p k)) volume 0 (Real.sqrt tau) ∧
      (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic (p k) s) ≤ D) :
    ∃ (v : ∀ i, ℕ → M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i))
      (w : ∀ i, M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i))
      (B : iota → ℝ) (phi : ℕ → ℕ), StrictMono phi ∧
      (∀ i k, ‖v i k‖ ≤ B i ∧
        (v i k : ℝ → EuclideanSpace ℝ (Fin 3)) =ᵐ[volume.restrict (Icc (a i) (b i))]
          deriv (fun s => ((e i).lift ((p k).curve (s ^ 2))).2.val)) ∧
      (∀ i, ‖w i‖ ≤ B i) ∧
      (∀ i s, s ∈ Icc (a i) (b i) →
        ((e i).lift (gamma s)).2.val = ((e i).lift (gamma (a i))).2.val +
          ∫ r in a i..s, w i r) ∧
      ∀ i, ∀ l : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i) →L[ℝ] ℝ,
        Tendsto (fun k => l (v i (phi k))) atTop (𝓝 (l (w i))) := by
  classical
  let : Fintype iota := Fintype.ofFinite iota
  choose c hc hcbound using fun i => compact_gauge_square_velocity_bound
    (e i).index (e i).lift (e i).center (e i).smooth (e i).right_inv (hK i) (hKU i)
  choose hLp hvbound using fun i k => hcbound i (p k) (ha i) (hb i) (hab i)
    (henergy k).1 (henergy k).2 (fun s hs => hpaths i k hs)
  let v : ∀ i, ℕ → M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i) :=
    fun i k => (hLp i k).toLp (deriv (fun s => ((e i).lift ((p k).curve (s ^ 2))).2.val))
  let : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  let (i : iota) : TopologicalSpace.SeparableSpace
      (M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i)) := inferInstance
  obtain ⟨phi, hphi, w, hweak⟩ := M08.exists_finite_weak_subsequence v
    (fun i => Real.sqrt ((c i)⁻¹ * D)) hvbound
  refine ⟨v, w, (fun i => Real.sqrt ((c i)⁻¹ * D)), phi, hphi,
    (fun i k => ⟨hvbound i k, (hLp i k).coeFn_toLp⟩),
    (fun i => (hweak i).1), ?_, fun i => (hweak i).2⟩
  intro i s hs
  apply M08.chart_primitive_of_weak_limit
    (fun k r => ((e i).lift ((p (phi k)).curve (r ^ 2))).2.val)
    (fun r => ((e i).lift (gamma r)).2.val) (fun k => v i (phi k)) (w i)
    _ _ (hweak i).2 hs
  · intro k r hr
    have hregular := squarePath_gauge_coordinates_regular (e i).index (e i).lift
      (p (phi k)) (e i).smooth (ha i) (hb i)
      (fun t ht => hKU i (hpaths i (phi k) ht))
    exact M08.chart_primitive_of_deriv hregular.1 hregular.2 (hLp i (phi k)) hr
  · intro r hr
    have hcoord : ContinuousOn (fun q : G.Point => ((e i).lift q).2.val) (e i).source :=
      continuous_subtype_val.comp_continuousOn (e i).smooth.continuousOn.snd
    exact ((hcoord.continuousAt ((e i).source_open.mem_nhds
      (hKU i (hgamma i hr)))).tendsto.comp (hpoint i r hr)).comp hphi.tendsto_atTop

end PoincareConjecture.Proofs.M46
