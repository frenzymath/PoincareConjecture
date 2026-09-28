import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.RegularFiberScaling
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedSimilarity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology


theorem PoincareConjecture.RiemannianMetric.exists_scaled_openFiber_weighted_integral_equivalence
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
    [IsManifold (𝓡 (m+k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m+k) M)
    {f : M → Fin k → ℝ} (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) f x))
    (v : Fin k → ℝ) (hm : 2 ≤ m) {a : ℝ} (ha : 1 ≤ a) :
    let F := fun x => Real.sqrt a • f x
    let w := Real.sqrt a • v
    ∃ hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F,
      ∃ hregF : ∀ x ∈ U, Function.Surjective
        (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) F x),
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m) hf U hreg v
        letI := isManifold_openFiber (m := m) hf U hreg v
        letI := openFiberChartedSpace (m := m) hF U hregF w
        letI := isManifold_openFiber (m := m) hF U hregF w
        let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg v g
        let gNew := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hF U hregF w
          (PoincareConjecture.rescaledMetric g a (zero_lt_one.trans_le ha))
        ∃ e : openFiber f U v ≃ₘ⟮𝓡 m,𝓡 m⟯ openFiber F U w,
          (∀ x, openFiberIncl F U w (e x) = openFiberIncl f U v x) ∧
          (∀ (x : openFiber f U v) (z z' : TangentSpace (𝓡 m) x),
            gNew.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x z)
              (mfderiv (𝓡 m) (𝓡 m) e x z') = a * gOld.inner x z z') ∧
          (∀ x y, PoincareConjecture.RiemannianMetric.edist gNew (e x) (e y) =
            ENNReal.ofReal (Real.sqrt a) * gOld.edist x y) ∧
          (PoincareConjecture.MetricComplete g → f ⁻¹' {v} ⊆ U →
            PoincareConjecture.MetricComplete gOld ∧ PoincareConjecture.MetricComplete gNew) ∧
          ∀ (K : openFiber f U v → ℝ), (∀ x, 0 ≤ K x) →
            ∀ s t : Set (openFiber f U v),
              ((∫ x in s, max 0 (gOld.leviCivitaData.scalarCurvature x)
                  ∂gOld.volumeMeasure) /
                (1 + ∫ x in t, K x ∂gOld.volumeMeasure)) ≤
              ((∫ y in e '' s, max 0 (gNew.leviCivitaData.scalarCurvature y)
                  ∂gNew.volumeMeasure) /
                (1 + ∫ y in e '' t, a⁻¹ * K (e.symm y) ∂gNew.volumeMeasure)) := by
  let F := fun x => Real.sqrt a • f x
  let w := Real.sqrt a • v
  obtain ⟨hF, hregF, hdata⟩ :=
    g.exists_scaled_openFiber_metric_equivalence hf U hreg v (zero_lt_one.trans_le ha)
  refine ⟨hF, hregF, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg v
  let := isManifold_openFiber (m := m) hf U hreg v
  let := openFiberChartedSpace (m := m) hF U hregF w
  let := isManifold_openFiber (m := m) hF U hregF w
  let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg v g
  let gNew := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hF U hregF w
    (PoincareConjecture.rescaledMetric g a (zero_lt_one.trans_le ha))
  obtain ⟨e, hinc, hmetric, hdist, hcomplete⟩ := hdata
  refine ⟨e, hinc, hmetric, hdist, hcomplete, ?_⟩
  intro K hK s t
  exact gOld.leviCivitaData.normalized_pos_scalar_integral_le_of_metric_similarity
    gNew.leviCivitaData hm e ha hmetric K hK s t
