import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberScaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Similarity







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology

theorem PoincareConjecture.RiemannianMetric.exists_scaled_openFiber_scalar_integral_equivalence
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
    [IsManifold (𝓡 (m+k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m+k) M)
    {f : M → Fin k → ℝ} (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) f x))
    (v : Fin k → ℝ) {a : ℝ} (ha : 0<a) :
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
          (PoincareConjecture.rescaledMetric g a ha)
        ∃ e : openFiber f U v ≃ₘ⟮𝓡 m,𝓡 m⟯ openFiber F U w,
          (∀ x, openFiberIncl F U w (e x) = openFiberIncl f U v x) ∧
          (∀ (x : openFiber f U v) (z z' : TangentSpace (𝓡 m) x),
            gNew.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x z)
              (mfderiv (𝓡 m) (𝓡 m) e x z') = a * gOld.inner x z z') ∧
          (∀ x y, PoincareConjecture.RiemannianMetric.edist gNew (e x) (e y) =
            ENNReal.ofReal (Real.sqrt a) * gOld.edist x y) ∧
          (PoincareConjecture.MetricComplete g → f ⁻¹' {v} ⊆ U →
            PoincareConjecture.MetricComplete gOld ∧ PoincareConjecture.MetricComplete gNew) ∧
          MeasureTheory.MeasurePreserving e
            (ENNReal.ofReal (Real.sqrt a) ^ m • gOld.volumeMeasure) gNew.volumeMeasure ∧
          (∀ Ψ : ℝ → ℝ,
            (∫ y, Ψ (gNew.leviCivitaData.scalarCurvature y) ∂gNew.volumeMeasure) =
              (Real.sqrt a) ^ m *
                ∫ x, Ψ (a⁻¹ * gOld.leviCivitaData.scalarCurvature x) ∂gOld.volumeMeasure) ∧
          ∀ s : Set (openFiber f U v),
            (∫ y in e '' s, max 0 (gNew.leviCivitaData.scalarCurvature y) ∂gNew.volumeMeasure) =
              (Real.sqrt a) ^ m / a *
                ∫ x in s, max 0 (gOld.leviCivitaData.scalarCurvature x) ∂gOld.volumeMeasure := by
  let F := fun x => Real.sqrt a • f x
  let w := Real.sqrt a • v
  obtain ⟨hF, hregF, hdata⟩ := g.exists_scaled_openFiber_metric_equivalence hf U hreg v ha
  refine ⟨hF, hregF, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg v
  let := isManifold_openFiber (m := m) hf U hreg v
  let := openFiberChartedSpace (m := m) hF U hregF w
  let := isManifold_openFiber (m := m) hF U hregF w
  let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg v g
  let gNew := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hF U hregF w
    (PoincareConjecture.rescaledMetric g a ha)
  obtain ⟨e, hinc, hmetric, hdist, hcomplete⟩ := hdata
  refine ⟨e, hinc, hmetric, hdist, hcomplete, ?_, ?_, ?_⟩
  · have hp := (PoincareConjecture.rescaledMetric gOld a ha).measurePreserving_volumeMeasure_of_edist_eq
      gNew e.toEquiv (fun x y => (hdist x y).trans
        (PoincareConjecture.rescaledMetric_edist gOld a ha x y).symm)
    change MeasurePreserving e (PoincareConjecture.rescaledMetric gOld a ha).volumeMeasure
      gNew.volumeMeasure at hp
    rw [PoincareConjecture.rescaledMetric_volumeMeasure] at hp
    exact hp
  · intro Ψ
    simpa only [smul_eq_mul] using
      gOld.leviCivitaData.integral_scalarCurvature_eq_of_metric_similarity
        gNew.leviCivitaData e ha hmetric Ψ
  · intro s
    exact gOld.leviCivitaData.setIntegral_pos_scalarCurvature_eq_of_metric_similarity
      gNew.leviCivitaData e ha hmetric s
