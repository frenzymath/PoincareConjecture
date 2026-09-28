import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.IteratedFiber
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Isometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 400000 in

theorem PoincareConjecture.RiemannianMetric.exists_iterated_openFiber_scalar_integral_equivalence
    {m k : ℕ} {M : Type*} [TopologicalSpace M]
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((m + 1) + k))) M]
    [IsManifold (𝓡 ((m + 1) + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric ((m + 1) + k) M)
    {f : M → Fin k → ℝ} {φ : M → ℝ}
    (hf : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (hφ : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ φ)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) f x)) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
      (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
    letI (c : Fin k → ℝ) := openFiberChartedSpace (m := m + 1) hf U hreg c
    letI (c : Fin k → ℝ) := isManifold_openFiber (m := m + 1) hf U hreg c
    (∀ c : Fin k → ℝ, ∀ x : openFiber f U c,
      mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) (φ ∘ openFiberIncl f U c) x ≠ 0) →
    let joint := fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y)
    ∃ hjoint : ∀ x ∈ U, Function.Surjective
        (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) joint x),
      ∃ hjsmooth : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ joint,
      ∀ (c : Fin k → ℝ) (t : ℝ),
        let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg c g
        let φOld := φ ∘ openFiberIncl f U c
        let hφOld := hφ.comp (contMDiff_openFiberIncl (m := m + 1) hf U hreg c)
        ∃ hlevel : ∀ x : openFiber f U c, mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) φOld x ≠ 0,
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
            ⟨finrank_euclideanSpace_fin⟩
          letI := openLevelSetChartedSpace hφOld ⊤ (fun x _ => hlevel x) m t
          letI := isManifold_openLevelSet hφOld ⊤ (fun x _ => hlevel x) m t
          let gIter := PoincareConjecture.RiemannianMetric.regularLevelMetric
            hφOld ⊤ (fun x _ => hlevel x) t gOld
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
            m + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
          letI := openFiberChartedSpace (m := m) hjsmooth U hjoint (Fin.cons t c)
          letI := isManifold_openFiber (m := m) hjsmooth U hjoint (Fin.cons t c)
          let gJoint := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
            (openFiberIncl joint U (Fin.cons t c))
            (contMDiff_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons t c))
            (injective_mfderiv_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons t c))
          ∃ e : openLevelSet φOld ⊤ t ≃ₘ⟮𝓡 m, 𝓡 m⟯ openFiber joint U (Fin.cons t c),
            e.toEquiv = iteratedOpenFiberEquiv f φ U c t ∧
            (∀ (x : openLevelSet φOld ⊤ t) (v w : TangentSpace (𝓡 m) x),
              gIter.inner x v w = gJoint.inner (e x)
                (mfderiv (𝓡 m) (𝓡 m) e x v) (mfderiv (𝓡 m) (𝓡 m) e x w)) ∧
            (∀ x y : openLevelSet φOld ⊤ t,
              PoincareConjecture.RiemannianMetric.edist gJoint (e x) (e y) = gIter.edist x y) ∧
            MeasureTheory.MeasurePreserving e (PoincareConjecture.RiemannianMetric.volumeMeasure gIter) (PoincareConjecture.RiemannianMetric.volumeMeasure gJoint) ∧
            ∀ Ψ : ℝ → ℝ,
              (∫ x, Ψ ((PoincareConjecture.RiemannianMetric.leviCivitaData gIter).scalarCurvature x) ∂(PoincareConjecture.RiemannianMetric.volumeMeasure gIter)) =
                ∫ y, Ψ ((PoincareConjecture.RiemannianMetric.leviCivitaData gJoint).scalarCurvature y) ∂(PoincareConjecture.RiemannianMetric.volumeMeasure gJoint) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
      (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
  let (c : Fin k → ℝ) := openFiberChartedSpace (m := m + 1) hf U hreg c
  let (c : Fin k → ℝ) := isManifold_openFiber (m := m + 1) hf U hreg c
  dsimp only
  intro hφreg
  let joint := fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y)
  obtain ⟨hjoint, hjsmooth, hiter⟩ :=
    g.exists_iterated_openFiber_metric_equivalence hf hφ U hreg hφreg
  refine ⟨hjoint, hjsmooth, ?_⟩
  intro c t
  let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg c g
  let φOld := φ ∘ openFiberIncl f U c
  let hφOld := hφ.comp (contMDiff_openFiberIncl (m := m + 1) hf U hreg c)
  obtain ⟨hlevel, hdata⟩ := hiter c t
  refine ⟨hlevel, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hφOld ⊤ (fun x _ => hlevel x) m t
  let := isManifold_openLevelSet hφOld ⊤ (fun x _ => hlevel x) m t
  let gIter := PoincareConjecture.RiemannianMetric.regularLevelMetric
    hφOld ⊤ (fun x _ => hlevel x) t gOld
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
      m + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  let := openFiberChartedSpace (m := m) hjsmooth U hjoint (Fin.cons t c)
  let := isManifold_openFiber (m := m) hjsmooth U hjoint (Fin.cons t c)
  let gJoint := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
    (openFiberIncl joint U (Fin.cons t c))
    (contMDiff_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons t c))
    (injective_mfderiv_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons t c))
  obtain ⟨e, he, hmetric, hdist⟩ := hdata
  refine ⟨e, he, hmetric, hdist, ?_, ?_⟩
  · exact PoincareConjecture.RiemannianMetric.measurePreserving_volumeMeasure_of_edist_eq
      gIter gJoint e.toEquiv hdist
  · intro Ψ
    exact PoincareConjecture.LeviCivitaData.integral_scalarCurvature_eq_of_diffeomorph
      (PoincareConjecture.RiemannianMetric.leviCivitaData gIter)
      (PoincareConjecture.RiemannianMetric.leviCivitaData gJoint) e hmetric Ψ
