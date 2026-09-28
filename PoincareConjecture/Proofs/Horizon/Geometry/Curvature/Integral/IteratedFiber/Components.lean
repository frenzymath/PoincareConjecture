import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.ConnectedComponent.Equivalence
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.IteratedFiber
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevelEquiv
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.RegularDomain
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem PoincareConjecture.RiemannianMetric.exists_shifted_iterated_openFiber_component_equivalence
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((m + 1) + k))) M]
    [IsManifold (𝓡 ((m + 1) + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric ((m + 1) + k) M)
    {f : M → Fin k → ℝ} {F : M → ℝ}
    (hf : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (hF : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ F)
    (U : Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) f x)) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
      (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
    letI (c : Fin k → ℝ) := openFiberChartedSpace (m := m + 1) hf U hreg c
    letI (c : Fin k → ℝ) := isManifold_openFiber (m := m + 1) hf U hreg c
    (∀ c : Fin k → ℝ, ∀ x : openFiber f U c,
      mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) (F ∘ openFiberIncl f U c) x ≠ 0) →
    let joint := fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (F y) (f y)
    ∃ hjoint : ∀ x ∈ U, Function.Surjective
        (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) joint x),
      ∃ hjsmooth : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ joint,
      ∀ (c : Fin k → ℝ) (b t : ℝ),
        let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg c g
        let ψ := fun x : openFiber f U c => F (openFiberIncl f U c x) - b
        let hψ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ ψ :=
          (hF.comp (contMDiff_openFiberIncl (m := m + 1) hf U hreg c)).sub contMDiff_const
        let W := gOld.regularDomain hψ
        let hψreg := gOld.regularDomain_regular hψ
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openLevelSetChartedSpace hψ W hψreg m t
        letI := isManifold_openLevelSet hψ W hψreg m t
        let gLevel := PoincareConjecture.RiemannianMetric.regularLevelMetric hψ W hψreg t gOld
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
          m + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
        letI := openFiberChartedSpace (m := m) hjsmooth U hjoint (Fin.cons (t + b) c)
        letI := isManifold_openFiber (m := m) hjsmooth U hjoint (Fin.cons (t + b) c)
        let gJoint := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
          (openFiberIncl joint U (Fin.cons (t + b) c))
          (contMDiff_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons (t + b) c))
          (injective_mfderiv_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons (t + b) c))
        ∃ e : openLevelSet ψ W t ≃ₘ⟮𝓡 m, 𝓡 m⟯ openFiber joint U (Fin.cons (t + b) c),
          (∀ x, openFiberIncl joint U (Fin.cons (t + b) c) (e x) =
            openFiberIncl f U c (openLevelIncl ψ W t x)) ∧
          (∀ (x : openLevelSet ψ W t) (v w : TangentSpace (𝓡 m) x),
            gLevel.inner x v w = gJoint.inner (e x)
              (mfderiv (𝓡 m) (𝓡 m) e x v) (mfderiv (𝓡 m) (𝓡 m) e x w)) ∧
          ∀ p : openLevelSet ψ W t,
            let E := Poincare.connectedComponentDiffeomorph e p
            let gC := gLevel.connectedComponentMetric p
            let hC := PoincareConjecture.RiemannianMetric.connectedComponentMetric gJoint (e p)
            (∀ x y, hC.edist (E x) (E y) = gC.edist x y) ∧
            MeasurePreserving E gC.volumeMeasure hC.volumeMeasure ∧
            (∀ x, gC.leviCivitaData.scalarCurvature x =
              hC.leviCivitaData.scalarCurvature (E x)) ∧
            (∀ K : Poincare.connectedComponentOpens
                (EuclideanSpace ℝ (Fin m)) p → ℝ,
              (∫ x, K x ∂gC.volumeMeasure) =
                ∫ y, K (E.symm y) ∂hC.volumeMeasure) ∧
            ∀ Ψ : ℝ → ℝ,
              (∫ x, Ψ (gC.leviCivitaData.scalarCurvature x) ∂gC.volumeMeasure) =
                ∫ y, Ψ (hC.leviCivitaData.scalarCurvature y) ∂hC.volumeMeasure := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
    (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
  let (c : Fin k → ℝ) := openFiberChartedSpace (m := m + 1) hf U hreg c
  let (c : Fin k → ℝ) := isManifold_openFiber (m := m + 1) hf U hreg c
  intro hFreg
  let joint := fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (F y) (f y)
  obtain ⟨hjoint, hjsmooth, hiter⟩ :=
    g.exists_iterated_openFiber_metric_equivalence hf hF U hreg hFreg
  refine ⟨hjoint, hjsmooth, ?_⟩
  intro c b t
  let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg c g
  let φOld := F ∘ openFiberIncl f U c
  let hφOld := hF.comp (contMDiff_openFiberIncl (m := m + 1) hf U hreg c)
  let ψ := fun x : openFiber f U c => F (openFiberIncl f U c x) - b
  let hψ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ ψ := hφOld.sub contMDiff_const
  let W := gOld.regularDomain hψ
  let hψreg := gOld.regularDomain_regular hψ
  have hψall (x : openFiber f U c) :
      mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ψ x ≠ 0 := by
    have hd : mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ψ x =
        mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) φOld x := by
      change mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) (φOld - fun _ => b) x = _
      rw [mfderiv_sub (hφOld.mdifferentiable (by simp) x) mdifferentiableAt_const,
        mfderiv_const, sub_zero]
    rw [hd]
    exact hFreg c x
  obtain ⟨hlevel, hdata⟩ := hiter c (t + b)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hψ W hψreg m t
  let := isManifold_openLevelSet hψ W hψreg m t
  let := openLevelSetChartedSpace hφOld ⊤ (fun x _ => hlevel x) m (t + b)
  let := isManifold_openLevelSet hφOld ⊤ (fun x _ => hlevel x) m (t + b)
  let gLevel := PoincareConjecture.RiemannianMetric.regularLevelMetric hψ W hψreg t gOld
  let gIter := PoincareConjecture.RiemannianMetric.regularLevelMetric hφOld ⊤
    (fun x _ => hlevel x) (t + b) gOld
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
    m + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  let := openFiberChartedSpace (m := m) hjsmooth U hjoint (Fin.cons (t + b) c)
  let := isManifold_openFiber (m := m) hjsmooth U hjoint (Fin.cons (t + b) c)
  let gJoint : PoincareConjecture.RiemannianMetric m (openFiber joint U (Fin.cons (t + b) c)) :=
    PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
      (openFiberIncl joint U (Fin.cons (t + b) c))
      (contMDiff_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons (t + b) c))
      (injective_mfderiv_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons (t + b) c))
  obtain ⟨e₁, he₁, hm₁, hd₁⟩ := hdata
  have heq (x : openFiber f U c) :
      (x ∈ W ∧ ψ x = t) ↔ (x ∈ (⊤ : Opens (openFiber f U c)) ∧ φOld x = t + b) := by
    have hxW : x ∈ W := (gOld.mem_regularDomain_iff hψ x).mpr (hψall x)
    simp only [hxW, Opens.mem_top, true_and]
    change F (openFiberIncl f U c x) - b = t ↔
      F (openFiberIncl f U c x) = t + b
    exact sub_eq_iff_eq_add
  let e₀ := openLevelDiffeomorphOfEq hψ hφOld m hψreg (fun x _ => hlevel x) heq
  let e := e₀.trans e₁
  have hm₀ (x : openLevelSet ψ W t) (v w : TangentSpace (𝓡 m) x) :
      gLevel.inner x v w = gIter.inner (e₀ x)
        (mfderiv (𝓡 m) (𝓡 m) e₀ x v) (mfderiv (𝓡 m) (𝓡 m) e₀ x w) :=
    gOld.regularLevelMetric_inner_equivOfEq hψ hφOld hψreg
      (fun x _ => hlevel x) heq x v w
  have hm (x : openLevelSet ψ W t) (v w : TangentSpace (𝓡 m) x) :
      gLevel.inner x v w = gJoint.inner (e x)
        (mfderiv (𝓡 m) (𝓡 m) e x v) (mfderiv (𝓡 m) (𝓡 m) e x w) := by
    rw [hm₀, hm₁]
    have hd := mfderiv_comp x (e₁.contMDiff.mdifferentiable (by simp) (e₀ x))
      (e₀.contMDiff.mdifferentiable (by simp) x)
    change mfderiv (𝓡 m) (𝓡 m) e x = _ at hd
    rw [hd]
    rfl
  refine ⟨e, ?_, hm, ?_⟩
  · intro x
    change openFiberIncl joint U (Fin.cons (t + b) c) (e₁ (e₀ x)) = _
    have hval := congrArg (fun e : openLevelSet φOld ⊤ (t + b) ≃
      openFiber joint U (Fin.cons (t + b) c) =>
        openFiberIncl joint U (Fin.cons (t + b) c) (e (e₀ x))) he₁
    exact hval
  · intro p
    have hgeom := gLevel.connectedComponentMetric_geometry_diffeomorph gJoint e hm p
    exact ⟨hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2.1,
      hgeom.2.2.2.2.1, hgeom.2.2.2.2.2⟩
