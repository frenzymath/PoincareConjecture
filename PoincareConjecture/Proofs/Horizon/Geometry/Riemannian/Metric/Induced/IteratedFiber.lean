import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.Augmented
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.Iterated
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Equivalence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 400000 in

theorem PoincareConjecture.RiemannianMetric.exists_iterated_openFiber_metric_equivalence
    {m k : ℕ} {M : Type*} [TopologicalSpace M]
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
            ∀ x y : openLevelSet φOld ⊤ t,
              PoincareConjecture.RiemannianMetric.edist gJoint (e x) (e y) = gIter.edist x y := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
      (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
  let (c : Fin k → ℝ) := openFiberChartedSpace (m := m + 1) hf U hreg c
  let (c : Fin k → ℝ) := isManifold_openFiber (m := m + 1) hf U hreg c
  dsimp only
  intro hφreg
  let joint := fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y)
  have hjoint : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) joint x) := by
    intro x hx
    exact surjective_mfderiv_cons_of_regular_openFiber_restriction hf hφ U hreg
      (f x) ⟨⟨x, hx⟩, rfl⟩ (hφreg (f x) ⟨⟨x, hx⟩, rfl⟩)
  have hjsmooth : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ joint := by
    apply contMDiff_pi_space.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hφ
    · exact contMDiff_pi_space.mp hf j
  refine ⟨hjoint, hjsmooth, ?_⟩
  intro c t
  let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg c g
  let φOld := φ ∘ openFiberIncl f U c
  let hφOld := hφ.comp (contMDiff_openFiberIncl (m := m + 1) hf U hreg c)
  let hlevel := hφreg c
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
  let e₀ := iteratedOpenFiberEquiv f φ U c t
  have he : ContMDiff (𝓡 m) (𝓡 m) ∞ e₀ := by
    intro x
    apply (contMDiffAt_into_openFiber_iff (m := m) hjsmooth (Fin.cons t c)
      U hjoint e₀ x).mpr
    exact (contMDiff_openFiberIncl (m := m + 1) hf U hreg c _).comp x
      (contMDiff_openLevelIncl hφOld ⊤ (fun x _ => hlevel x) m t x)
  have hei : ContMDiff (𝓡 m) (𝓡 m) ∞ e₀.symm := by
    intro x
    apply (contMDiffAt_into_openLevelSet_iff hφOld m t ⊤
      (fun x _ => hlevel x) e₀.symm x).mpr
    apply (contMDiffAt_into_openFiber_iff (m := m + 1) hf c U hreg
      (openLevelIncl φOld ⊤ t ∘ e₀.symm) x).mpr
    exact contMDiff_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons t c) x
  let e : openLevelSet φOld ⊤ t ≃ₘ⟮𝓡 m, 𝓡 m⟯ openFiber joint U (Fin.cons t c) :=
    { toEquiv := e₀, contMDiff_toFun := he, contMDiff_invFun := hei }
  have hmetric : ∀ (x : openLevelSet φOld ⊤ t) (v w : TangentSpace (𝓡 m) x),
      gIter.inner x v w = gJoint.inner (e x)
        (mfderiv (𝓡 m) (𝓡 m) e x v) (mfderiv (𝓡 m) (𝓡 m) e x w) := by
    intro x v w
    have hcomp : (openFiberIncl joint U (Fin.cons t c)) ∘ e =
        openFiberIncl f U c ∘ openLevelIncl φOld ⊤ t := rfl
    have hd : (mfderiv (𝓡 m) (𝓡 ((m + 1) + k))
        ((openFiberIncl joint U (Fin.cons t c)) ∘ e) x :
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ((m + 1) + k))) =
        mfderiv (𝓡 m) (𝓡 ((m + 1) + k))
          (openFiberIncl f U c ∘ openLevelIncl φOld ⊤ t) x := by
      rw [hcomp]
    rw [mfderiv_comp x
      ((contMDiff_openFiberIncl (m := m) hjsmooth U hjoint (Fin.cons t c) _).mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiable (by simp) x),
      mfderiv_comp x
        ((contMDiff_openFiberIncl (m := m + 1) hf U hreg c _).mdifferentiableAt (by simp))
        ((contMDiff_openLevelIncl hφOld ⊤ (fun x _ => hlevel x) m t x).mdifferentiableAt (by simp))] at hd
    have hdv := congrArg (fun A => A v) hd
    have hdw := congrArg (fun A => A w) hd
    change g.inner (openFiberIncl f U c (openLevelIncl φOld ⊤ t x))
      (mfderiv (𝓡 (m + 1)) (𝓡 ((m + 1) + k)) (openFiberIncl f U c) _
        (mfderiv (𝓡 m) (𝓡 (m + 1)) (openLevelIncl φOld ⊤ t) x v))
      (mfderiv (𝓡 (m + 1)) (𝓡 ((m + 1) + k)) (openFiberIncl f U c) _
        (mfderiv (𝓡 m) (𝓡 (m + 1)) (openLevelIncl φOld ⊤ t) x w)) =
      g.inner (openFiberIncl joint U (Fin.cons t c) (e x))
        (mfderiv (𝓡 m) (𝓡 ((m + 1) + k)) (openFiberIncl joint U (Fin.cons t c)) _
          (mfderiv (𝓡 m) (𝓡 m) e x v))
        (mfderiv (𝓡 m) (𝓡 ((m + 1) + k)) (openFiberIncl joint U (Fin.cons t c)) _
          (mfderiv (𝓡 m) (𝓡 m) e x w))
    change mfderiv (𝓡 m) (𝓡 ((m + 1) + k)) (openFiberIncl joint U (Fin.cons t c)) _
      (mfderiv (𝓡 m) (𝓡 m) e x v) = _ at hdv
    change mfderiv (𝓡 m) (𝓡 ((m + 1) + k)) (openFiberIncl joint U (Fin.cons t c)) _
      (mfderiv (𝓡 m) (𝓡 m) e x w) = _ at hdw
    rw [hdv, hdw]
    rfl
  exact ⟨e, rfl, hmetric,
    PoincareConjecture.RiemannianMetric.edist_eq_of_diffeomorph_metric_pullback gIter gJoint e hmetric⟩
