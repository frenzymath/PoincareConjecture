import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.IteratedFiber
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.Equivalence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 600000 in

theorem PoincareConjecture.RiemannianMetric.exists_prefix_openFiber_metric_equivalence
    {m k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((m + 1) + k))) M]
    [IsManifold (𝓡 ((m + 1) + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric ((m + 1) + k) M)
    (f : Fin (k + 1) → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (U : Opens M)
    (hprefix : ∀ x ∈ U, Surjective
      (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ)
        (fun y (i : Fin k) => f i.castSucc y) x))
    (hfull : ∀ x ∈ U, Surjective
      (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ)
        (fun y i => f i y) x)) :
    let P := fun y (i : Fin k) => f i.castSucc y
    let hP : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
      contMDiff_pi_space.mpr (fun i => hf i.castSucc)
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
      (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
    letI (c : Fin k → ℝ) := openFiberChartedSpace (m := m + 1) hP U hprefix c
    letI (c : Fin k → ℝ) := isManifold_openFiber (m := m + 1) hP U hprefix c
    (∀ c : Fin k → ℝ, ∀ x : openFiber P U c,
      mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ)
        (f (Fin.last k) ∘ openFiberIncl P U c) x ≠ 0) →
    ∀ c : Fin (k + 1) → ℝ,
      let cP := fun i : Fin k => c i.castSucc
      let gP := g.openRegularFiberMetric hP U hprefix cP
      let φ := f (Fin.last k) ∘ openFiberIncl P U cP
      let hφ := (hf (Fin.last k)).comp (contMDiff_openFiberIncl (m := m + 1) hP U hprefix cP)
      ∃ hlevel : ∀ x : openFiber P U cP, mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) φ x ≠ 0,
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openLevelSetChartedSpace hφ ⊤ (fun x _ => hlevel x) m (c (Fin.last k))
        letI := isManifold_openLevelSet hφ ⊤ (fun x _ => hlevel x) m (c (Fin.last k))
        let gIter := gP.regularLevelMetric hφ ⊤ (fun x _ => hlevel x) (c (Fin.last k))
        let F := fun y i => f i y
        let hF : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ F :=
          contMDiff_pi_space.mpr hf
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
          m + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
        letI := openFiberChartedSpace (m := m) hF U hfull c
        letI := isManifold_openFiber (m := m) hF U hfull c
        let gFull := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
          (openFiberIncl F U c) (contMDiff_openFiberIncl (m := m) hF U hfull c)
          (injective_mfderiv_openFiberIncl (m := m) hF U hfull c)
        ∃ e : openLevelSet φ ⊤ (c (Fin.last k)) ≃ₘ⟮𝓡 m, 𝓡 m⟯ openFiber F U c,
          (∀ x, openFiberIncl F U c (e x) =
            openFiberIncl P U cP (openLevelIncl φ ⊤ (c (Fin.last k)) x)) ∧
          ∀ x y, PoincareConjecture.RiemannianMetric.edist gFull (e x) (e y) = gIter.edist x y := by
  classical
  let P := fun y (i : Fin k) => f i.castSucc y
  let hP : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
    contMDiff_pi_space.mpr (fun i => hf i.castSucc)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
    (m + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
  let (c : Fin k → ℝ) := openFiberChartedSpace (m := m + 1) hP U hprefix c
  let (c : Fin k → ℝ) := isManifold_openFiber (m := m + 1) hP U hprefix c
  dsimp only
  intro hlast c
  let F := fun y i => f i y
  let hF : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ F :=
    contMDiff_pi_space.mpr hf
  let joint := fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ)
    (f (Fin.last k) y) (P y)
  obtain ⟨hjoint, hjsmooth, hiter⟩ :=
    g.exists_iterated_openFiber_metric_equivalence hP (hf (Fin.last k)) U hprefix hlast
  let cP := fun i : Fin k => c i.castSucc
  let t := c (Fin.last k)
  let gP := g.openRegularFiberMetric hP U hprefix cP
  let φ := f (Fin.last k) ∘ openFiberIncl P U cP
  let hφ := (hf (Fin.last k)).comp (contMDiff_openFiberIncl (m := m + 1) hP U hprefix cP)
  obtain ⟨hlevel, hdata⟩ := hiter cP t
  refine ⟨hlevel, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hφ ⊤ (fun x _ => hlevel x) m t
  let := isManifold_openLevelSet hφ ⊤ (fun x _ => hlevel x) m t
  let gIter := gP.regularLevelMetric hφ ⊤ (fun x _ => hlevel x) t
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
    m + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  let := openFiberChartedSpace (m := m) hjsmooth U hjoint (Fin.cons t cP)
  let := isManifold_openFiber (m := m) hjsmooth U hjoint (Fin.cons t cP)
  let := openFiberChartedSpace (m := m) hF U hfull c
  let := isManifold_openFiber (m := m) hF U hfull c
  let gFull := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
    (openFiberIncl F U c) (contMDiff_openFiberIncl (m := m) hF U hfull c)
    (injective_mfderiv_openFiberIncl (m := m) hF U hfull c)
  obtain ⟨e₁, he₁, _, _⟩ := hdata
  have heq : ∀ x, (x ∈ U ∧ joint x = Fin.cons t cP) ↔ (x ∈ U ∧ F x = c) := by
    intro x
    apply and_congr_right
    intro _
    constructor
    · intro he
      apply funext
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact congrFun he 0
      · exact congrFun he i.succ
    · intro he
      change Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (F x (Fin.last k)) (fun i => F x i.castSucc) =
        Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (c (Fin.last k)) (fun i => c i.castSucc)
      rw [he]
  let e₂ := openFiberDiffeomorphOfEq (m := m) hjsmooth hF hjoint hfull heq
  let e := e₁.trans e₂
  have hambient (x : openLevelSet φ ⊤ t) :
      openFiberIncl F U c (e x) = openFiberIncl P U cP (openLevelIncl φ ⊤ t x) := by
    change openFiberIncl joint U (Fin.cons t cP) (e₁.toEquiv x) = _
    rw [he₁]
    rfl
  have hmetric : ∀ (x : openLevelSet φ ⊤ t) (v w : TangentSpace (𝓡 m) x),
      gIter.inner x v w = gFull.inner (e x)
        (mfderiv (𝓡 m) (𝓡 m) e x v) (mfderiv (𝓡 m) (𝓡 m) e x w) := by
    intro x v w
    have hcomp : openFiberIncl F U c ∘ e =
        openFiberIncl P U cP ∘ openLevelIncl φ ⊤ t := funext hambient
    have hd : (mfderiv (𝓡 m) (𝓡 ((m + 1) + k)) (openFiberIncl F U c ∘ e) x :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ((m + 1) + k))) =
      mfderiv (𝓡 m) (𝓡 ((m + 1) + k))
        (openFiberIncl P U cP ∘ openLevelIncl φ ⊤ t) x := by rw [hcomp]
    rw [mfderiv_comp x
      ((contMDiff_openFiberIncl (m := m) hF U hfull c _).mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiable (by simp) x),
      mfderiv_comp x
        ((contMDiff_openFiberIncl (m := m + 1) hP U hprefix cP _).mdifferentiableAt (by simp))
        ((contMDiff_openLevelIncl hφ ⊤ (fun x _ => hlevel x) m t x).mdifferentiableAt (by simp))] at hd
    have hdv := congrArg (fun A => A v) hd
    have hdw := congrArg (fun A => A w) hd
    change g.inner (openFiberIncl P U cP (openLevelIncl φ ⊤ t x))
      (mfderiv (𝓡 (m + 1)) (𝓡 ((m + 1) + k)) (openFiberIncl P U cP) _
        (mfderiv (𝓡 m) (𝓡 (m + 1)) (openLevelIncl φ ⊤ t) x v))
      (mfderiv (𝓡 (m + 1)) (𝓡 ((m + 1) + k)) (openFiberIncl P U cP) _
        (mfderiv (𝓡 m) (𝓡 (m + 1)) (openLevelIncl φ ⊤ t) x w)) =
      g.inner (openFiberIncl F U c (e x))
        (mfderiv (𝓡 m) (𝓡 ((m + 1) + k)) (openFiberIncl F U c) _
          (mfderiv (𝓡 m) (𝓡 m) e x v))
        (mfderiv (𝓡 m) (𝓡 ((m + 1) + k)) (openFiberIncl F U c) _
          (mfderiv (𝓡 m) (𝓡 m) e x w))
    change mfderiv (𝓡 m) (𝓡 ((m + 1) + k)) (openFiberIncl F U c) _
      (mfderiv (𝓡 m) (𝓡 m) e x v) = _ at hdv
    change mfderiv (𝓡 m) (𝓡 ((m + 1) + k)) (openFiberIncl F U c) _
      (mfderiv (𝓡 m) (𝓡 m) e x w) = _ at hdw
    rw [hdv, hdw, hambient]
    rfl
  exact ⟨e, hambient,
    PoincareConjecture.RiemannianMetric.edist_eq_of_diffeomorph_metric_pullback gIter gFull e hmetric⟩
