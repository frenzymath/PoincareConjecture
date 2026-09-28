import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberEquiv
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberComplete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology
namespace PoincareConjecture.RiemannianMetric
variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M] [IsManifold (𝓡 (m+k)) ∞ M]
  {f : M → Fin k → ℝ} (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ f)
  (U : Opens M) (hreg : ∀ x ∈ U,
    Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) f x)) (v : Fin k → ℝ)
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem openRegularFiberMetric_rescaledMetric
    (g : RiemannianMetric (m+k) M) (a : ℝ) (ha : 0<a) :
    letI := openFiberChartedSpace (m := m) hf U hreg v
    letI := isManifold_openFiber (m := m) hf U hreg v
    openRegularFiberMetric hf U hreg v (rescaledMetric g a ha) =
      rescaledMetric (openRegularFiberMetric hf U hreg v g) a ha := by
  rfl

theorem openRegularFiberMetric_rescaledMetric_edist
    (g : RiemannianMetric (m+k) M) (a : ℝ) (ha : 0<a)
    (x y : openFiber f U v) :
    letI := openFiberChartedSpace (m := m) hf U hreg v
    letI := isManifold_openFiber (m := m) hf U hreg v
    (openRegularFiberMetric hf U hreg v (rescaledMetric g a ha)).edist x y =
      ENNReal.ofReal (Real.sqrt a) * (openRegularFiberMetric hf U hreg v g).edist x y := by
  let := openFiberChartedSpace (m := m) hf U hreg v
  let := isManifold_openFiber (m := m) hf U hreg v
  rw [openRegularFiberMetric_rescaledMetric]
  exact rescaledMetric_edist _ a ha x y
end PoincareConjecture.RiemannianMetric

theorem PoincareConjecture.RiemannianMetric.exists_scaled_openFiber_metric_equivalence
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
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
            PoincareConjecture.MetricComplete gOld ∧ PoincareConjecture.MetricComplete gNew) := by
  let F := fun x => Real.sqrt a • f x
  let w := Real.sqrt a • v
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F :=
    (show ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (fun _ : M => Real.sqrt a)
      from contMDiff_const).smul hf
  have hregF : ∀ x ∈ U, Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) F x) := by
    intro x hx
    exact surjective_mfderiv_const_smul ((hf x).mdifferentiableAt (by simp))
      (hreg x hx) hs
  refine ⟨hF,hregF,?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg v
  let := isManifold_openFiber (m := m) hf U hreg v
  let := openFiberChartedSpace (m := m) hF U hregF w
  let := isManifold_openFiber (m := m) hF U hregF w
  let gOld := openRegularFiberMetric hf U hreg v g
  let gNew := openRegularFiberMetric hF U hregF w (rescaledMetric g a ha)
  have hfib (x : M) : F x = w ↔ f x = v := by
    constructor
    · intro he
      funext i
      apply mul_left_cancel₀ hs
      exact congrFun he i
    · intro he
      dsimp [F,w]
      rw [he]
  have he (x : M) : (x ∈ U ∧ f x=v) ↔ (x ∈ U ∧ F x=w) :=
    and_congr_right fun _ => (hfib x).symm
  let e := openFiberDiffeomorphOfEq (m := m) hf hF hreg hregF he
  refine ⟨e,fun _ => rfl,?_,?_,?_⟩
  · intro x z z'
    have hm := openRegularFiberMetric_inner_equivOfEq hf hF hreg hregF he
      (rescaledMetric g a ha) x z z'
    change gNew.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x z)
      (mfderiv (𝓡 m) (𝓡 m) e x z') = _
    exact hm.symm
  · intro x y
    calc
      _ = (openRegularFiberMetric hf U hreg v (rescaledMetric g a ha)).edist x y :=
        openRegularFiberMetric_edist_equivOfEq hf hF hreg hregF he
          (rescaledMetric g a ha) x y
      _ = _ := openRegularFiberMetric_rescaledMetric_edist hf U hreg v g a ha x y
  · intro hc hfull
    refine ⟨metricComplete_openRegularFiberMetric_of_fullFiber hf U hreg v g hc hfull, ?_⟩
    apply metricComplete_openRegularFiberMetric_of_fullFiber hF U hregF w
      (rescaledMetric g a ha) (metricComplete_rescaledMetric g a ha hc)
    intro x hx
    exact hfull ((hfib x).mp hx)
