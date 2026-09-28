import PoincareConjecture.Definitions.M33RegularHistory
import PoincareConjecture.Definitions.Ch16.ControlledSurgery
import PoincareConjecture.Proofs.M04.TensorMetricTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

namespace M48

theorem scalarCurvature_smooth {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature := by
  have h := M04.contMDiffOn_tensorTraceLast g (k := 0)
    (M04.isSmoothCovariantTensor_ricciEvaluation D) isOpen_univ
    (V := fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
  have htrace (x : M) (v : Fin 0 → TangentSpace (𝓡 n) x) :
      M04.tensorTraceLast g D.ricciEvaluation x v = D.scalarCurvature x := by
    have hv : v = Fin.elim0 := funext fun i => Fin.elim0 i
    rw [hv]
    simp [M04.tensorTraceLast, LeviCivitaData.ricciEvaluation,
      LeviCivitaData.scalarCurvature]
  simpa only [htrace, contMDiffOn_univ] using h

theorem scalarGradient_range_bddAbove {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (x : M) :
    BddAbove (range (fun v : {v : TangentSpace (𝓡 3) x // g.inner x v v = 1} =>
      |mvfderiv (𝓡 3) D.scalarCurvature x v.1|)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine ⟨‖mvfderiv (𝓡 3) D.scalarCurvature x‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  have hv : ‖v.1‖ = 1 := by
    rw [norm_eq_sqrt_real_inner]
    change Real.sqrt (g.inner x v.1 v.1) = 1
    rw [v.2, Real.sqrt_one]
  simpa only [Real.norm_eq_abs, hv, mul_one] using
    (mvfderiv (𝓡 3) D.scalarCurvature x).le_opNorm v.1

theorem scalar_direction_le_gradient {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 3) x) (hv : g.inner x v v = 1) :
    |mvfderiv (𝓡 3) D.scalarCurvature x v| ≤ scalarGradientNorm g D x :=
  le_csSup (scalarGradient_range_bddAbove g D x) ⟨⟨v, hv⟩, rfl⟩

end M48

namespace M33RegularHistoryData

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W)

theorem scalar_gradient {J : Set ℝ} {r C : ℝ}
    (hJ : H.generalized.interval ⊆ J)
    (analytic : SurgeryHighCurvatureAnalyticOn F J r C)
    (t : ℝ) (ht : t ∈ H.generalized.interval)
    (x : (H.generalized.slice t).carrier)
    (hQ : r⁻¹ ^ 2 ≤ (H.generalized.connection t).scalarCurvature x)
    (v : TangentSpace (𝓡 3) x) (hv : (H.generalized.metric t).inner x v v = 1) :
    |mvfderiv (𝓡 3) (H.generalized.connection t).scalarCurvature x v| ≤
      C * (H.generalized.connection t).scalarCurvature x ^ (3 / 2 : ℝ) := by
  let f := H.history.forward t ht
  let w := mfderiv (𝓡 3) (𝓡 3) f x v
  have hw : (F.metric t).inner (f x) w w = 1 :=
    (H.history.metric_pullback t ht x v v).trans hv
  have hscalar : (F.connection t).scalarCurvature ∘ f =
      (H.generalized.connection t).scalarCurvature :=
    funext (H.scalar_pullback t ht)
  have hderiv := mvfderiv_comp_apply x
    ((M48.scalarCurvature_smooth (F.connection t)).mdifferentiable (by simp) (f x))
    ((H.history.forward_smooth t ht).mdifferentiable (by simp) x) v
  rw [hscalar] at hderiv
  rw [hderiv]
  apply (M48.scalar_direction_le_gradient (F.metric t) (F.connection t) (f x) w hw).trans
  have hactual : r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature (f x) := by
    simpa only [f, H.scalar_pullback] using hQ
  simpa only [f, H.scalar_pullback] using
    (analytic t (hJ ht) (W.time_subset (H.interval_eq ▸ ht)) (f x) hactual).1

theorem pinched_at (t : ℝ) (ht : t ∈ H.generalized.interval)
    (h : SurgeryPinchedAt (F.connection t) t) :
    SurgeryPinchedAt (H.generalized.connection t) t := by
  refine ⟨h.1, ?_, ?_⟩
  · intro x _
    simpa only [H.scalar_pullback] using h.2.1 (H.history.forward t ht x) (mem_univ _)
  · intro x _ hx
    have hy : 0 < (F.connection t).negativeCurvaturePart (H.history.forward t ht x) := by
      simpa only [H.negative_part_pullback] using hx
    simpa only [H.scalar_pullback, H.negative_part_pullback] using
      h.2.2 (H.history.forward t ht x) (mem_univ _) hy

theorem scalar_lower_bound (t : ℝ) (ht : t ∈ H.generalized.interval)
    (h : SurgeryPinchedAt (F.connection t) t) (x : (H.generalized.slice t).carrier) :
    -6 ≤ (H.generalized.connection t).scalarCurvature x := by
  have hpinch := (H.pinched_at t ht h).2.1 x (mem_univ _)
  have hclock : 0 < 1 + 4 * t := by linarith [h.1]
  have hquot : -6 ≤ (-6 : ℝ) / (1 + 4 * t) := by
    apply (le_div_iff₀ hclock).2
    nlinarith [h.1]
  exact hquot.trans hpinch

end M33RegularHistoryData

end PoincareConjecture
