import PoincareConjecture.Proofs.M10.PreferredFields
import PoincareConjecture.Proofs.M10.SmoothMetric
import PoincareConjecture.Proofs.M10.ProductDerivatives
import Mathlib.Analysis.Calculus.FDeriv.CompCLM









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem preferredField_coordinates (q : M) (v : TangentSpace (𝓡 n) q) {x : M}
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) q).continuousLinearMapAt
      ℝ x (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x) = v := by
  let v' : EuclideanSpace ℝ (Fin n) := v
  have he := TangentBundle.symmL_trivializationAt (I := 𝓡 n) hx
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at he
  have he' : (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) q).symmL ℝ x v =
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x := by
    simpa only [preferredField_eq_inverseChartDerivative q v hx] using!
      congrArg (fun D ↦ D (v : EuclideanSpace ℝ (Fin n))) he
  rw [← he']
  exact Bundle.Trivialization.continuousLinearMapAt_symmL _ hx v'

set_option backward.isDefEq.respectTransparency false in

theorem coordinateBackwardMetric_on_preferredFields (q : M) (τ : ℝ)
    {x : M} (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source)
    (v w : TangentSpace (𝓡 n) q) :
    coordinateBackwardMetric F T q (extChartAt (𝓡 n) q x, τ) v w =
      (F.metric (T - τ)).inner x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w x) := by
  have hx' : x ∈ (extChartAt (𝓡 n) q).source := by
    simpa only [extChartAt_source] using hx
  dsimp only [coordinateBackwardMetric]
  rw [(extChartAt (𝓡 n) q).left_inv hx']
  have h := backwardMetricCoordinates_apply (F := F) (T := T) q (x, τ) hx
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w x)
  simpa only [preferredField_coordinates q v hx, preferredField_coordinates q w hx] using h

set_option backward.isDefEq.respectTransparency false in

theorem coordinateBackwardMetric_space_derivative
    (hwindow : Icc (T - τmax) T ⊆ J) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (q : M) (u v w : TangentSpace (𝓡 n) q) :
    fderiv ℝ (coordinateBackwardMetric F T q) (extChartAt (𝓡 n) q q, τ) (u, 0) v w =
      mvfderiv (𝓡 n) (fun x ↦ (F.metric (T - τ)).inner x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w x)) q u := by
  let m : M → ℝ := fun x ↦ (F.metric (T - τ)).inner x
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w x)
  let v' : EuclideanSpace ℝ (Fin n) := v
  let w' : EuclideanSpace ℝ (Fin n) := w
  have hm : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) m q := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - τ)).toRiemannianMetric⟩
    exact (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v).inner_bundle
      (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)
  have heq : m ∘ (extChartAt (𝓡 n) q).symm =ᶠ[𝓝 (extChartAt (𝓡 n) q q)]
      (fun y ↦ coordinateBackwardMetric F T q (y, τ) v w) := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓡 n) q] with y hy
    have hx : (extChartAt (𝓡 n) q).symm y ∈
        (chartAt (EuclideanSpace ℝ (Fin n)) q).source := by
      simpa only [extChartAt_source] using (extChartAt (𝓡 n) q).map_target hy
    have h := coordinateBackwardMetric_on_preferredFields (F := F) (T := T) q τ hx v w
    rw [(extChartAt (𝓡 n) q).right_inv hy] at h
    exact h.symm
  have hB := (coordinateBackwardMetric_contDiffAt (F := F) hwindow q hτ hmax).differentiableAt
    (by simp)
  have hEval := (hB.hasFDerivAt.clm_apply
    (hasFDerivAt_const v' (extChartAt (𝓡 n) q q, τ))).clm_apply
      (hasFDerivAt_const w' (extChartAt (𝓡 n) q q, τ))
  simp only [ContinuousLinearMap.comp_zero, zero_add] at hEval
  have hs := fderiv_horizontal_eq hEval.differentiableAt u
  rw [hEval.fderiv] at hs
  simp only [ContinuousLinearMap.flip_apply] at hs
  rw [← heq.fderiv_eq, preferredChart_scalar_derivative q hm u] at hs
  exact hs

end PoincareConjecture.M10
