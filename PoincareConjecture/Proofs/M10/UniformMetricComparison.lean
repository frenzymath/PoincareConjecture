import PoincareConjecture.Proofs.M10.MetricDerivativeBound
import PoincareConjecture.Proofs.M10.StaticEndpoints
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}


theorem exists_uniform_backward_metric_comparison
    (hmax : 0 < τmax) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ s ∈ Icc 0 τmax, ∀ q : M,
      ∀ v : TangentSpace (𝓡 n) q,
        (F.metric T).inner q v v ≤ Q * (F.metric (T - s)).inner q v v := by
  obtain ⟨K, hK, hbound⟩ := hcurvature.2
  let A : ℝ := 2 * (n : ℝ) ^ 3 * K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨Real.exp (A * τmax), Real.exp_pos _, ?_⟩
  intro s hs q v
  let m := fun r : ℝ ↦ (F.metric (T - r)).inner q v v
  let H := fun r : ℝ ↦ Real.exp (A * r) * m r
  have hc : ContinuousOn H (Icc 0 τmax) :=
    (by fun_prop : Continuous (fun r : ℝ ↦ Real.exp (A * r))).continuousOn.mul
      (metric_pairing_continuousOn_backward hwindow q v v)
  have hd (r : ℝ) (hr : r ∈ Ioo 0 τmax) :
      HasDerivAt H (Real.exp (A * r) *
        (A * m r + 2 * (F.connection (T - r)).ricci q v v)) r := by
    have he := ((hasDerivAt_id r).const_mul A).exp
    have hm := backward_metric_inner_hasDerivAt (F := F) hwindow hr.1 hr.2 q v v
    apply (he.mul hm).congr_deriv
    simp only [id_eq, mul_one]
    dsimp only [m]
    ring
  have hn (r : ℝ) (hr : r ∈ Ioo 0 τmax) :
      0 ≤ Real.exp (A * r) * (A * m r + 2 * (F.connection (T - r)).ricci q v v) := by
    apply mul_nonneg (Real.exp_pos _).le
    have ht : T - r ∈ Icc (T - τmax) T := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hb := abs_twice_ricci_self_le hwindow hr.1 hr.2 q
      ((le_abs_self _).trans (hbound (T - r) ht q)) v
    have hlow := (abs_le.mp hb).1
    dsimp only [A, m]
    linarith only [hlow]
  have hmono : MonotoneOn H (Icc 0 τmax) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hc
      (fun r hr ↦ (hd r (by simpa only [interior_Icc] using hr)).hasDerivWithinAt)
      (fun r hr ↦ hn r (by simpa only [interior_Icc] using hr))
  have hcomp := hmono ⟨le_rfl, hmax.le⟩ hs hs.1
  have hzero : H 0 = (F.metric T).inner q v v := by
    simp only [H, m, mul_zero, Real.exp_zero, sub_zero, one_mul]
  rw [hzero] at hcomp
  apply hcomp.trans
  apply mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hA))
  by_cases hv : v = 0
  · simp only [m, hv, map_zero, le_refl]
  · exact ((F.metric (T - s)).pos q v hv).le

end PoincareConjecture.M10
