import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundMetricEllipticity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Myers.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import PoincareConjecture.Proofs.M13.Metric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30




theorem round_component_subset_normalized_ball
    {X : Type u} [TopologicalSpace X] [T3Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    {epsilon : ℝ} (A : SingularRoundComponent g epsilon)
    (hepsilon : epsilon ≤ 1 / 2)
    {Q : ℝ} (hQ : 0 < Q) {x : X} (hx : x ∈ A.carrier)
    (hhigh : 4 < D.scalarCurvature x / Q)
    (hscalar : |D.scalarCurvature x / A.scale - 6| < 1) :
    A.carrier ⊆ RiemannianMetric.ball
      (M13.scaleSmoothMetric g Q hQ) x 8 := by
  let : CompactSpace A.model.carrier := isCompact_univ_iff.mp A.model_compact
  let : ConnectedSpace A.model.carrier := connectedSpace_iff_univ.mpr A.model_connected
  have hcomplete : MetricComplete A.model_metric := by
    unfold MetricComplete
    infer_instance
  have hRic (z : A.model.carrier) (v : TangentSpace (𝓡 3) z) :
      2 * A.model_metric.inner z v v ≤ A.model_connection.ricci z v v := by
    have hconstant := A.model_connection.sectionalCurvature_eq_of_orthonormal z 1
      (fun a b haa hbb hab => A.model_curvature_one z a b ⟨haa, hbb, hab⟩)
    have heq := A.model_connection.ricci_of_constant_sectional z 1 hconstant v v
    norm_num at heq
    exact heq.ge
  have hmodel (z w : A.model.carrier) :
      A.model_metric.edist z w ≤ ENNReal.ofReal 4 := by
    apply (A.model_metric.edist_le_of_positive_ricci A.model_connection
      hcomplete (show (0 : ℝ) < 2 by norm_num) hRic z w).trans
    apply ENNReal.ofReal_le_ofReal
    exact Real.sqrt_le_iff.mpr (by norm_num)
  let r := D.scalarCurvature x / Q
  have hr : 4 < r := hhigh
  have hrpos : 0 < r := by linarith
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
  have hsqrtTwo : 2 < Real.sqrt r :=
    (Real.lt_sqrt (by norm_num)).mpr (by nlinarith)
  have hrawUpper : D.scalarCurvature x < 7 * A.scale := by
    have hh := (abs_lt.mp hscalar).2
    exact (div_lt_iff₀ A.scale_pos).mp (by linarith)
  have hratio : Q / A.scale < 7 / r := by
    apply (div_lt_div_iff₀ A.scale_pos hrpos).mpr
    have hRq : r * Q = D.scalarCurvature x := div_mul_cancel₀ _ hQ.ne'
    nlinarith
  let C := 4 / Real.sqrt r
  have hC : 0 < C := div_pos (by norm_num) hsqrt
  have hCsq : C ^ 2 = 16 / r := by
    dsimp only [C]
    rw [div_pow, Real.sq_sqrt hrpos.le]
    norm_num
  let h : RiemannianMetric 3 X := M13.scaleSmoothMetric g Q hQ
  have hbound (z : A.model.carrier) (v : TangentSpace (𝓡 3) z) :
      h.inner (A.forward z) (mfderiv (𝓡 3) (𝓡 3) A.forward z v)
        (mfderiv (𝓡 3) (𝓡 3) A.forward z v) ≤
          C ^ 2 * A.model_metric.inner z v v := by
    have hnonneg : 0 ≤ A.model_metric.inner z v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (A.model_metric.pos z v hv).le
    have hquad := (M28.tube.round_metric_quadratic_bounds A z v).2
    have hquad' : A.scale * g.inner (A.forward z)
        (mfderiv (𝓡 3) (𝓡 3) A.forward z v)
        (mfderiv (𝓡 3) (𝓡 3) A.forward z v) ≤
          2 * A.model_metric.inner z v v :=
      hquad.trans (mul_le_mul_of_nonneg_right (by linarith) hnonneg)
    have hh := mul_le_mul_of_nonneg_left hquad' (div_nonneg hQ.le A.scale_pos.le)
    have hcancel : Q / A.scale * (A.scale * g.inner (A.forward z)
        (mfderiv (𝓡 3) (𝓡 3) A.forward z v)
        (mfderiv (𝓡 3) (𝓡 3) A.forward z v)) =
          h.inner (A.forward z) (mfderiv (𝓡 3) (𝓡 3) A.forward z v)
            (mfderiv (𝓡 3) (𝓡 3) A.forward z v) := by
      change _ = Q * _
      field_simp [A.scale_pos.ne']
      rfl
    rw [hcancel] at hh
    apply hh.trans
    rw [hCsq]
    calc
      Q / A.scale * (2 * A.model_metric.inner z v v) =
          (2 * (Q / A.scale)) * A.model_metric.inner z v v := by ring
      _ ≤ (16 / r) * A.model_metric.inner z v v := by
        apply mul_le_mul_of_nonneg_right _ hnonneg
        have htwo : 0 < 2 / r := div_pos (by norm_num) hrpos
        rw [show 16 / r = 2 * (7 / r) + 2 / r by ring]
        linarith
  have hsmall : C * 4 < 8 := by
    dsimp only [C]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hsqrt).mpr
    nlinarith
  intro z hz
  change h.edist x z < ENNReal.ofReal 8
  have hd := A.model_metric.edist_le_mul_of_inner_mfderiv_le h
    (A.forward_smooth.of_le (by simp)) hC hbound (A.inverse x) (A.inverse z)
  rw [A.right_inverse hx, A.right_inverse hz] at hd
  apply (hd.trans (mul_le_mul' le_rfl (hmodel _ _))).trans_lt
  rw [← ENNReal.ofReal_mul hC.le]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hsmall

end PoincareConjecture.M30
