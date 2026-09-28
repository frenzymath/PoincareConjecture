import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Controls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace AncientKappaSolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem past_norm_le_scalar (hM04 : RicciFlowCurvatureTheory.{u})
    (hM06 : HarnackAncientTheory.{u}) (K : AncientKappaSolution n M)
    (t b : ℝ) (htb : t ≤ b) (hb : b ≤ 0) (x : M) :
    (K.flow.connection t).curvatureTensorNorm x ≤
      (K.flow.connection b).scalarCurvature x :=
  ((K.flow.connection t).curvatureTensorNorm_le_scalarCurvature_sharp
    (hM04.tensor_calculus n M _ _) x
    (K.nonnegative_curvature_operator t (htb.trans hb) x)).trans
      (K.scalar_monotone hM04 hM06 t b htb hb x)

noncomputable def structuralData (hM04 : RicciFlowCurvatureTheory.{u})
    (hM06 : HarnackAncientTheory.{u})
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (K : AncientKappaSolution n M) : AncientKappaStructuralData K where
  scalar_pos := K.scalar_pos hM04 hM06
  norm_le_scalar t ht x :=
    (K.flow.connection t).curvatureTensorNorm_le_scalarCurvature_sharp
      (hM04.tensor_calculus n M _ _) x (K.nonnegative_curvature_operator t ht x)
  scalar_le_dim_norm t _ x :=
    (K.flow.connection t).scalarCurvature_le_curvatureTensorNorm_sharp x
  ricci_nonnegative t ht x v := (K.ricci_bounds hM04 t ht x v).1
  ricci_upper_bound t ht x v := (K.ricci_bounds hM04 t ht x v).2
  scalar_derivative_nonnegative := K.scalar_derivative_nonnegative hM04 hM06
  scalar_monotone := K.scalar_monotone hM04 hM06
  metric_monotone := K.metric_monotone hM04
  edist_monotone := K.edist_monotone hM04
  ball_monotone s t hst ht x r := by
    intro y hy
    exact lt_of_le_of_lt (K.edist_monotone hM04 s t hst ht x y) hy
  past_norm_le_scalar := K.past_norm_le_scalar hM04 hM06
  fixed_set_bound b hb A C hC t ht x hx :=
    (K.past_norm_le_scalar hM04 hM06 t b ht hb x).trans (hC x hx)
  whole_past_bound b hb := by
    obtain ⟨C, hC, hbound⟩ := K.bounded_curvature b hb
    refine ⟨(n : ℝ) * C + 1, by positivity, ?_⟩
    intro t ht x
    rw [abs_of_nonneg (show 0 ≤ (K.flow.connection t).curvatureTensorNorm x from
      Real.sqrt_nonneg _)]
    calc
      _ ≤ (K.flow.connection b).scalarCurvature x :=
        K.past_norm_le_scalar hM04 hM06 t b ht hb x
      _ ≤ (n : ℝ) * (K.flow.connection b).curvatureTensorNorm x :=
        (K.flow.connection b).scalarCurvature_le_curvatureTensorNorm_sharp x
      _ ≤ (n : ℝ) * C :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hbound x)) (Nat.cast_nonneg n)
      _ ≤ (n : ℝ) * C + 1 := by linarith
  normalization p b hb := ancientKappaNormalization hM13 K p b hb
    (K.scalar_pos hM04 hM06 b hb p)

end AncientKappaSolution

theorem horizon_ancientKappaStructuralConsequences
    (n : ℕ)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hM06 : HarnackAncientTheory.{u})
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    AncientKappaStructuralConclusion.{u} n := by
  exact ⟨⟨fun _ _ _ _ _ _ _ _ _ _ K => K.structuralData hM04 hM06 hM13⟩⟩

end PoincareConjecture
