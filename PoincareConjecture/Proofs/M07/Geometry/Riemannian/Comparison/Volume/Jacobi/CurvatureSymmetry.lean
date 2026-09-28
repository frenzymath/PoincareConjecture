import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.CurvatureTrace

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter VectorField

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem connection_torsion_difference (D : LeviCivitaData g)
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (v : TangentSpace (𝓡 n) x) :
    D.connection (D.covariantDerivativeOnFields X Y) x v -
      D.connection (D.covariantDerivativeOnFields Y X) x v =
        D.connection (mlieBracket (𝓡 n) X Y) x v := by
  have hXY := D.contMDiffAt_covariantDerivativeOnFields hX hY
  have hYX := D.contMDiffAt_covariantDerivativeOnFields hY hX
  have heq : D.covariantDerivativeOnFields X Y - D.covariantDerivativeOnFields Y X =ᶠ[𝓝 x]
      mlieBracket (𝓡 n) X Y := by
    filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hX,
      eventually_mdifferentiableAt_of_contMDiffAt hY] with y hyX hyY
    exact D.covariantDerivativeOnFields_sub_swap hyX hyY
  have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((hXY.sub_section hYX).mdifferentiableAt (by simp))
    ((contMDiffAt_mlieBracket hX hY).mdifferentiableAt (by simp)) (by simp) heq
  rw [D.connection_sub (hXY.mdifferentiableAt (by simp))
    (hYX.mdifferentiableAt (by simp))] at hc
  exact congrArg (fun L => L v) hc

theorem curvatureOnFields_cyclic_eq_zero_local (D : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    D.curvatureOnFields X Y Z x + D.curvatureOnFields Y Z X x +
      D.curvatureOnFields Z X Y x = 0 := by
  have d1 := connection_torsion_difference D hY hZ (X x)
  have d2 := connection_torsion_difference D hZ hX (Y x)
  have d3 := connection_torsion_difference D hX hY (Z x)
  have t1 := D.covariantDerivativeOnFields_sub_swap (hX.mdifferentiableAt (by simp))
    ((contMDiffAt_mlieBracket hY hZ).mdifferentiableAt (by simp))
  have t2 := D.covariantDerivativeOnFields_sub_swap (hY.mdifferentiableAt (by simp))
    ((contMDiffAt_mlieBracket hZ hX).mdifferentiableAt (by simp))
  have t3 := D.covariantDerivativeOnFields_sub_swap (hZ.mdifferentiableAt (by simp))
    ((contMDiffAt_mlieBracket hX hY).mdifferentiableAt (by simp))
  have : IsManifold (𝓡 n) (minSmoothness ℝ 3) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 3 M)
  have hj := leibniz_identity_mlieBracket_apply (I := 𝓡 n)
    (hX.of_le (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast))
    (hY.of_le (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast))
    (hZ.of_le (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast))
  have hn : mlieBracket (𝓡 n) Y (mlieBracket (𝓡 n) X Z) x =
      -mlieBracket (𝓡 n) Y (mlieBracket (𝓡 n) Z X) x := by
    rw [mlieBracket_swap (V := X) (W := Z)]
    rw [show -mlieBracket (𝓡 n) Z X = (-1 : ℝ) • mlieBracket (𝓡 n) Z X by simp]
    rw [mlieBracket_const_smul_right
      ((contMDiffAt_mlieBracket hZ hX).mdifferentiableAt (by simp))]
    simp
  rw [hn, mlieBracket_swap_apply (V := mlieBracket (𝓡 n) X Y) (W := Z)] at hj
  unfold covariantDerivativeOnFields at d1 d2 d3 t1 t2 t3
  unfold curvatureOnFields
  linear_combination (norm := abel) d1 + d2 + d3 + t1 + t2 + t3 + hj

theorem curvature_cyclic_eq_zero (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w + D.curvature x v w u + D.curvature x w u v = 0 := by
  exact D.curvatureOnFields_cyclic_eq_zero_local
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)

theorem inner_radialCurvature_symm (D : LeviCivitaData g) (x : M)
    (v u w : TangentSpace (𝓡 n) x) :
    g.inner x (D.radialCurvature x v u) w =
      g.inner x u (D.radialCurvature x v w) := by
  have hb := congrArg (fun z => g.inner x z v) (D.curvature_cyclic_eq_zero x u v w)
  simp only [map_add, add_apply, map_zero, zero_apply] at hb
  change D.curvatureTensor x u v w v = g.inner x u (D.curvature x w v v)
  rw [g.symm x u]
  change D.curvatureTensor x u v w v = D.curvatureTensor x w v u v
  change D.curvatureTensor x u v v w + D.curvatureTensor x v w v u +
    D.curvatureTensor x w u v v = 0 at hb
  rw [D.curvatureTensor_swap_last x u v v w,
    D.curvatureTensor_swap_first x v w v u,
    D.curvatureTensor_swap_last x w v v u,
    D.curvatureTensor_zero_last] at hb
  linarith

end PoincareConjecture.LeviCivitaData
