import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.M04.CurvatureSymmetries
import PoincareConjecture.Proofs.M60.Mathlib.OrthonormalPairExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open Poincare.Geometry.Curvature.Operator

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem m60Ricci_plane_trace_basis (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
      D.ricci x (b 0) (b 0) + D.ricci x (b 1) (b 1) =
        D.scalarCurvature x / 2 + D.curvatureTensor x (b 0) (b 1) (b 0) (b 1) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b
  have hzero (i : Fin 3) : D.curvatureTensor x (b i) (b i) (b i) (b i) = 0 := by
    have h := M04.curvatureTensor_swap_first D x (b i) (b i) (b i) (b i)
    linarith
  have hswap (i j : Fin 3) : D.curvatureTensor x (b i) (b j) (b i) (b j) =
      D.curvatureTensor x (b j) (b i) (b j) (b i) := by
    rw [M04.curvatureTensor_swap_first, M04.curvatureTensor_swap_last, neg_neg]
  have h0 := D.ricci_eq_sum_orthonormalBasis hD x b (b 0) (b 0)
  have h1 := D.ricci_eq_sum_orthonormalBasis hD x b (b 1) (b 1)
  have hs := D.scalarCurvature_eq_twice_trace_curvatureOperator hD x b
  rw [curvatureOperator_trace] at hs
  have hs' : D.scalarCurvature x = 2 *
      (D.curvatureTensor x (b 1) (b 2) (b 1) (b 2) +
        D.curvatureTensor x (b 2) (b 0) (b 2) (b 0) +
        D.curvatureTensor x (b 0) (b 1) (b 0) (b 1)) := by
    simpa [Matrix.trace, Matrix.diag, curvatureMatrix, Fin.sum_univ_succ,
      pairFirst, pairSecond, add_assoc] using hs
  simp only [Fin.sum_univ_three, hzero, zero_add, add_zero] at h0 h1
  rw [hswap 1 0] at h1
  rw [hswap 2 0] at hs'
  linarith

theorem m60Ricci_plane_trace (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) (u v : TangentSpace (𝓡 3) x)
    (hu : g.inner x u u = 1) (hv : g.inner x v v = 1) (huv : g.inner x u v = 0) :
    D.ricci x u u + D.ricci x v v =
      D.scalarCurvature x / 2 + D.curvatureTensor x u v u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  obtain ⟨b, hb0, hb1⟩ := M60.exists_orthonormalBasis_pair
    (E := TangentSpace (𝓡 3) x)
    (by change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3; simp)
    u v hu hv huv
  simpa only [hb0, hb1] using m60Ricci_plane_trace_basis D hD x b

end PoincareConjecture
