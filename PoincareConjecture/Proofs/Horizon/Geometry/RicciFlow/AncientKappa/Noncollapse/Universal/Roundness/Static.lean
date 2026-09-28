import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TensorCone
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Volume.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.Einstein
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open PoincareConjecture.AncientKappaRoundness
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance


theorem einstein_of_ricciComplement_mem_all_pinchingCones
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hpinch : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      ∀ c : ℝ, 1 < c → ∀ x : M,
        D.ricciComplementTensor hD x ∈ tensorPinchingCone c) :
    ∀ x, ∀ v w : TangentSpace (𝓡 3) x,
      D.ricci x v w = (D.scalarCurvature x / 3) * g.inner x v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro x
  let A := (TensorFiber.operatorTensorEquiv.symm (D.ricciComplementTensor hD x)).toLinearMap
  have hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  obtain ⟨r, hr, hA⟩ := eq_smul_id_of_mem_all_pinchingCones
    (E := TangentSpace (𝓡 3) x) hn
    (A := A) (fun c hc => hpinch c hc x)
  have hT : D.ricciComplementTensor hD x = TensorFiber.operatorTensor A := by
    exact (TensorFiber.operatorTensorEquiv.apply_symm_apply _).symm
  have heval (v w : TangentSpace (𝓡 3) x) :
      (D.scalarCurvature x / 2) * g.inner x v w - D.ricci x v w = r * g.inner x v w := by
    have h := congrArg (fun T : TensorFiber (TangentSpace (𝓡 3) x) 2 => T ![v, w]) hT
    rw [D.ricciComplementTensor_apply, hA, TensorFiber.operatorTensor_apply] at h
    change (D.scalarCurvature x / 2) * g.inner x v w - D.ricci x v w =
      g.inner x v (r • w) at h
    simpa only [map_smul, smul_eq_mul] using h
  have htrace : D.scalarCurvature x = 3 * (D.scalarCurvature x / 2 - r) := by
    change (∑ i, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x i)) = _
    have he (i) : D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x i) =
        D.scalarCurvature x / 2 - r := by
      have h := heval (g.orthonormalBasis x i) (g.orthonormalBasis x i)
      have hi : g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 :=
        (g.orthonormalBasis x).inner_eq_ite i i |>.trans (if_pos rfl)
      rw [hi] at h
      linarith
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      hn, nsmul_eq_mul]
    norm_num
  intro v w
  have hrval : r = D.scalarCurvature x / 6 := by linarith
  rw [hrval] at heval
  nlinarith [heval v w]



theorem isRoundMetricSlice_of_einstein
    [ConnectedSpace M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hop : ∀ x, D.NonnegativeCurvatureOperator x)
    (hnonflat : ∃ x, D.curvatureTensorNorm x ≠ 0)
    (hEinstein : ∀ x, ∀ v w : TangentSpace (𝓡 3) x,
      D.ricci x v w = (D.scalarCurvature x / 3) * g.inner x v w) :
    IsRoundMetricSlice D := by
  obtain ⟨R, hconst⟩ := Poincare.Manifold.exists_eq_const_of_mvfderiv_eq_zero
    (fun x => (D.contMDiff_scalarCurvature x).mdifferentiableAt (by simp))
    (D.mvfderiv_scalarCurvature_eq_zero_of_three_dimensional_einstein hD hEinstein)
  obtain ⟨p, hp⟩ := hnonflat
  have hRp : 0 < D.scalarCurvature p :=
    (lt_of_le_of_ne (show 0 ≤ D.curvatureTensorNorm p from Real.sqrt_nonneg _) hp.symm).trans_le
      (D.curvatureTensorNorm_le_scalarCurvature_sharp hD p (hop p))
  have hpositive (x : M) : 0 < D.scalarCurvature x := by
    rw [hconst x, ← hconst p]
    exact hRp
  obtain ⟨c, hc, hsec⟩ :=
    D.constantPositiveSectionalCurvature_of_three_dimensional_einstein hD hEinstein hpositive
  refine ⟨c, hc, fun x u v => ?_⟩
  exact D.curvatureTensor_diagonal_of_constant_sectional x c
    (D.sectionalCurvature_eq_of_orthonormal x c (hsec x)) u v



theorem isRoundMetricSlice_of_ricciComplement_mem_all_pinchingCones
    [ConnectedSpace M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hop : ∀ x, D.NonnegativeCurvatureOperator x)
    (hnonflat : ∃ x, D.curvatureTensorNorm x ≠ 0)
    (hpinch : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      ∀ c : ℝ, 1 < c → ∀ x : M,
        D.ricciComplementTensor hD x ∈ tensorPinchingCone c) :
    IsRoundMetricSlice D :=
  D.isRoundMetricSlice_of_einstein hD hop hnonflat
    (D.einstein_of_ricciComplement_mem_all_pinchingCones hD hpinch)

end PoincareConjecture.LeviCivitaData
