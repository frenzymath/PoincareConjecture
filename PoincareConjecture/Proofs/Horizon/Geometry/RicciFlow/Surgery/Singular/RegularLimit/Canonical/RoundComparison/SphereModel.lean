import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.LocalTransport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Round
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Transition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.Definitions








noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators InnerProductSpace
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private def spherePoint : UnitSphere 3 :=
  ⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by simp⟩

private def sphereCoefficients (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  (16 / (‖x‖ ^ 2 + 4) ^ 2) • innerSL ℝ

private theorem sphereCoefficients_smooth : ContDiff ℝ ∞ sphereCoefficients := by
  let : IsBoundedSMul ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := NormedSpace.toIsBoundedSMul
        (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
  have hs : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) =>
      16 / (‖x‖ ^ 2 + 4) ^ 2) :=
    contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
      (fun x => by positivity)
  exact hs.smul contDiff_const


def sphereReferenceMetric : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)) :=
  RiemannianMetric.ofEuclideanCoefficients sphereCoefficients sphereCoefficients_smooth
    (fun x v w => by change _ * ⟪v, w⟫_ℝ = _ * ⟪w, v⟫_ℝ; rw [real_inner_comm])
    (fun x v hv => by
      change 0 < (16 / (‖x‖ ^ 2 + 4) ^ 2) * ⟪v, v⟫_ℝ
      exact mul_pos (by positivity) (real_inner_self_pos.mpr hv))

private theorem sphereReferenceMetric_pullback (q : UnitSphere 3)
    (x v w : EuclideanSpace ℝ (Fin 3)) :
    sphereReferenceMetric.inner x v w = (roundSphereMetric 3).inner
      ((chartAt (EuclideanSpace ℝ (Fin 3)) q).symm x)
      (mfderiv (𝓡 3) (𝓡 3) (chartAt (EuclideanSpace ℝ (Fin 3)) q).symm x v)
      (mfderiv (𝓡 3) (𝓡 3) (chartAt (EuclideanSpace ℝ (Fin 3)) q).symm x w) :=
  (roundSphereMetric_chart_symm_inner q x v w).symm

theorem sphereReferenceMetric_scalar : sphereReferenceMetric.leviCivitaData.scalarCurvature 0 = 6 := by
  have he := sphereReferenceMetric.leviCivitaData.scalarCurvature_eq_of_local_isometry
    (roundSphereMetric 3).leviCivitaData isOpen_univ
    (sphere_chart_symm_contMDiff spherePoint).contMDiffOn
    (fun x _ v w => sphereReferenceMetric_pullback spherePoint x v w)
    (mem_univ (0 : EuclideanSpace ℝ (Fin 3)))
  rw [he]
  have hs := (roundSphereMetric 3).leviCivitaData.scalarCurvature_of_constant_sectional
    ((chartAt (EuclideanSpace ℝ (Fin 3)) spherePoint).symm 0) 1
    (roundSphereMetric_unit_sectionalCurvature _)
  norm_num at hs
  exact hs


def roundScalarTolerance : ℝ :=
  scalarTolerance sphereReferenceMetric.leviCivitaData 0 (α := 1) (by norm_num)

theorem roundScalarTolerance_pos : 0 < roundScalarTolerance :=
  scalarTolerance_pos sphereReferenceMetric.leviCivitaData 0 (by norm_num)



theorem scalar_close_of_unit_curvature
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g h : RiemannianMetric 3 M} (D : LeviCivitaData g) (DH : LeviCivitaData h)
    (hsec : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      LeviCivitaData.IsOrthonormalPair g x v w → D.sectionalCurvature x v w = 1)
    (x : M)
    (hclose : ∀ r : ℕ, r ≤ 2 → g.tensorNorm
      (D.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
          h.inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r) x < roundScalarTolerance) :
    |DH.scalarCurvature x - 6| < 1 := by
  have hsec' (y : M) (v w : TangentSpace (𝓡 3) y)
      (hn : g.inner y v v * g.inner y w w - (g.inner y v w) ^ 2 ≠ 0) :
      D.sectionalCurvature y v w = 1 :=
    D.sectionalCurvature_eq_of_orthonormal y 1
      (fun a b haa hbb hab => hsec y a b ⟨haa, hbb, hab⟩) v w hn
  obtain ⟨F, hq, hFx, hF, _, hFm⟩ := SpaceForm.exists_local_isometry_of_unit_curvature
    (roundSphereMetric 3) g (roundSphereMetric 3).leviCivitaData D
    roundSphereMetric_unit_sectionalCurvature hsec' spherePoint x
  let c := chartAt (EuclideanSpace ℝ (Fin 3)) spherePoint
  let f := F ∘ c.symm
  let U : Set (EuclideanSpace ℝ (Fin 3)) := c.symm ⁻¹' F.source
  have hU : IsOpen U := F.open_source.preimage
    (sphere_chart_symm_contMDiff spherePoint).continuous
  have hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ U := by
    simpa only [U, mem_preimage, c, sphere_chart_symm_zero] using hq
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U :=
    hF.comp (sphere_chart_symm_contMDiff spherePoint).contMDiffOn (fun _ hy => hy)
  have hfm (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U)
      (v w : EuclideanSpace ℝ (Fin 3)) :
      sphereReferenceMetric.inner y v w = g.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) := by
    have hder := mfderiv_comp y
      ((hF.contMDiffAt (F.open_source.mem_nhds hy)).mdifferentiableAt (by simp))
      ((sphere_chart_symm_contMDiff spherePoint y).mdifferentiableAt (by simp))
    change _ = g.inner (F (c.symm y))
      (mfderiv (𝓡 3) (𝓡 3) (F ∘ c.symm) y v)
      (mfderiv (𝓡 3) (𝓡 3) (F ∘ c.symm) y w)
    rw [hder]
    exact (sphereReferenceMetric_pullback spherePoint y v w).trans (hFm _ hy _ _)
  have hinv (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
      (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible := by
    have hb := sphereReferenceMetric.mfderiv_bijective_of_pullback_eq g y
      (fun u v => (hfm y hy u v).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) y) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : EuclideanSpace ℝ (Fin 3) → Type _) _
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f y)) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : M → Type _) _
    exact ⟨(LinearEquiv.ofBijective
      (mfderiv (𝓡 3) (𝓡 3) f y).toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  have hfzero : f 0 = x := by simpa only [f, Function.comp_apply, c,
    sphere_chart_symm_zero] using hFx
  have he := scalar_control_of_local_isometry sphereReferenceMetric.leviCivitaData 0
    (by norm_num : (0 : ℝ) < 1) D DH hU hzero hf hinv hfm
    (fun r hr => by simpa only [hfzero, roundScalarTolerance] using hclose r hr)
  simpa only [hfzero, sphereReferenceMetric_scalar] using he

end PoincareConjecture.SingularRegularLimit.RoundComparison
