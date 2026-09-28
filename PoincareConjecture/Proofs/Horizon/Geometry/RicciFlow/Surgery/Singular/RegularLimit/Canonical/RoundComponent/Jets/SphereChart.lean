import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.SphereModel

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology InnerProductSpace
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem sphereReferenceMetric_inner_zero (v w : E) :
    sphereReferenceMetric.inner 0 v w = ⟪v, w⟫_ℝ := by
  change (16 / (‖(0 : E)‖ ^ 2 + 4) ^ 2) * ⟪v, w⟫_ℝ = ⟪v, w⟫_ℝ
  norm_num

theorem exists_centered_unit_curvature_chart
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 X} (D : LeviCivitaData g)
    (hsec : ∀ (x : X) (v w : TangentSpace (𝓡 3) x),
      LeviCivitaData.IsOrthonormalPair g x v w → D.sectionalCurvature x v w = 1)
    (x : X) :
    ∃ (U : Set E) (f : E → X), IsOpen U ∧ (0 : E) ∈ U ∧ f 0 = x ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
      (∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible) ∧
      ∀ y ∈ U, ∀ v w : E,
        sphereReferenceMetric.inner y v w = g.inner (f y)
          (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) := by
  let q : UnitSphere 3 := ⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by simp⟩
  have hsec' (y : X) (v w : TangentSpace (𝓡 3) y)
      (hn : g.inner y v v * g.inner y w w - (g.inner y v w) ^ 2 ≠ 0) :
      D.sectionalCurvature y v w = 1 :=
    D.sectionalCurvature_eq_of_orthonormal y 1
      (fun a b haa hbb hab => hsec y a b ⟨haa, hbb, hab⟩) v w hn
  obtain ⟨F, hq, hFx, hF, _, hFm⟩ := SpaceForm.exists_local_isometry_of_unit_curvature
    (roundSphereMetric 3) g (roundSphereMetric 3).leviCivitaData D
    roundSphereMetric_unit_sectionalCurvature hsec' q x
  let c := chartAt E q
  let f := F ∘ c.symm
  let U : Set E := c.symm ⁻¹' F.source
  have hU : IsOpen U := F.open_source.preimage (sphere_chart_symm_contMDiff q).continuous
  have hzero : (0 : E) ∈ U := by
    simpa only [U, mem_preimage, c, sphere_chart_symm_zero] using hq
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U :=
    hF.comp (sphere_chart_symm_contMDiff q).contMDiffOn (fun _ hy => hy)
  have hfm (y : E) (hy : y ∈ U) (v w : E) :
      sphereReferenceMetric.inner y v w = g.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) := by
    have hder := mfderiv_comp y
      ((hF.contMDiffAt (F.open_source.mem_nhds hy)).mdifferentiableAt (by simp))
      ((sphere_chart_symm_contMDiff q y).mdifferentiableAt (by simp))
    change _ = g.inner (F (c.symm y))
      (mfderiv (𝓡 3) (𝓡 3) (F ∘ c.symm) y v)
      (mfderiv (𝓡 3) (𝓡 3) (F ∘ c.symm) y w)
    rw [hder]
    have hs : sphereReferenceMetric.inner y v w = (roundSphereMetric 3).inner
        (c.symm y) (mfderiv (𝓡 3) (𝓡 3) c.symm y v)
        (mfderiv (𝓡 3) (𝓡 3) c.symm y w) :=
      (roundSphereMetric_chart_symm_inner q y v w).symm
    exact hs.trans (hFm _ hy _ _)
  have hinv (y : E) (hy : y ∈ U) : (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible := by
    have hb := sphereReferenceMetric.mfderiv_bijective_of_pullback_eq g y
      (fun u v => (hfm y hy u v).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) y) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 3) : E → Type _) _
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f y)) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 3) : X → Type _) _
    exact ⟨(LinearEquiv.ofBijective
      (mfderiv (𝓡 3) (𝓡 3) f y).toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  refine ⟨U, f, hU, hzero, ?_, hf, hinv, hfm⟩
  simpa only [f, Function.comp_apply, c, sphere_chart_symm_zero] using hFx

end PoincareConjecture.SingularRegularLimit.RoundComparison
