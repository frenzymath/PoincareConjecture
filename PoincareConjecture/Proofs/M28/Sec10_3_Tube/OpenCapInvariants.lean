import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenNeckRestriction
import PoincareConjecture.Proofs.M09.TensorTrace
import PoincareConjecture.Proofs.M14.Sec6_5_ScalarEvolutionTransportRicci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

private theorem scalar_smooth {g : RiemannianMetric 3 M} (D : LeviCivitaData g) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature :=
  Proofs.M09.tensorMetricTrace_smooth g D.ricciEvaluation
    D.normalization_curvatureTensorCalculus.2.1

theorem intrinsicOpenMetric_scalarCurvatureSupOn (g : RiemannianMetric 3 M)
    (V : TopologicalSpace.Opens M) (DV : LeviCivitaData (intrinsicOpenMetric g V))
    (D : LeviCivitaData g) {S : Set M} (hSV : S ⊆ (V : Set M)) :
    scalarCurvatureSupOn (intrinsicOpenMetric g V) DV
        ((Subtype.val : V → M) ⁻¹' S) = scalarCurvatureSupOn g D S := by
  unfold scalarCurvatureSupOn
  apply congrArg sSup
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x : V), x.property⟩,
      (intrinsicOpenMetric_scalarCurvature g V DV D x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨⟨(x : M), hSV x.property⟩, x.property⟩,
      intrinsicOpenMetric_scalarCurvature g V DV D _⟩

theorem intrinsicOpenMetric_scalarGradientNorm (g : RiemannianMetric 3 M)
    (V : TopologicalSpace.Opens M) (DV : LeviCivitaData (intrinsicOpenMetric g V))
    (D : LeviCivitaData g) (x : V) :
    scalarGradientNorm (intrinsicOpenMetric g V) DV x =
      scalarGradientNorm g D (x : M) := by
  let L : TangentSpace (𝓡 3) x ≃L[ℝ] TangentSpace (𝓡 3) (x : M) :=
    (openSubtype_isLocalDiffeomorph V).mfderivToContinuousLinearEquiv (by simp) x
  have hscalar : DV.scalarCurvature = D.scalarCurvature ∘ (Subtype.val : V → M) := by
    funext y
    exact intrinsicOpenMetric_scalarCurvature g V DV D y
  have hchain (v : TangentSpace (𝓡 3) x) :
      mvfderiv (𝓡 3) DV.scalarCurvature x v =
        mvfderiv (𝓡 3) D.scalarCurvature (x : M) (L v) := by
    rw [hscalar, mvfderiv_comp x
      ((scalar_smooth D).mdifferentiable (by simp) (x : M))
      ((openSubtype_isLocalDiffeomorph V).contMDiff.mdifferentiable (by simp) x)]
    rfl
  unfold scalarGradientNorm
  apply congrArg sSup
  ext a
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨⟨L v, v.property⟩, ?_⟩
    exact congrArg abs (hchain v).symm
  · rintro ⟨v, rfl⟩
    have hunit : (intrinsicOpenMetric g V).inner x (L.symm v) (L.symm v) = 1 := by
      change g.inner (x : M) (L (L.symm v)) (L (L.symm v)) = 1
      simpa only [L.apply_symm_apply] using v.property
    refine ⟨⟨L.symm v, hunit⟩, ?_⟩
    change |mvfderiv (𝓡 3) DV.scalarCurvature x (L.symm v)| =
      |mvfderiv (𝓡 3) D.scalarCurvature (x : M) v|
    rw [hchain, L.apply_symm_apply]

theorem intrinsicOpenMetric_ricciNormSq (g : RiemannianMetric 3 M)
    (V : TopologicalSpace.Opens M) (DV : LeviCivitaData (intrinsicOpenMetric g V))
    (D : LeviCivitaData g) (x : V) : DV.ricciNormSq x = D.ricciNormSq (x : M) := by
  exact M14.ricciNormSq_eq_of_local_isometry DV D isOpen_univ
    (contMDiff_subtype_val (I := 𝓡 3) (U := V)).contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem intrinsicOpenMetric_scalarLaplacian (g : RiemannianMetric 3 M)
    (V : TopologicalSpace.Opens M) (DV : LeviCivitaData (intrinsicOpenMetric g V))
    (D : LeviCivitaData g) (x : V) :
    DV.laplacian DV.scalarCurvature x = D.laplacian D.scalarCurvature (x : M) := by
  have hscalar : DV.scalarCurvature = D.scalarCurvature ∘ (Subtype.val : V → M) := by
    funext y
    exact intrinsicOpenMetric_scalarCurvature g V DV D y
  have hinv (y : V) :
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → M) y).IsInvertible := by
    rw [← (openSubtype_isLocalDiffeomorph V).mfderivToContinuousLinearEquiv_coe
      (by simp) y]
    exact ContinuousLinearMap.isInvertible_equiv
  rw [hscalar]
  exact DV.laplacian_comp_of_metric_pullback D
    ((openSubtype_isLocalDiffeomorph V).contMDiff x)
    (Eventually.of_forall hinv) (Eventually.of_forall (fun _ _ _ => rfl))
    (scalar_smooth D (x : M))

end PoincareConjecture.M28
