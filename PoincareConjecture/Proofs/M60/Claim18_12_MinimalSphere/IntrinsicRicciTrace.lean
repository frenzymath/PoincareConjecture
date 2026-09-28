import PoincareConjecture.Proofs.M60.Mathlib.TensorPullback
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.ConformalArea
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.ScaledRicciTrace
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.TraceRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def m60SphereIntrinsicRicciTrace (D : LeviCivitaData g)
    (f : UnitTwoSphere → M) (p : UnitTwoSphere) : ℝ :=
  m60RoundSphereMetric.tensorTrace
    (M60.tensorPullbackEvaluation (n := 2) f D.ricciEvaluation) p (fun i => Fin.elim0 i)

theorem m60SphereIntrinsicRicciTrace_contMDiff (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (m60SphereIntrinsicRicciTrace D f) := by
  have hp := M60.isSmoothCovariantTensor_pullback hD.2.1 hf
  have h := (hp.tensorTrace (g := m60RoundSphereMetric)).2 Set.univ isOpen_univ
    (fun i _ => Fin.elim0 i) (fun i => Fin.elim0 i)
  change ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p => ∑ i, D.ricci (f p)
    (mfderiv (𝓡 2) (𝓡 n) f p (m60RoundSphereMetric.orthonormalBasis p i))
    (mfderiv (𝓡 2) (𝓡 n) f p (m60RoundSphereMetric.orthonormalBasis p i)))
  simpa [contMDiffOn_univ, RiemannianMetric.tensorTrace,
    M60.tensorPullbackEvaluation, LeviCivitaData.ricciEvaluation] using h

theorem m60SphereIntrinsicRicciTrace_eq_basis (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M) (p : UnitTwoSphere) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
      ⟨m60RoundSphereMetric.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) p),
      m60SphereIntrinsicRicciTrace D f p =
        ∑ i : Fin 2, D.ricci (f p) (mfderiv (𝓡 2) (𝓡 n) f p (b i))
          (mfderiv (𝓡 2) (𝓡 n) f p (b i)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
    ⟨m60RoundSphereMetric.toRiemannianMetric⟩
  intro b
  obtain ⟨A, hA⟩ := hD.2.1.1 (f p)
  let C := A.compLinearMap (fun _ => (mfderiv (𝓡 2) (𝓡 n) f p).toLinearMap)
  have h := bilinear_sum_orthonormalBasis_eq (bilinearOfTwoTensor C)
    (m60RoundSphereMetric.orthonormalBasis p) b
  change (∑ i, D.ricci (f p)
    (mfderiv (𝓡 2) (𝓡 n) f p (m60RoundSphereMetric.orthonormalBasis p i))
    (mfderiv (𝓡 2) (𝓡 n) f p (m60RoundSphereMetric.orthonormalBasis p i))) = _
  simpa only [bilinearOfTwoTensor_apply, C, MultilinearMap.compLinearMap_apply,
    ContinuousLinearMap.coe_coe, ← hA, LeviCivitaData.ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one]
    using h

theorem m60ScalarCurvature_contMDiff (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature := by
  change ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
    (fun x => ∑ i, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
  have h := (hD.2.1.tensorTrace (g := g)).2 Set.univ isOpen_univ
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simpa [contMDiffOn_univ, RiemannianMetric.tensorTrace, LeviCivitaData.scalarCurvature,
    LeviCivitaData.ricciEvaluation] using h

noncomputable def m60SphereCurvatureContribution (D : LeviCivitaData g)
    (f : UnitTwoSphere → M) (p : UnitTwoSphere) : ℝ :=
  m60SphereIntrinsicRicciTrace D f p -
    (D.scalarCurvature (f p) / 2) * m60SphereConformalFactor g f p

theorem m60SphereCurvatureContribution_contMDiff (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (hc : M60WeaklyConformal g f) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (m60SphereCurvatureContribution D f) :=
  (m60SphereIntrinsicRicciTrace_contMDiff D hD f hf).sub
    (((m60ScalarCurvature_contMDiff D hD).comp hf).div_const 2 |>.mul
      (m60SphereConformalFactor_contMDiff g f hf hc))

theorem m60SphereCurvatureContribution_integrable (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (hc : M60WeaklyConformal g f) :
    Integrable (m60SphereCurvatureContribution D f) m60RoundSphereMetric.volumeMeasure :=
  (m60SphereCurvatureContribution_contMDiff D hD f hf hc).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end PoincareConjecture
