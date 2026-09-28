import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.IntrinsicRicciTrace
import PoincareConjecture.Proofs.M60.Mathlib.ConformalTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem m60SphereRicciTraceDensity_eq_intrinsic_mul (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (hc : M60WeaklyConformal g f)
    (z : LoopPlane) :
    m60SphereRicciTraceDensity D f z =
      m60SphereIntrinsicRicciTrace D f (m60SphereParameter z) *
        (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
    ⟨m60RoundSphereMetric.toRiemannianMetric⟩
  let p := m60SphereParameter z
  let w := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  obtain ⟨R, hR⟩ := m60Ricci_exists_bilinear D hD (f p)
  let B := R.compl₁₂ (mfderiv (𝓡 2) (𝓡 n) f p).toLinearMap
    (mfderiv (𝓡 2) (𝓡 n) f p).toLinearMap
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) p) := by
    unfold TangentSpace
    infer_instance
  have hw (i j : Fin 2) : inner ℝ (w i) (w j) =
      (16 / (‖z‖ ^ 2 + 4) ^ 2) * (if i = j then 1 else 0) := by
    change m60RoundSphereInner p (w i) (w j) = _
    rw [m60SphereParameter_inner, (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_ite]
  have ht := M60.sum_bilinear_conformal_basis B
    (m60RoundSphereMetric.orthonormalBasis p) w
    (by change 2 = Module.finrank ℝ LoopPlane; simp)
    (by positivity) hw
  have hleft : m60SphereRicciTraceDensity D f z = ∑ i, B (w i) (w i) := by
    rw [m60SphereRicciTraceDensity_eq_of_weaklyConformal D hD f hf hc]
    rw [mfderiv_comp z (hf.mdifferentiable (by simp) _)
      (m60SphereParameter_contMDiff.mdifferentiable (by simp) _)]
    simp only [B, LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, hR, w, p, Function.comp_apply]
  have hright : (∑ i, B (m60RoundSphereMetric.orthonormalBasis p i)
      (m60RoundSphereMetric.orthonormalBasis p i)) = m60SphereIntrinsicRicciTrace D f p := by
    simp only [m60SphereIntrinsicRicciTrace, RiemannianMetric.tensorTrace,
      M60.tensorPullbackEvaluation, LeviCivitaData.ricciEvaluation,
      B, LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe, hR, Fin.cons_zero, Fin.cons_one]
  rw [hleft, ht, hright, mul_comm]

theorem m60SphereRicciTrace_integral_eq_intrinsic (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (hc : M60WeaklyConformal g f) :
    (∫ z : LoopPlane, m60SphereRicciTraceDensity D f z) =
      ∫ p, m60SphereIntrinsicRicciTrace D f p ∂m60RoundSphereMetric.volumeMeasure := by
  rw [m60RoundSphereMetric_integral _
    (m60SphereIntrinsicRicciTrace_contMDiff D hD f hf).continuous]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z =>
    m60SphereRicciTraceDensity_eq_intrinsic_mul D hD f (hf.of_le (by simp)) hc z

end PoincareConjecture
