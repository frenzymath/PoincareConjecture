import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.ProductCircleObservation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass
import Mathlib.Analysis.InnerProductSpace.Calculus













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)




theorem unit_observation_tangent_orthogonal
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (R : E →L[ℝ] LoopPlane) (hnorm : ∀ q, ‖R (e q)‖ = 1)
    (q : M) (w : TangentSpace (𝓡 n) q) :
    inner ℝ (R (e q)) (R (mfderiv (𝓡 n) (𝓡 m) e q w)) = 0 := by
  let f := R ∘ e
  have hf : ContMDiff (𝓡 n) (𝓡 2) 1 f := R.contDiff.contMDiff.comp he
  have hchain := mfderiv_comp_apply (I := 𝓡 n) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
    (f := f) (g := fun z : LoopPlane => ‖z‖ ^ 2) q
    (hasStrictFDerivAt_norm_sq (f q)).hasFDerivAt.differentiableAt.mdifferentiableAt
    (hf.mdifferentiable (by simp) q) w
  have hconst : (fun z : LoopPlane => ‖z‖ ^ 2) ∘ f = fun _ : M => (1 : ℝ) := by
    funext p
    simp only [f, Function.comp_apply, hnorm, one_pow]
  rw [hconst, mfderiv_const, mfderiv_eq_fderiv, fderiv_norm_sq_apply] at hchain
  have hDf := mfderiv_comp_apply (f := e) (g := R) q
    R.differentiableAt.mdifferentiableAt (he.mdifferentiable (by simp) q) w
  rw [mfderiv_eq_fderiv, R.fderiv] at hDf
  change mfderiv (𝓡 n) (𝓡 2) f q w = R (mfderiv (𝓡 n) (𝓡 m) e q w) at hDf
  simp only [zero_apply, two_smul, hDf] at hchain
  change 0 = inner ℝ (R (e q)) (R (mfderiv (𝓡 n) (𝓡 m) e q w)) +
    inner ℝ (R (e q)) (R (mfderiv (𝓡 n) (𝓡 m) e q w)) at hchain
  linarith



theorem planarCircleCurrent_zero_of_tangent
    (u v w : LoopPlane) (hu : ‖u‖ = 1)
    (hv : inner ℝ u v = 0) (hw : inner ℝ u w = 0) :
    planarCircleCurrent v w = 0 := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have h : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_two, star_trivial, pow_two] using h
  have hv' : u 0 * v 0 + u 1 * v 1 = 0 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_two, star_trivial, mul_comm] using hv
  have hw' : u 0 * w 0 + u 1 * w 1 = 0 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_two, star_trivial, mul_comm] using hw
  have hid : (u 0 ^ 2 + u 1 ^ 2) * planarCircleCurrent v w =
      (u 0 * v 0 + u 1 * v 1) * planarCircleCurrent u w -
        (u 0 * w 0 + u 1 * w 1) * planarCircleCurrent u v := by
    unfold planarCircleCurrent
    ring
  simpa only [hu2, hv', hw', one_mul, zero_mul, sub_zero] using hid




theorem observedWeakAnnulus_circle_jacobian_zero
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (R : E →L[ℝ] LoopPlane) (hnorm : ∀ q, ‖R (e q)‖ = 1)
    {c0 c1 : ℝ → M} (A : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
      planarCircleCurrent (R (A.column 0 p)) (R (A.column 1 p)) = 0 := by
  filter_upwards [A.tangent 0, A.tangent 1] with p h0 h1
  obtain ⟨v, hv⟩ := h0
  obtain ⟨w, hw⟩ := h1
  apply planarCircleCurrent_zero_of_tangent (R (e (A.map p))) _ _ (hnorm _)
  · rw [← hv]
    exact unit_observation_tangent_orthogonal e he R hnorm _ v
  · rw [← hw]
    exact unit_observation_tangent_orthogonal e he R hnorm _ w

end PoincareConjecture.M64
