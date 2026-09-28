import PoincareConjecture.Proofs.M34.Mathlib.ModelTangentSection
import PoincareConjecture.Proofs.M09.PullbackExtension
import PoincareConjecture.Proofs.M09.VelocityRestriction
import Mathlib.Analysis.Calculus.ContDiff.Deriv












set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

variable {n : ℕ}



theorem model_curveVelocity_eq_deriv (alpha : ℝ → EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    curveVelocity (n := n) alpha s = deriv alpha s := by
  simp only [curveVelocity, mfderiv_eq_fderiv, deriv]
  rfl



theorem model_curveVelocity_contDiffOn {alpha : ℝ → EuclideanSpace ℝ (Fin n)}
    {O : Set ℝ} (hO : IsOpen O) (ha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha O) :
    ContDiffOn ℝ ∞ (curveVelocity (n := n) alpha) O := by
  have hv : curveVelocity (n := n) alpha = deriv alpha :=
    funext (model_curveVelocity_eq_deriv alpha)
  rw [hv]
  exact ha.contDiffOn.deriv_of_isOpen hO (m := ∞) (by simp)

set_option backward.isDefEq.respectTransparency false in


noncomputable def modelCurveVelocityExtension
    (alpha : ℝ → EuclideanSpace ℝ (Fin n)) (K O : Set ℝ)
    (hO : IsOpen O) (hKO : K ⊆ O) (hK : UniqueDiffOn ℝ K)
    (ha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha O) :
    ParametricAlongCurveExtensionOn (n := n) K alpha
      (curveVelocityWithin (n := n) alpha K) where
  extension := fun r _ => curveVelocity (n := n) alpha r
  domain := O ×ˢ univ
  open_domain := hO.prod isOpen_univ
  graph_mem := fun s hs => ⟨hKO hs, mem_univ _⟩
  smooth := by
    have hv := (model_curveVelocity_contDiffOn hO ha).contMDiffOn
    exact (contMDiff_modelTangentMk (𝓡 n) ∞).comp_contMDiffOn
      (contMDiffOn_snd.prodMk (hv.comp contMDiffOn_fst (fun _ hs => hs.1)))
  agrees := by
    intro s hs
    exact (PoincareConjecture.Proofs.M09.curveVelocityWithin_eq_curveVelocity alpha K s
      (hK s hs) ((ha.contMDiffAt (hO.mem_nhds (hKO hs))).mdifferentiableAt (by simp))).symm




theorem modelCurveVelocityExtension_covariantDerivative
    {J : Set ℝ} (F : RicciFlow n (EuclideanSpace ℝ (Fin n)) J)
    (time : ℝ → ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin n)) (K O : Set ℝ)
    (hO : IsOpen O) (hKO : K ⊆ O) (hK : UniqueDiffOn ℝ K)
    (ha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha O)
    (B : ParametricAlongCurveExtensionOn (n := n) K alpha
      (curveVelocityWithin (n := n) alpha K))
    {s : ℝ} (hs : s ∈ K) :
    pullbackCovariantDerivative F time alpha (curveVelocityWithin alpha K) K B s =
      pullbackCovariantDerivative F time alpha (curveVelocityWithin alpha K) K
        (modelCurveVelocityExtension alpha K O hO hKO hK ha) s :=
  PoincareConjecture.Proofs.M09.pullbackCovariantDerivative_extension_independent
    F time alpha _ K B _ s hs (hK s hs)
      ((ha.contMDiffAt (hO.mem_nhds (hKO hs))).mdifferentiableAt (by simp))

end PoincareConjecture.M34
