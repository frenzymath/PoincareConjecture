import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative
import PoincareConjecture.Proofs.M35.RadialGauge.JointSuccessor

set_option autoImplicit false

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open DeTurckDomainRegularityNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem continuousLinearMap_eq_coordinate_sum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p : V →L[ℝ] F) :
    p = ∑ i, (EuclideanSpace.proj i).smulRight
      (p (EuclideanSpace.single i (1 : ℝ))) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro i
  simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]

theorem schwartz_fderiv_eq_coordinate_sum (φ : 𝓢(V, ℝ)) (x : V) :
    fderiv ℝ φ x = ∑ i, (EuclideanSpace.proj i).smulRight
      (orderedSchwartzDerivative [i] φ x) := by
  simpa only [orderedSchwartzDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
    continuousLinearMap_eq_coordinate_sum (fderiv ℝ φ x)

theorem orderedSchwartzDerivative_fderiv_eq_coordinate_sum
    (w : List (Fin n)) (φ : 𝓢(V, ℝ)) (x : V) :
    fderiv ℝ (orderedSchwartzDerivative w φ) x =
      ∑ i, (EuclideanSpace.proj i).smulRight (orderedSchwartzDerivative (i :: w) φ x) := by
  simpa only [orderedSchwartzDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
    continuousLinearMap_eq_coordinate_sum (fderiv ℝ (orderedSchwartzDerivative w φ) x)

theorem contDiffOn_orderedSchwartzDerivative_of_mixed_jets
    {J : Set ℝ} (hJ : IsOpen J) (φ : ℕ → ℝ → 𝓢(V, ℝ))
    (hc : ∀ j w, ContinuousOn
      (fun p : ℝ × V => orderedSchwartzDerivative w (φ j p.1) p.2) (J ×ˢ univ))
    (ht : ∀ j w t, t ∈ J → ∀ x,
      HasDerivAt (fun s => orderedSchwartzDerivative w (φ j s) x)
        (orderedSchwartzDerivative w (φ (j + 1) t) x) t)
    (j : ℕ) (w : List (Fin n)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => orderedSchwartzDerivative w (φ j p.1) p.2)
      (J ×ˢ univ) := by
  have hall (k : ℕ) : ∀ j w, ContDiffOn ℝ k
      (fun p : ℝ × V => orderedSchwartzDerivative w (φ j p.1) p.2) (J ×ˢ univ) := by
    induction k with
    | zero =>
      intro j w
      exact contDiffOn_zero.mpr (hc j w)
    | succ k ih =>
      intro j w
      have hdu : ContDiffOn ℝ k
          (fun p : ℝ × V => fderiv ℝ (orderedSchwartzDerivative w (φ j p.1)) p.2)
          (J ×ˢ univ) := by
        have hs : ContDiffOn ℝ k
            (fun p : ℝ × V => ∑ i : Fin n, (EuclideanSpace.proj i : V →L[ℝ] ℝ).smulRight
              (orderedSchwartzDerivative (i :: w) (φ j p.1) p.2)) (J ×ˢ univ) := by
          apply ContDiffOn.sum
          intro i _
          have hlin := ((ContinuousLinearMap.smulRightL ℝ V ℝ)
            (EuclideanSpace.proj i)).contDiff (n := (k : ℕ))
          exact hlin.comp_contDiffOn (ih j (i :: w))
        exact hs.congr (fun p _ =>
          orderedSchwartzDerivative_fderiv_eq_coordinate_sum w (φ j p.1) p.2)
      exact RadialGauge.joint_contDiffOn_succ_of_partials hJ k
        (fun t _ => (orderedSchwartzDerivative w (φ j t)).differentiable)
        (ht j w) (ih (j + 1) w) hdu
  exact contDiffOn_infty.mpr (fun k => hall k j w)

theorem contDiffOn_schwartz_family_of_mixed_jets
    {J : Set ℝ} (hJ : IsOpen J) (φ : ℕ → ℝ → 𝓢(V, ℝ))
    (hc : ∀ j w, ContinuousOn
      (fun p : ℝ × V => orderedSchwartzDerivative w (φ j p.1) p.2) (J ×ˢ univ))
    (ht : ∀ j w t, t ∈ J → ∀ x,
      HasDerivAt (fun s => orderedSchwartzDerivative w (φ j s) x)
        (orderedSchwartzDerivative w (φ (j + 1) t) x) t)
    (j : ℕ) : ContDiffOn ℝ ∞ (fun p : ℝ × V => φ j p.1 p.2) (J ×ˢ univ) :=
  contDiffOn_orderedSchwartzDerivative_of_mixed_jets hJ φ hc ht j []

end PoincareConjecture.M35.Uniqueness.Heat
