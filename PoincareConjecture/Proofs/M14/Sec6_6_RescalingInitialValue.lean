import PoincareConjecture.Proofs.M14.Sec6_6_RescalingInitialVelocity
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingEuler
import PoincareConjecture.Proofs.M14.Sec6_2_EulerEquation
import PoincareConjecture.Proofs.M14.Sec6_2_SquareEulerReverse

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hCoordinates : M12MetricPredecessors.{0} n)
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

private theorem initialValuePath_iff_data {S : GeneralizedLGeometryTransport n X time I}
    {T b τ : ℝ} {x y : S.Point} {Z : S.Horizontal x} (hb : b = 0) :
    Nonempty (M14SquareRootInitialValuePath S T τ x y Z) ↔
      ∃ p : M14BackwardPath S T b τ x y,
        ∃ R : M14SquareRootPath S p,
        ∃ E : M14PullbackExtension S R.curve (M14SqrtParameterInterval b τ)
            R.horizontal_velocity,
          (∀ s ∈ M14SqrtParameterInterval b τ, ∀ W,
            M14SquareRootEulerResidual S R E s W = 0) ∧
          ∃ h : R.curve 0 = x, h ▸ R.horizontal_velocity 0 = (2 : ℝ) • Z := by
  subst b
  constructor
  · rintro ⟨P⟩
    exact ⟨P.path, P.square_path, P.extension, P.euler, P.initial_velocity⟩
  · rintro ⟨p, R, E, he, hv⟩
    exact ⟨{ path := p, square_path := R, extension := E, euler := he, initial_velocity := hv }⟩

include hCoordinates in

theorem rescalingInitialValuePath
    {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}
    (P : M14SquareRootInitialValuePath G T τ x y Z) :
    Nonempty (M14SquareRootInitialValuePath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x y (rescalingInitialEquiv G.spacetime Q hQ a x Z)) := by
  let p := rescalingPath hM12 hM13 G Q hQ a P.path
  let R := rescalingSquarePath hM12 hM13 G Q hQ a P.square_path
  obtain ⟨F⟩ := exists_backwardVelocity_extension_of_square P.square_path
  have hF := eulerEquation_of_squareRootEuler hM12 P.square_path P.extension P.euler F
  let F' := rescalingPathExtension hM12 hM13 G Q hQ a P.path F
  have hF' := rescalingEulerEquation hM12 hM13 G Q hQ a P.path F hF
  obtain ⟨E⟩ := exists_squareRoot_velocity_extension R
  have he : ∀ s ∈ M14SqrtParameterInterval (Q * 0) (Q * τ), ∀ W,
      M14SquareRootEulerResidual (rescalingTransport hM12 hM13 G Q hQ a) R E s W = 0 :=
    fun _ hs W => squareRootEulerResidual_eq_zero_of_euler p hCoordinates hM12 F' hF' R E hs W
  have hv := rescalingSquare_initial_vector hM12 hM13 G Q hQ a P R
  have hdata : ∃ p' : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * 0) (Q * τ) x y,
      ∃ R' : M14SquareRootPath (rescalingTransport hM12 hM13 G Q hQ a) p',
      ∃ E' : M14PullbackExtension (rescalingTransport hM12 hM13 G Q hQ a) R'.curve
        (M14SqrtParameterInterval (Q * 0) (Q * τ)) R'.horizontal_velocity,
        (∀ s ∈ M14SqrtParameterInterval (Q * 0) (Q * τ), ∀ W,
          M14SquareRootEulerResidual (rescalingTransport hM12 hM13 G Q hQ a) R' E' s W = 0) ∧
        ∃ h : R'.curve 0 = x,
          h ▸ R'.horizontal_velocity 0 = (2 : ℝ) • rescalingInitialEquiv G.spacetime Q hQ a x Z :=
    ⟨p, R, E, he, hv⟩
  exact (initialValuePath_iff_data (mul_zero Q)).mpr hdata

include hCoordinates in

theorem rescalingInitialValuePath_inverse
    {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}
    (P : M14SquareRootInitialValuePath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x y (rescalingInitialEquiv G.spacetime Q hQ a x Z)) :
    Nonempty (M14SquareRootInitialValuePath G T τ x y Z) := by
  have hdata : ∃ p : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * 0) (Q * τ) x y,
      ∃ R : M14SquareRootPath (rescalingTransport hM12 hM13 G Q hQ a) p,
      ∃ E : M14PullbackExtension (rescalingTransport hM12 hM13 G Q hQ a) R.curve
        (M14SqrtParameterInterval (Q * 0) (Q * τ)) R.horizontal_velocity,
        (∀ s ∈ M14SqrtParameterInterval (Q * 0) (Q * τ), ∀ W,
          M14SquareRootEulerResidual (rescalingTransport hM12 hM13 G Q hQ a) R E s W = 0) ∧
        ∃ h : R.curve 0 = x,
          h ▸ R.horizontal_velocity 0 = (2 : ℝ) • rescalingInitialEquiv G.spacetime Q hQ a x Z := by
    exact (initialValuePath_iff_data (mul_zero Q)).mp ⟨P⟩
  obtain ⟨p, R, E, he, hv⟩ := hdata
  let p' := rescalingPathInverse hM12 hM13 G Q hQ a p
  let R' := rescalingSquarePathInverse hM12 hM13 G Q hQ a R
  obtain ⟨F'⟩ := exists_backwardVelocity_extension_of_square R'
  obtain ⟨F⟩ := exists_backwardVelocity_extension_of_square R
  have hF := eulerEquation_of_squareRootEuler hM12 R E he F
  have htarget : ∃ F : M14PullbackExtension (rescalingTransport hM12 hM13 G Q hQ a)
      p.curve (Ioo (Q * 0) (Q * τ)) p.horizontal_velocity,
      M14EulerEquation (rescalingTransport hM12 hM13 G Q hQ a) p F := ⟨F, hF⟩
  rw [← rescalingPath_right_inverse hM12 hM13 G Q hQ a p] at htarget
  obtain ⟨Ftarget, hFtarget⟩ := htarget
  have he' := eulerEquation_of_rescaling hM12 hM13 G Q hQ a p' F' Ftarget hFtarget
  obtain ⟨E'⟩ := exists_squareRoot_velocity_extension R'
  exact ⟨{
    path := p'
    square_path := R'
    extension := E'
    euler := fun _ hs W => squareRootEulerResidual_eq_zero_of_euler p' hCoordinates hM12
      F' he' R' E' hs W
    initial_velocity := rescalingSquareInverse_initial_vector hM12 hM13 G Q hQ a R hv R' }⟩

end PoincareConjecture.M14
