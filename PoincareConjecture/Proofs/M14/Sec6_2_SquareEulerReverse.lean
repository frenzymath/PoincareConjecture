import PoincareConjecture.Proofs.M14.Sec6_2_SquarePullback
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCongruence
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackRestriction
import PoincareConjecture.Proofs.M14.Sec6_2_SquareCurve
import PoincareConjecture.Proofs.M14.Sec6_2_OpenFieldExtension
import PoincareConjecture.Proofs.M14.Sec6_1_InteriorDensity











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}




theorem backwardPath_contMDiffOn_of_square (R : M14SquareRootPath G p) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ p.curve (Ioo a b) := by
  apply (sqrtPullback_contMDiffOn p.tau_nonneg (R.smooth.mono R.interval_subset)).congr
  intro t ht
  have ht₀ : 0 ≤ t := p.tau_nonneg.trans ht.1.le
  have hs : Real.sqrt t ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt ht.1.le, Real.sqrt_le_sqrt ht.2.le⟩
  simpa only [Real.sq_sqrt ht₀] using (R.agrees (Real.sqrt t) hs).symm




theorem exists_backwardVelocity_extension_of_square (R : M14SquareRootPath G p) :
    Nonempty (M14PullbackExtension G p.curve (Ioo a b) p.horizontal_velocity) := by
  apply exists_pullbackExtension_of_isOpen isOpen_Ioo
  have hv := projectedCurveVelocityWithin_smooth isOpen_Ioo.uniqueDiffOn
    (backwardPath_contMDiffOn_of_square R)
  apply hv.congr
  intro s hs
  simp only [backwardPath_velocity_eq_projected p hs, projectedCurveVelocityWithin,
    projectedCurveVelocity, mfderivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hs)]

private theorem squareResidual_pair_heq {x y : G.Point} (h : x = y)
    {A V W : G.Horizontal x} {A' V' W' : G.Horizontal y}
    (hA : HEq A A') (hV : HEq V V') (hW : HEq W W') (s : ℝ) :
    G.spacetime.horizontalMetric.inner x A W -
        2 * s ^ 2 * M14HorizontalScalarDifferential G x W.val +
        4 * s * horizontalRicci G.leafwise x V W =
      G.spacetime.horizontalMetric.inner y A' W' -
        2 * s ^ 2 * M14HorizontalScalarDifferential G y W'.val +
        4 * s * horizontalRicci G.leafwise y V' W' := by
  cases h
  cases hA
  cases hV
  cases hW
  rfl




theorem squareRootEulerResidual_eq_scaled
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) R.horizontal_velocity)
    (F : M14PullbackExtension G p.curve (Ioo a b) p.horizontal_velocity)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt a) (Real.sqrt b))
    {W : G.Horizontal (R.curve s)} {W' : G.Horizontal (p.curve (s ^ 2))} (hW : HEq W W') :
    M14SquareRootEulerResidual G R E s W = (4 * s ^ 2) * M14EulerResidual G p F (s ^ 2) W' := by
  let J := Ioo (Real.sqrt a) (Real.sqrt b)
  have hsub : J ⊆ M14SqrtParameterInterval a b := Ioo_subset_Icc_self
  have heq : EqOn R.curve (fun r => p.curve (r ^ 2)) J :=
    fun r hr => R.agrees r (hsub hr)
  have hvel (r : ℝ) (hr : r ∈ J) :
      HEq (R.horizontal_velocity r) ((2 * r) • p.horizontal_velocity (r ^ 2)) :=
    (heq_of_eq (R.horizontal_agrees r hr)).trans (eqRec_heq _ _)
  let E₀ := pullbackExtensionRestrict E hsub
  let E₁ := pullbackExtensionCongrOn E₀ heq hvel
  have hrestrict := horizontalCovariantDerivative_restrict E hsub (isOpen_Ioo.mem_nhds hs)
  have hcongr := horizontalCovariantDerivative_congrOn E₀ heq hvel hs
  have hcurve : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞
      (fun r => p.curve (r ^ 2)) J :=
    (R.smooth.mono (hsub.trans R.interval_subset)).congr (fun _ hr => (heq hr).symm)
  have hind := horizontalCovariantDerivative_extension_independent E₁ (squarePullbackExtension p F)
    hs (isOpen_Ioo.uniqueDiffOn s hs) ((hcurve s hs).mdifferentiableWithinAt (by simp))
  have hD : HEq (M14HorizontalCovariantDerivative G R.curve
      (M14SqrtParameterInterval a b) R.horizontal_velocity E s)
      (M14HorizontalCovariantDerivative G (fun r => p.curve (r ^ 2)) J
        (fun r => (2 * r) • p.horizontal_velocity (r ^ 2)) (squarePullbackExtension p F) s) :=
    (heq_of_eq hrestrict).trans (hcongr.trans (heq_of_eq hind))
  exact (squareResidual_pair_heq (G := G) (heq hs) hD (hvel s hs) hW s).trans
    (squarePullback_eulerResidual p hM12 F hs W')




theorem eulerEquation_of_squareRootEuler
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) R.horizontal_velocity)
    (heuler : ∀ s ∈ M14SqrtParameterInterval a b, ∀ W,
      M14SquareRootEulerResidual G R E s W = 0)
    (F : M14PullbackExtension G p.curve (Ioo a b) p.horizontal_velocity) :
    M14EulerEquation G p F := by
  intro t ht
  have ht₀ : 0 < t := p.tau_nonneg.trans_lt ht.1
  have hs : Real.sqrt t ∈ Ioo (Real.sqrt a) (Real.sqrt b) :=
    ⟨Real.sqrt_lt_sqrt p.tau_nonneg ht.1, Real.sqrt_lt_sqrt ht₀.le ht.2⟩
  have hzero : ∀ W : G.Horizontal (p.curve ((Real.sqrt t) ^ 2)),
      M14EulerResidual G p F ((Real.sqrt t) ^ 2) W = 0 := by
    intro W
    let V : G.Horizontal (R.curve (Real.sqrt t)) :=
      (R.agrees (Real.sqrt t) (Ioo_subset_Icc_self hs)).symm ▸ W
    have hid := squareRootEulerResidual_eq_scaled hM12 R E F hs
      (W := V) (W' := W) (eqRec_heq _ _)
    have hz := hid.symm.trans (heuler (Real.sqrt t) (Ioo_subset_Icc_self hs) V)
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (Real.sqrt_pos.mpr ht₀).ne'))
  rw [Real.sq_sqrt ht₀.le] at hzero
  exact hzero

end PoincareConjecture.M14
