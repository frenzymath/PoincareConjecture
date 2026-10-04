import PoincareLib.Topology.Manifold.Schoenflies.Plane.Calculus.IntervalInterpolation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Smooth inverses for increasing real fibers

The triangular-map step in Smale (1959), Theorem 4, p. 624, and Munkres
(1960), Lemma 1.2, p. 194, requires joint smoothness of an inverse with
respect to an auxiliary parameter. We prove it for parameters in an
arbitrary real Banach space. The spatial derivative is positive and each
fiber is surjective; no uniform lower bound on the derivative is needed.
See `smale/derivations/2026-09-21-parametric-interpolation.md`.
-/

set_option autoImplicit false

open Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The invertible block triangular derivative used in Smale's Theorem 4,
p. 624. The scalar diagonal entry is evaluation on the vertical unit vector. -/
noncomputable def fiberDerivativeEquiv (L : E × ℝ →L[ℝ] ℝ)
    (hL : L (0, 1) ≠ 0) : (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ E).skewProd
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (L (0, 1)) hL))
    (L.comp (ContinuousLinearMap.inl ℝ E ℝ))

/-- The block triangular equivalence has the required derivative formula;
Smale (1959), Theorem 4, p. 624. -/
theorem fiberDerivativeEquiv_apply (L : E × ℝ →L[ℝ] ℝ)
    (hL : L (0, 1) ≠ 0) (p : E × ℝ) :
    fiberDerivativeEquiv L hL p = (p.1, L p) := by
  apply Prod.ext
  · rfl
  · change p.2 * L (0, 1) + L (p.1, 0) = L p
    have hscale : L (0, p.2) = p.2 * L (0, 1) := by
      simpa using L.map_smul p.2 (0, 1)
    rw [← hscale, ← map_add]
    simp

/-- As a continuous linear map, the triangular equivalence is the product
of the parameter projection and L; Smale's Theorem 4, p. 624. -/
theorem fiberDerivativeEquiv_coe (L : E × ℝ →L[ℝ] ℝ)
    (hL : L (0, 1) ≠ 0) :
    (fiberDerivativeEquiv L hL : E × ℝ →L[ℝ] E × ℝ) =
      (ContinuousLinearMap.fst ℝ E ℝ).prod L := by
  apply ContinuousLinearMap.ext
  exact fun p => fiberDerivativeEquiv_apply L hL p

/-- Restricting the derivative to a fixed real fiber evaluates it on the
vertical unit vector. This identifies the positive diagonal entry in
Smale's Theorem 4, p. 624, and Munkres's Lemma 1.2, p. 194. -/
theorem hasDerivAt_fiber {F : E × ℝ → ℝ} {L : E × ℝ →L[ℝ] ℝ}
    {z : E} {x : ℝ} (hF : HasFDerivAt F L (z, x)) :
    HasDerivAt (fun y => F (z, y)) (L (0, 1)) x := by
  exact (hF.comp x (hasFDerivAt_prodMk_right z x)).hasDerivAt

/-- A jointly smooth family of increasing surjective real maps gives a
jointly smooth diffeomorphism preserving its parameter. This is the inverse
regularity step of Smale's Theorem 4, p. 624, generalized to Banach parameters. -/
noncomputable def fiberDiffeomorph [CompleteSpace E] {F : E × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ z x, 0 < deriv (fun y => F (z, y)) x)
    (hsurj : ∀ z, Surjective (fun x => F (z, x))) :
    (E × ℝ) ≃ₘ[ℝ] (E × ℝ) := by
  let T : E × ℝ → E × ℝ := fun p => (p.1, F p)
  have hT : ContDiff ℝ ∞ T := contDiff_fst.prodMk hF
  have hdiag : ∀ p : E × ℝ, (fderiv ℝ F p) (0, 1) ≠ 0 := by
    intro p
    have hd := hasDerivAt_fiber ((hF.differentiable (by simp)) p).hasFDerivAt
    rw [← hd.deriv]
    exact (hpos p.1 p.2).ne'
  let D : E × ℝ → (E × ℝ) ≃L[ℝ] (E × ℝ) :=
    fun p => fiberDerivativeEquiv (fderiv ℝ F p) (hdiag p)
  have hderiv : ∀ p, HasFDerivAt T (D p : E × ℝ →L[ℝ] E × ℝ) p := by
    intro p
    rw [show (D p : E × ℝ →L[ℝ] E × ℝ) =
      (ContinuousLinearMap.fst ℝ E ℝ).prod (fderiv ℝ F p) from
        fiberDerivativeEquiv_coe _ _]
    exact hasFDerivAt_fst.prodMk ((hF.differentiable (by simp)) p).hasFDerivAt
  have hbij : Bijective T := by
    constructor
    · rintro ⟨z, x⟩ ⟨w, y⟩ h
      have hzw : z = w := congrArg Prod.fst h
      subst w
      have hxy : x = y :=
        (strictMono_of_deriv_pos (hpos z)).injective (congrArg Prod.snd h)
      exact Prod.ext rfl hxy
    · rintro ⟨z, y⟩
      obtain ⟨x, hx⟩ := hsurj z y
      exact ⟨(z, x), Prod.ext rfl hx⟩
  have hopen : IsOpenMap T := isOpenMap_of_hasStrictFDerivAt_equiv
    (fun p => hT.contDiffAt.hasStrictFDerivAt' (hderiv p) (by simp))
  let e : (E × ℝ) ≃ₜ (E × ℝ) :=
    (Equiv.ofBijective T hbij).toHomeomorphOfContinuousOpen hT.continuous hopen
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := hT.contMDiff
      contMDiff_invFun := (e.contDiff_symm hderiv hT).contMDiff }

/-- The parameter-preserving diffeomorphism has the prescribed family as
its second coordinate; Smale (1959), Theorem 4, p. 624. -/
@[simp] theorem fiberDiffeomorph_apply [CompleteSpace E] {F : E × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ z x, 0 < deriv (fun y => F (z, y)) x)
    (hsurj : ∀ z, Surjective (fun x => F (z, x))) (p : E × ℝ) :
    fiberDiffeomorph hF hpos hsurj p = (p.1, F p) := rfl

end Poincare.Manifold.Schoenflies.Plane
