import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.PeriodicLengthParameter
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Interpolation of equivariant length parameters

Morgan-Tian Definition 18.17, printed p. 430, boundary regularization.
A monotone homeomorphism can have a Lipschitz length parameter even
when it is not Lipschitz. Interpolating two scalar parameters with the
same increment gives a periodic curve-valued cylinder map.
-/

set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareMT.M60

/-- The length parameter after a monotone homeomorphism has the
Lipschitz bound of the reparameterized curve. Source: MT Definition
18.17, p. 430, cylinder regularization derivation. -/
theorem lipschitzWith_lengthParameter_comp_homeomorph
    {E : Type*} [PseudoEMetricSpace E] {f : ℝ → E}
    (hf : LocallyBoundedVariationOn f univ) (H : ℝ ≃ₜ ℝ)
    (hH : Monotone H) {C : ℝ≥0} (hcomp : LipschitzWith C (f ∘ H)) :
    LipschitzWith C (fun t => variationOnFromTo f univ 0 (H t)) := by
  have hLip := lipschitzOnWith_reparameterized_length
    (hH.monotoneOn univ) hcomp.lipschitzOnWith (mem_univ 0)
  rw [image_univ_of_surjective H.surjective] at hLip
  have h := (LipschitzWith.const (variationOnFromTo f univ 0 (H 0))).add
    (lipschitzOnWith_univ.mp hLip)
  have heq (t : ℝ) : variationOnFromTo f univ 0 (H 0) +
      variationOnFromTo f univ (H 0) (H t) = variationOnFromTo f univ 0 (H t) :=
    variationOnFromTo.add hf (mem_univ 0) (mem_univ (H 0)) (mem_univ (H t))
  simpa only [zero_add, heq] using h

/-- Affine interpolation of two real parameters. Its first variable
is the interpolation time. Source: MT Definition 18.17, p. 430. -/
def lengthParameterInterpolation (a b : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - p.1) * a p.2 + p.1 * b p.2

/-- Convex interpolation stays in the natural curve's domain.
Source: MT Definition 18.17, p. 430, cylinder regularization. -/
theorem lengthParameterInterpolation_mem {a b : ℝ → ℝ} {S : Set ℝ}
    (hS : Convex ℝ S) (ha : ∀ t, a t ∈ S) (hb : ∀ t, b t ∈ S)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    lengthParameterInterpolation a b (u, t) ∈ S := by
  exact hS (ha t) (hb t) (sub_nonneg.mpr hu.2) hu.1 (sub_add_cancel 1 u)

/-- Interpolation preserves the common scalar period increment.
Source: MT Definition 18.17, p. 430. -/
theorem lengthParameterInterpolation_add_period {a b : ℝ → ℝ} {T L : ℝ}
    (ha : ∀ t, a (t + T) = a t + L) (hb : ∀ t, b (t + T) = b t + L)
    (u t : ℝ) :
    lengthParameterInterpolation a b (u, t + T) =
      lengthParameterInterpolation a b (u, t) + L := by
  dsimp only [lengthParameterInterpolation]
  rw [ha, hb]
  ring

/-- The curve-valued interpolation is periodic without any assumption
that the natural curve's scalar domain is all of the real line.
Source: MT Definition 18.17, p. 430, cylinder regularization. -/
theorem periodic_lengthParameterInterpolation
    {E : Type*} {beta : ℝ → E} {a b : ℝ → ℝ} {S : Set ℝ} {T L : ℝ}
    (hS : Convex ℝ S) (haS : ∀ t, a t ∈ S) (hbS : ∀ t, b t ∈ S)
    (ha : ∀ t, a (t + T) = a t + L) (hb : ∀ t, b (t + T) = b t + L)
    (hbeta : ∀ s ∈ S, beta (s + L) = beta s)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Function.Periodic (fun t => beta (lengthParameterInterpolation a b (u, t))) T := by
  intro t
  change beta (lengthParameterInterpolation a b (u, t + T)) = _
  rw [lengthParameterInterpolation_add_period ha hb]
  exact hbeta _ (lengthParameterInterpolation_mem hS haS hbS hu)

/-- Scalar interpolation is locally Lipschitz jointly in time and
angle. Source: MT Definition 18.17, p. 430, cylinder regularization. -/
theorem locallyLipschitz_lengthParameterInterpolation
    {a b : ℝ → ℝ} {A B : ℝ≥0} (ha : LipschitzWith A a) (hb : LipschitzWith B b) :
    LocallyLipschitz (lengthParameterInterpolation a b) := by
  let q : (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    fun p => (1 - p.1.1) * p.2.1 + p.1.1 * p.2.2
  have hq : ContDiff ℝ 1 q := by fun_prop
  have hp : LocallyLipschitz (fun p : ℝ × ℝ => (p, (a p.2, b p.2))) :=
    LocallyLipschitz.id.prodMk
      ((ha.comp LipschitzWith.prod_snd).locallyLipschitz.prodMk
        (hb.comp LipschitzWith.prod_snd).locallyLipschitz)
  exact hq.locallyLipschitz.comp hp

end PoincareMT.M60
