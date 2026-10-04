import PoincareLib.Geometry.CurveShortening.Deformation.GoodTimes.PeriodicLoop
import PoincareLib.Geometry.CurveShortening.Deformation.Profile.RestartedProfile
import PoincareLib.Geometry.CurveShortening.Evolution.Flow

/-!
# The literal embedded and immersed filling-area endpoints

These statements pin the producer/consumer interfaces for the generic
perturbation argument in Morgan--Tian Lemma 19.4, pp. 439-441. They do
not assert the generic-perturbation theorem or either filling inequality.
The actual velocity residual is retained because a generic perturbation
of a curve-shortening solution need not solve curve shortening.
Source: independently reviewed M65 derivation 40; monitor round 8.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} (F : RicciFlow 3 M (Icc a b))

/-- Actual smooth regular loop slices with actual frozen filling
competitors. No embedding, area comparison, limiting topology, or
generic perturbation is part of this data. MT Lemma 19.4, pp. 439-441;
derivation 40, actual smooth consumer. -/
structure M65SmoothFilledLoopFamily (J : Set ℝ) where
  loops : ℝ → C1FreeLoopSpace (M := M)
  joint_smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞
    (fun z : ℝ × ℝ => periodicFreeLoop (loops z.2) z.1) (univ ×ˢ J)
  immersed : ∀ t ∈ J, ∀ x : ℝ,
    curveVelocity (n := 3) (periodicFreeLoop (loops t)) x ≠ 0
  filled : ∀ t ∈ J, Nonempty (LipschitzSpanningDisk (F.metric t) (loops t))

/-- The embedded-time upper-right inequality, including the actual
pointwise velocity residual times the literal boundary length. The
Plateau and supplied-disk producers must prove this statement.
MT Lemma 19.4 and Claim 19.5, pp. 439-441; derivation 40. -/
def M65EmbeddedFillingAreaInequality : Prop :=
  ∀ (J : Set ℝ), IsOpen J → J ⊆ Ioo a b →
    ∀ (C : M65SmoothFilledLoopFamily F J) (q : ℝ), q ∈ J →
      Function.Injective (C.loops q : LoopCircle → M) →
      ∀ epsilon : ℝ, 0 ≤ epsilon →
      (∀ x : ℝ, (F.metric q).tangentNorm (periodicFreeLoop (C.loops q) x)
        (curveVelocity (n := 3) (fun t => periodicFreeLoop (C.loops t) x) q -
          m62CurvatureVector F (fun y t => periodicFreeLoop (C.loops t) y) q x) ≤ epsilon) →
      ∀ delta : ℝ, 0 < delta → ∀ᶠ h in 𝓝[>] (0 : ℝ),
        (fillingArea (F.metric (q + h)) (C.loops (q + h)) -
          fillingArea (F.metric q) (C.loops q)) / h ≤
        -2 * Real.pi - flowScalarCurvatureInfimum F q *
          fillingArea (F.metric q) (C.loops q) / 2 +
          epsilon * freeLoopLength (F.metric q) (C.loops q) + delta

/-- The required comparison for the actual immersed curve-shortening
family on any compact interior time interval. No injectivity or generic
approximation is an assumption. This is the input to the fixed-good-grid
terminal argument. MT Lemma 19.4 and Remark 19.29; derivation 40. -/
def M65ImmersedFillingAreaComparison : Prop :=
  ∀ (J : Set ℝ), IsOpen J → J ⊆ Ioo a b →
    ∀ C : M65SmoothFilledLoopFamily F J,
      (∀ t ∈ J, ∀ x : ℝ,
        curveVelocity (n := 3) (fun q => periodicFreeLoop (C.loops q) x) t =
          m62CurvatureVector F (fun y q => periodicFreeLoop (C.loops q) y) t x) →
      ∀ s t : ℝ, s ≤ t → Icc s t ⊆ J →
        fillingArea (F.metric t) (C.loops t) ≤
          m65RestartedAreaProfile F s (fillingArea (F.metric s) (C.loops s)) t

end PoincareMT
