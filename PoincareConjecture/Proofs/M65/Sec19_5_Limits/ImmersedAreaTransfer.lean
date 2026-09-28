import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.PeriodicLoop
import PoincareConjecture.Proofs.M65.Def18_23_Profile.RestartedProfile
import PoincareConjecture.Definitions.M62Curve












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} (F : RicciFlow 3 M (Icc a b))





structure M65SmoothFilledLoopFamily (J : Set ℝ) where
  loops : ℝ → C1FreeLoopSpace (M := M)
  joint_smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞
    (fun z : ℝ × ℝ => periodicFreeLoop (loops z.2) z.1) (univ ×ˢ J)
  immersed : ∀ t ∈ J, ∀ x : ℝ,
    curveVelocity (n := 3) (periodicFreeLoop (loops t)) x ≠ 0
  filled : ∀ t ∈ J, Nonempty (LipschitzSpanningDisk (F.metric t) (loops t))





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





def M65ImmersedFillingAreaComparison : Prop :=
  ∀ (J : Set ℝ), IsOpen J → J ⊆ Ioo a b →
    ∀ C : M65SmoothFilledLoopFamily F J,
      (∀ t ∈ J, ∀ x : ℝ,
        curveVelocity (n := 3) (fun q => periodicFreeLoop (C.loops q) x) t =
          m62CurvatureVector F (fun y q => periodicFreeLoop (C.loops q) y) t x) →
      ∀ s t : ℝ, s ≤ t → Icc s t ⊆ J →
        fillingArea (F.metric t) (C.loops t) ≤
          m65RestartedAreaProfile F s (fillingArea (F.metric s) (C.loops s)) t

end PoincareConjecture
