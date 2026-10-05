import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.AreaContinuity.ConstantLift
import PoincareLib.Geometry.Riemannian.LoopSpace.Length.PeriodicSpeed
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops
import PoincareLib.Topology.Homotopy.LoopSpace.Contraction.Local
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Actual annuli between nearby C1 loops

For the filling-area limit in Morgan--Tian Claim 19.28, pp. 459-461,
the closed M58 local contraction joins corresponding loop points.
The smooth time cutoff gives a globally C1 periodic plane map, hence
a genuinely admissible annulus. See M65 derivation 26.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The actual interpolation of corresponding loop points used in the
C1 filling-area passage of Claim 19.28, pp. 459-461. -/
noncomputable def m65ContractionAnnulusMap (C : ℝ × (M × M) → M)
    (gamma eta : C1FreeLoopSpace (M := M)) (p : LoopPlane) : M :=
  C (Real.smoothTransition (p 1), periodicFreeLoop eta (p 0), periodicFreeLoop gamma (p 0))

/-- A contraction regular near the corresponding loop pairs gives a
global C1 annulus map; Claim 19.28, pp. 459-461. -/
theorem m65ContractionAnnulusMap_contMDiff (C : ℝ × (M × M) → M)
    (gamma eta : C1FreeLoopSpace (M := M))
    (hC : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (s, periodicFreeLoop eta x, periodicFreeLoop gamma x)) :
    ContMDiff (𝓡 2) (𝓡 3) 1 (m65ContractionAnnulusMap C gamma eta) := by
  have hcoord (i : Fin 2) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 1
      (fun p : LoopPlane => p i) :=
    (show ContDiff ℝ 1 (fun p : LoopPlane => p i) from
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).contMDiff
  have ht : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 1
      (fun p : LoopPlane => Real.smoothTransition (p 1)) :=
    (show ContDiff ℝ 1 Real.smoothTransition from
      Real.smoothTransition.contDiff).contMDiff.comp (hcoord 1)
  have hinput := ht.prodMk
    (((contMDiff_periodicFreeLoop eta).comp (hcoord 0)).prodMk
      ((contMDiff_periodicFreeLoop gamma).comp (hcoord 0)))
  intro p
  exact (hC _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ _).comp
    p (hinput p)

/-- The interpolation preserves the literal angular period;
Claim 19.28, pp. 459-461. -/
theorem m65ContractionAnnulusMap_periodic (C : ℝ × (M × M) → M)
    (gamma eta : C1FreeLoopSpace (M := M)) (x s : ℝ) :
    m65ContractionAnnulusMap C gamma eta (annulusPoint (x + curvePeriod) s) =
      m65ContractionAnnulusMap C gamma eta (annulusPoint x s) := by
  change C (_, periodicFreeLoop eta (x + curvePeriod),
      periodicFreeLoop gamma (x + curvePeriod)) = _
  rw [show curvePeriod = rampPeriod from rfl,
    periodic_periodicFreeLoop eta, periodic_periodicFreeLoop gamma]
  rfl

/-- The lower boundary is the original loop, with its exact angular
parameterization; Claim 19.28, pp. 459-461. -/
theorem m65ContractionAnnulusMap_lower (C : ℝ × (M × M) → M)
    (h0 : ∀ p q, C (0, p, q) = q)
    (gamma eta : C1FreeLoopSpace (M := M)) (x : ℝ) :
    m65ContractionAnnulusMap C gamma eta (annulusPoint x 0) =
      periodicFreeLoop gamma x := by
  change C (Real.smoothTransition 0, _, _) = _
  rw [Real.smoothTransition.zero, h0]
  rfl

/-- The upper boundary is the nearby loop, with its exact angular
parameterization; Claim 19.28, pp. 459-461. -/
theorem m65ContractionAnnulusMap_upper (C : ℝ × (M × M) → M)
    (gamma eta : C1FreeLoopSpace (M := M))
    (h1 : ∀ x, C (1, periodicFreeLoop eta x, periodicFreeLoop gamma x) =
      periodicFreeLoop eta x) (x : ℝ) :
    m65ContractionAnnulusMap C gamma eta (annulusPoint x 1) =
      periodicFreeLoop eta x := by
  change C (Real.smoothTransition 1, _, _) = _
  rw [Real.smoothTransition.one, h1]
  rfl

end PoincareMT
