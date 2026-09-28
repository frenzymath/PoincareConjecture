import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.ConstantLift
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed
import PoincareConjecture.Proofs.M58.Mathlib.LocalContraction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

noncomputable def m65ContractionAnnulusMap (C : ℝ × (M × M) → M)
    (gamma eta : C1FreeLoopSpace (M := M)) (p : LoopPlane) : M :=
  C (Real.smoothTransition (p 1), periodicFreeLoop eta (p 0), periodicFreeLoop gamma (p 0))

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

theorem m65ContractionAnnulusMap_periodic (C : ℝ × (M × M) → M)
    (gamma eta : C1FreeLoopSpace (M := M)) (x s : ℝ) :
    m65ContractionAnnulusMap C gamma eta (annulusPoint (x + curvePeriod) s) =
      m65ContractionAnnulusMap C gamma eta (annulusPoint x s) := by
  change C (_, periodicFreeLoop eta (x + curvePeriod),
      periodicFreeLoop gamma (x + curvePeriod)) = _
  rw [show curvePeriod = rampPeriod from rfl,
    periodic_periodicFreeLoop eta, periodic_periodicFreeLoop gamma]
  rfl

theorem m65ContractionAnnulusMap_lower (C : ℝ × (M × M) → M)
    (h0 : ∀ p q, C (0, p, q) = q)
    (gamma eta : C1FreeLoopSpace (M := M)) (x : ℝ) :
    m65ContractionAnnulusMap C gamma eta (annulusPoint x 0) =
      periodicFreeLoop gamma x := by
  change C (Real.smoothTransition 0, _, _) = _
  rw [Real.smoothTransition.zero, h0]
  rfl

theorem m65ContractionAnnulusMap_upper (C : ℝ × (M × M) → M)
    (gamma eta : C1FreeLoopSpace (M := M))
    (h1 : ∀ x, C (1, periodicFreeLoop eta x, periodicFreeLoop gamma x) =
      periodicFreeLoop eta x) (x : ℝ) :
    m65ContractionAnnulusMap C gamma eta (annulusPoint x 1) =
      periodicFreeLoop eta x := by
  change C (Real.smoothTransition 1, _, _) = _
  rw [Real.smoothTransition.one, h1]
  rfl

end PoincareConjecture
