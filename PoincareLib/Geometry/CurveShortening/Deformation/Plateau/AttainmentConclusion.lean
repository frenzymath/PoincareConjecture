import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Boundary.RegularityInput
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Weak.MinimizerConclusion
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Weak.MinimizerConformalVariation
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityEulerAlphaOneM60
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.StrictTrace
import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# Actual attainment in the frozen Lipschitz filling class

The five proved analytic inputs give the original least-area disk.
The embedding and the three distinct pin values are chosen internally.
MT Lemma 19.2, p. 438; Morrey ICM pp. 181-188; derivation 41.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace PoincareMT

/-- Every smooth regular Jordan loop with an actual Lipschitz filling
has an actual least-area disk in that same frozen class, with all
interior, boundary and branch data required by Lemma 19.4.
MT Lemma 19.2, p. 438; derivation 41. -/
theorem m65Plateau_attainment
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
    (g : RiemannianMetric 3 M) (connection : LeviCivitaData g)
    (gamma : C1FreeLoopSpace (M := M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ t, curveVelocity (n := 3) (periodicFreeLoop gamma) t ≠ 0)
    (hgamma : Function.Injective (gamma : LoopCircle → M))
    (hfill : Nonempty (LipschitzSpanningDisk g gamma)) :
    Nonempty (M65MinimalDisk g connection gamma) := by
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 3) (M := M)
  let a : LoopCircle := ⟨Complex.orthonormalBasisOneI.repr 1, by simp⟩
  let b : LoopCircle := ⟨Complex.orthonormalBasisOneI.repr (-1), by simp⟩
  let c : LoopCircle := ⟨Complex.orthonormalBasisOneI.repr Complex.I, by simp⟩
  have hab : a ≠ b := by
    intro h
    have hh := congrArg (fun z : LoopCircle => Complex.orthonormalBasisOneI.repr.symm z) h
    norm_num [a, b] at hh
  have hac : a ≠ c := by
    intro h
    have hh := congrArg (fun z : LoopCircle =>
      (Complex.orthonormalBasisOneI.repr.symm z).re) h
    norm_num [a, c] at hh
  have hbc : b ≠ c := by
    intro h
    have hh := congrArg (fun z : LoopCircle =>
      (Complex.orthonormalBasisOneI.repr.symm z).re) h
    norm_num [b, c] at hh
  have hperiodic : periodicFreeLoop gamma = gamma ∘ m65LoopAngular := by
    funext t
    exact gamma.boundary (m65LoopAngular t)
  have hs : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular) := hperiodic ▸ hsmooth
  have hr : ∀ t, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) t ≠ 0 := hperiodic ▸ hregular
  exact m65Plateau_attainment_of_five_inputs g connection e gamma a b c he hinj
    (m65Plateau_weak_minimum g e he hinj hemb.isEmbedding isCompact_univ
      gamma hgamma hfill a b c hab hac hbc)
    (fun F hmin => m65WeakDisk_conformal_of_normalized_minimum g he hinj
      hemb.isEmbedding isCompact_univ gamma.continuous F hab hac hbc hmin)
    (m65PlateauInteriorRegularityInput_proved connection e he hinj hemb.isEmbedding
      isCompact_univ gamma a b c)
    (m65PlateauBoundaryRegularityInput_proved g connection e he hinj hemb.isEmbedding
      isCompact_univ gamma hs hr a b c hab hac hbc)
    (m65Plateau_strict_trace g connection e he hemb.injective hinj gamma hgamma hs hr a b c)

end PoincareMT
