import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.PlaneFirstVariation
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Boundary.AngularTrace

/-!
# The least-area disk interface

This is the exact output to be constructed by Plateau and consumed by
the supplied-disk part of Lemma 19.4. It does not assert existence.
Boundary differentials are genuine within derivatives on the closed
disk; no smooth extension outside the disk is required. The finite
branch set includes boundary branches, without asserting immersion.
Source: MT Lemma 19.2, printed p. 438; M65 derivations 24 and 28.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The actual attained filling disk, with precisely the regularity
needed by the supplied-disk variation argument. The primitive fields
contain no variation inequality, Gauss--Bonnet formula, branch-order
expansion, or assertion that the boundary is immersed. Those are separate
theorems. Source: MT Lemma 19.2, printed p. 438; M65 derivations 24 and 28. -/
structure M65MinimalDisk (g : RiemannianMetric 3 M) (connection : LeviCivitaData g)
    (γ : C1FreeLoopSpace (M := M)) where
  disk : LipschitzSpanningDisk g γ
  area_eq : disk.area = fillingArea g γ
  interior_smooth : ContMDiffOn (𝓡 2) (𝓡 3) ∞ disk.map (Metric.ball (0 : LoopPlane) 1)
  weakly_conformal : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, ∃ c : ℝ,
    m60AreaGram g disk.map z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  harmonic : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
    m65PlaneTension connection disk.map z = 0
  boundary_regular : ContMDiffOn (𝓡 2) (𝓡 3) 1 disk.map loopDiskSet
  finite_branches : {z : LoopPlane | z ∈ loopDiskSet ∧
    mfderivWithin (𝓡 2) (𝓡 3) disk.map loopDiskSet z = 0}.Finite

end PoincareMT
