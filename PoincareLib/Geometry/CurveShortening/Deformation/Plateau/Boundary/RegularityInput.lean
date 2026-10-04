import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Boundary.RegularityLocalConclusion
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Boundary.RegularityGlobal
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Weak.MinimizerConformalNormalization
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Attainment

/-!
# The literal Plateau boundary input

The original normalized minimum supplies genuine local within-C1 maps,
which glue to its original smooth interior representative and actual
weakly monotone trace. Strict trace is a separate proved input.
Heinz 1970 pp. 99-105; MT Lemma 19.2; derivations 41, 42 and 50.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareMT

/-- The frozen boundary regularity input is proved for the original
weak minimum, without a boundary derivative or extension hypothesis.
Heinz pp. 99-105; MT Lemma 19.2, p. 438; derivations 41, 42 and 50. -/
theorem m65PlateauBoundaryRegularityInput_proved
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (connection : LeviCivitaData g)
    (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (gamma : C1FreeLoopSpace (M := M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) t ≠ 0)
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    M65PlateauBoundaryRegularityInput g connection e gamma a b c := by
  intro F hmin hconf f hf
  apply M65Boundary.exists_global_boundary_extension connection F f hf
  intro p hp
  obtain ⟨r, q, hr, hq, heq, htrace⟩ :=
    M65Boundary.weakDisk_boundary_local_contMDiff g connection he hinj hemb compact
      gamma.continuous hsmooth hregular F
      (F.normalized_minimum_is_minimum g he.continuous gamma.continuous hab hac hbc hmin)
      hconf hf hp
  exact ⟨r, hr, q, hq, heq, htrace⟩

end PoincareMT
