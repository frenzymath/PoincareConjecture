import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.StrongNeckRestriction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.PolarCoordinates

/-!
# Ambient extensions of actual neck coordinates

Radial normalization retracts a neighborhood of the unit sphere onto
the sphere. Composing an actual neck coordinate with this retraction
gives a smooth ambient map and preserves the literal chosen-chart
composition. This supplies fixed target charts for the finite-atlas
step of Morgan-Tian Theorem 12.28, pp. 323-324.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.EpsilonNeck

open M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual neck map extended off the sphere by the existing radial
retraction. The arbitrary value at the origin is not used geometrically. -/
noncomputable def ambientCoordinate (z : E₃ × ℝ) : M :=
  N.coordinate_map (capDirection z.1, z.2)

/-- The ambient extension recovers the original map exactly on the
unit sphere at every total axial value. -/
theorem ambientCoordinate_coe (q : UnitTwoSphere) (s : ℝ) :
    N.ambientCoordinate ((q : E₃), s) = N.coordinate_map (q, s) := by
  have hq : capDirection (q : E₃) = q := by
    simpa only [one_smul] using capDirection_smul zero_lt_one q
  exact congrArg (fun p => N.coordinate_map (p, s)) hq

/-- The radial extension is smooth at every nonzero ambient point
whose axial coordinate belongs to the old actual neck domain. -/
theorem ambientCoordinate_contMDiffAt {z : E₃ × ℝ} (hz : z.1 ≠ 0)
    (hs : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffAt 𝓘(ℝ, E₃ × ℝ) (𝓡 3) ∞ N.ambientCoordinate z := by
  have hn : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map
      (capDirection z.1, z.2) := N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs⟩)
  have hf : ContMDiffAt 𝓘(ℝ, E₃ × ℝ) (𝓡 3) ∞ Prod.fst z :=
    (contDiffAt_fst (𝕜 := ℝ) (n := ∞)).contMDiffAt
  have ht : ContMDiffAt 𝓘(ℝ, E₃ × ℝ) 𝓘(ℝ, ℝ) ∞ Prod.snd z :=
    (contDiffAt_snd (𝕜 := ℝ) (n := ∞)).contMDiffAt
  exact hn.comp z
    (((capDirection_contMDiffAt hz).comp z hf).prodMk ht)

/-- Its expression in any fixed target chart is an ordinary smooth germ
where the literal image is contained in that chart's source. -/
theorem chart_ambientCoordinate_contDiffAt (q : M) {z : E₃ × ℝ} (hz : z.1 ≠ 0)
    (hs : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hq : N.ambientCoordinate z ∈ (extChartAt (𝓡 3) q).source) :
    ContDiffAt ℝ ∞ ((extChartAt (𝓡 3) q) ∘ N.ambientCoordinate) z := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact ((contMDiffOn_extChartAt (I := 𝓡 3) (x := q)).contMDiffAt
    (by simpa only [extChartAt_source] using
      (isOpen_extChartAt_source q).mem_nhds hq)).comp z
      (N.ambientCoordinate_contMDiffAt hz hs)

/-- The chosen sphere-chart composition equals the ambient extension
after the included chosen chart, with equality on the entire parameter
space and hence equality of every ordinary derivative germ. -/
theorem ambientCoordinate_sphereChart (q : UnitTwoSphere) :
    (fun p : E₂ × ℝ => N.ambientCoordinate
      (((chartAt E₂ q).symm p.1 : E₃), p.2)) =
    (fun p : E₂ × ℝ => N.coordinate_map ((chartAt E₂ q).symm p.1, p.2)) := by
  funext p
  exact N.ambientCoordinate_coe _ _

end PoincareMT.EpsilonNeck
