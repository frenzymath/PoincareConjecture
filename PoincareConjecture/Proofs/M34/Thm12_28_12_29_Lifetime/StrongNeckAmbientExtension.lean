import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckRestriction
import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.PolarCoordinates

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

open M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable def ambientCoordinate (z : E₃ × ℝ) : M :=
  N.coordinate_map (capDirection z.1, z.2)

theorem ambientCoordinate_coe (q : UnitTwoSphere) (s : ℝ) :
    N.ambientCoordinate ((q : E₃), s) = N.coordinate_map (q, s) := by
  have hq : capDirection (q : E₃) = q := by
    simpa only [one_smul] using capDirection_smul zero_lt_one q
  exact congrArg (fun p => N.coordinate_map (p, s)) hq

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

theorem chart_ambientCoordinate_contDiffAt (q : M) {z : E₃ × ℝ} (hz : z.1 ≠ 0)
    (hs : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hq : N.ambientCoordinate z ∈ (extChartAt (𝓡 3) q).source) :
    ContDiffAt ℝ ∞ ((extChartAt (𝓡 3) q) ∘ N.ambientCoordinate) z := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact ((contMDiffOn_extChartAt (I := 𝓡 3) (x := q)).contMDiffAt
    (by simpa only [extChartAt_source] using
      (isOpen_extChartAt_source q).mem_nhds hq)).comp z
      (N.ambientCoordinate_contMDiffAt hz hs)

theorem ambientCoordinate_sphereChart (q : UnitTwoSphere) :
    (fun p : E₂ × ℝ => N.ambientCoordinate
      (((chartAt E₂ q).symm p.1 : E₃), p.2)) =
    (fun p : E₂ × ℝ => N.coordinate_map ((chartAt E₂ q).symm p.1, p.2)) := by
  funext p
  exact N.ambientCoordinate_coe _ _

end PoincareConjecture.EpsilonNeck
