import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.TerminalMonotonicity
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Noncollapse

/-!
# All-past noncollapse from positive terminal volume

Closed-time volume monotonicity and Bishop--Gromov comparison supply the
explicit constant `AVR(0,p) / 2^n` at every center and radius in the ancient
past. In particular it satisfies the parabolic noncollapse condition used
in dimension reduction. The original zero-volume theorem still keeps its
noncollapse assumption explicit.

Reference: Kleiner--Lott, Proposition 41.13, p. 2678, and Corollary 44.1,
pp. 2682--2683 (corrected 2013).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.RicciFlow

variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]

/-- One terminal volume ratio controls all balls throughout the ancient past. -/
theorem ancient_ball_volume_lower_bound_of_terminal_asymptoticVolumeRatio
    (hC : RicciFlowCurvatureCalculus.{u}) (hm : 0 < m)
    (F : RicciFlow (m + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (p : M) (hvolume : 0 < (F.metric 0).asymptoticVolumeRatio p) :
    ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (((F.metric 0).asymptoticVolumeRatio p / 2 ^ (m + 1)) *
        r ^ (m + 1)) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r) := by
  intro t ht x r hr
  apply (F.metric t).ball_volume_lower_bound_of_asymptoticVolumeRatio
    (F.connection t) (by omega) (hcomplete t ht)
    (fun y v => ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M (F.metric t) (F.connection t))
        y (hoperator t ht y) v).1)
    p x ((F.metric t).edist_ne_top p x) hvolume.le hr
  exact F.antitoneOn_asymptoticVolumeRatio_of_bounded_ancient hC hm
    hcomplete hoperator hK hbound p ht (by simp) ht

/-- Positive terminal volume produces the explicit parabolic noncollapse
constant, including the original closed terminal slice. -/
theorem ancient_parabolic_noncollapse_of_terminal_asymptoticVolumeRatio
    (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (F : RicciFlow (m + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (p : M) (hvolume : 0 < (F.metric 0).asymptoticVolumeRatio p) :
    let κ := (F.metric 0).asymptoticVolumeRatio p / 2 ^ (m + 1)
    0 < κ ∧ ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ (m + 1)) ≤
        (F.metric t).volumeMeasure ((F.metric t).ball x r) := by
  refine ⟨div_pos hvolume (by positivity), ?_⟩
  intro t ht x r hr _
  exact F.ancient_ball_volume_lower_bound_of_terminal_asymptoticVolumeRatio
    hC hm hcomplete hoperator hK hbound p hvolume t ht x r hr

end PoincareMT.RicciFlow
