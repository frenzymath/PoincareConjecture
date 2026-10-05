import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Escape
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Escape of shrinking central spheres

The actual central spheres of shrinking necks eventually avoid every compact
set. Their diameter tends to zero, and their centers escape every compact
set by scalar-curvature continuity. Local compactness supplies the compact
neighborhood needed to combine these conclusions; completeness is unnecessary.

Reference: Morgan--Tian, Proposition 2.19, pp. 31--32.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

/-- Vanishing neck scales force the entire central spheres eventually outside
every compact set, without completeness or a global curvature bound. -/
theorem eventually_disjoint_central_sphere_compact_of_scale_tendsto_zero
    (D : LeviCivitaData g) {ι : Type*} {l : Filter ι}
    (N : ι → EpsilonNeck g)
    (hscale : Tendsto (fun i => (N i).scale) l (𝓝 0))
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ i in l, Disjoint (N i).central_sphere K := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  obtain ⟨δ, hδ, hcompact⟩ := hK.exists_isCompact_cthickening
  have hsmall : ∀ᶠ i in l, (2 * Real.pi) * (N i).scale < δ := by
    have h : Tendsto (fun i => (2 * Real.pi) * (N i).scale) l (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hscale
    exact h.eventually_lt_const hδ
  filter_upwards [eventually_center_not_mem_compact_of_scale_tendsto_zero D N hscale
    hcompact, hsmall] with i hi hdiam
  refine Set.disjoint_left.mpr ?_
  intro x hx hxK
  apply hi
  apply Metric.mem_cthickening_of_edist_le (N i).center x δ K hxK
  exact ((N i).edist_central_sphere_le_two_pi_mul_scale
    (N i).center_on_central_sphere hx).trans (ENNReal.ofReal_le_ofReal hdiam.le)

/-- Failure of the fixed-epsilon lower scale bound produces actual central
spheres that escape every compact set. -/
theorem exists_escaping_central_sphere_sequence_of_no_scale_lower_bound
    (D : LeviCivitaData g) (ε : ℝ)
    (hsmall : ¬ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ N : EpsilonNeck g, N.epsilon = ε → ρ ≤ N.scale) :
    ∃ N : ℕ → EpsilonNeck g,
      (∀ i, (N i).epsilon = ε) ∧
      Tendsto (fun i => (N i).scale) atTop (𝓝 0) ∧
      ∀ K : Set M, IsCompact K →
        ∀ᶠ i in atTop, Disjoint (N i).central_sphere K := by
  obtain ⟨N, hε, hscale, _⟩ :=
    exists_escaping_neck_sequence_of_no_scale_lower_bound D ε hsmall
  exact ⟨N, hε, hscale, fun K hK =>
    eventually_disjoint_central_sphere_compact_of_scale_tendsto_zero D N hscale hK⟩

end PoincareMT.EpsilonNeck
