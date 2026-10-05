import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.EscapeSphere
import PoincareLib.Geometry.Riemannian.Distance.CompleteBalls

/-!
# Escape of entire shrinking necks

For fixed epsilon, the diameter bound and scalar continuity force every point
of a shrinking neck to escape compact sets. Completeness then makes each neck
carrier relatively compact, so a later neck avoids any fixed earlier neck.

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

/-- The full carriers, and not only their centers or central spheres, escape
every compact set when epsilon is fixed and their scales tend to zero. -/
theorem eventually_disjoint_carrier_compact_of_scale_tendsto_zero
    (D : LeviCivitaData g) {ι : Type*} {l : Filter ι}
    (N : ι → EpsilonNeck g) {ε : ℝ} (hε : ∀ i, (N i).epsilon = ε)
    (hscale : Tendsto (fun i => (N i).scale) l (𝓝 0))
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ i in l, Disjoint (N i).carrier K := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  obtain ⟨δ, hδ, hcompact⟩ := hK.exists_isCompact_cthickening
  have hsmall : ∀ᶠ i in l, (2 * Real.pi + 2 * ε⁻¹) * (N i).scale < δ := by
    have h : Tendsto (fun i => (2 * Real.pi + 2 * ε⁻¹) * (N i).scale)
        l (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hscale
    exact h.eventually_lt_const hδ
  filter_upwards [eventually_center_not_mem_compact_of_scale_tendsto_zero D N hscale
    hcompact, hsmall] with i hi hdiam
  refine Set.disjoint_left.mpr ?_
  intro x hx hxK
  apply hi
  apply Metric.mem_cthickening_of_edist_le (N i).center x δ K hxK
  have hbound := (N i).edist_center_le_of_mem_carrier hx
  rw [hε i] at hbound
  exact hbound.trans (ENNReal.ofReal_le_ofReal hdiam.le)

/-- Completeness makes the closure of the open neck carrier compact. -/
theorem isCompact_closure_carrier (N : EpsilonNeck g)
    (hcomplete : MetricComplete g) :
    IsCompact (closure N.carrier) := by
  have hball := g.isCompact_closedBall_of_metricComplete hcomplete N.center
    ((2 * Real.pi + 2 * N.epsilon⁻¹) * N.scale)
  exact hball.of_isClosed_subset isClosed_closure
    (closure_minimal (fun _ hx => N.edist_center_le_of_mem_carrier hx) hball.isClosed)

/-- Any fixed neck is eventually disjoint from an entire shrinking-neck
family of fixed epsilon in a complete metric. -/
theorem eventually_disjoint_carrier_of_scale_tendsto_zero
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    {ι : Type*} {l : Filter ι} (N : ι → EpsilonNeck g)
    {ε : ℝ} (hε : ∀ i, (N i).epsilon = ε)
    (hscale : Tendsto (fun i => (N i).scale) l (𝓝 0))
    (N₀ : EpsilonNeck g) :
    ∀ᶠ i in l, Disjoint (N i).carrier (closure N₀.carrier) :=
  eventually_disjoint_carrier_compact_of_scale_tendsto_zero D N hε hscale
    (N₀.isCompact_closure_carrier hcomplete)

/-- Failure of the fixed-epsilon lower bound produces arbitrarily small
necks whose entire carriers avoid a prescribed compact set. -/
theorem exists_small_neck_disjoint_compact_of_no_scale_lower_bound
    (D : LeviCivitaData g) (ε : ℝ)
    (hsmall : ¬ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ N : EpsilonNeck g, N.epsilon = ε → ρ ≤ N.scale)
    {K : Set M} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : EpsilonNeck g, N.epsilon = ε ∧ N.scale < δ ∧
      Disjoint N.carrier K := by
  obtain ⟨N, hε, hscale, _⟩ :=
    exists_escaping_neck_sequence_of_no_scale_lower_bound D ε hsmall
  obtain ⟨i, hi, hdisj⟩ := ((hscale.eventually_lt_const hδ).and
    (eventually_disjoint_carrier_compact_of_scale_tendsto_zero D N hε hscale hK)).exists
  exact ⟨N i, hε i, hi, hdisj⟩

/-- In a complete metric the compact set can include a fixed earlier neck
and any prescribed base point, as required by the soul-to-end argument. -/
theorem exists_small_neck_disjoint_neck_and_point_of_no_scale_lower_bound
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (ε : ℝ)
    (hsmall : ¬ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ N : EpsilonNeck g, N.epsilon = ε → ρ ≤ N.scale)
    (N₀ : EpsilonNeck g) (p : M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : EpsilonNeck g, N.epsilon = ε ∧ N.scale < δ ∧
      Disjoint N.carrier (closure N₀.carrier) ∧ p ∉ N.carrier := by
  obtain ⟨N, hε, hscale, hdisj⟩ :=
    exists_small_neck_disjoint_compact_of_no_scale_lower_bound D ε hsmall
      ((N₀.isCompact_closure_carrier hcomplete).union (isCompact_singleton (x := p))) hδ
  rw [disjoint_union_right, disjoint_singleton_right] at hdisj
  exact ⟨N, hε, hscale, hdisj⟩

end PoincareMT.EpsilonNeck
