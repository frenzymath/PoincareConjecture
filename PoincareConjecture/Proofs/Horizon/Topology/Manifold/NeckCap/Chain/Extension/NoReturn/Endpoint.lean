import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.Propagation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SphereContact










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem EpsilonNeck.exists_negative_half_exclusion_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g), N.IsSeparating → N.epsilon ≤ ε₀ →
        N'.epsilon = N.epsilon → N'.center ∉ N.carrier →
        N.region 0 N.epsilon⁻¹ ⊆ connectedComponentIn N.central_sphereᶜ N'.center →
        Disjoint N'.carrier (N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) := by
  obtain ⟨ε₁, hε₁, _, hscale⟩ := EpsilonNeck.exists_scale_comparison_at_common_closure.{u}
  refine ⟨min ε₁ (1 / 1000), lt_min hε₁ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hε heq hcenter hpositive
  apply disjoint_left.mpr
  intro x hx' hx
  have hscale' := (hscale N N' (hε.trans (min_le_left _ _))
    (heq ▸ hε.trans (min_le_left _ _)) ⟨x, subset_closure hx.1, subset_closure hx'⟩).2
  let U := connectedComponentIn N.central_sphereᶜ N'.center
  have hxU : x ∈ U := N.mem_component_complement_of_negative_half_overlap N'
    (hε.trans (min_le_right _ _)) heq hscale' hcenter hx.1 hx' hx.2.2.le
  have hU : IsPreconnected U := isPreconnected_connectedComponentIn
  have hcomponent : U ⊆ connectedComponent N.center := by
    rw [connectedComponent_eq (N.carrier_subset_connectedComponent hx.1)]
    exact hU.subset_connectedComponent hxU
  have havoid : Disjoint U N.central_sphere := by
    apply disjoint_left.mpr
    intro y hy hsphere
    exact connectedComponentIn_subset N.central_sphereᶜ N'.center hy hsphere
  have hi := inv_pos.mpr N.epsilon_pos
  obtain ⟨y, hy⟩ := (N.isConnected_region (a := 0) (b := N.epsilon⁻¹)
    (by linarith) le_rfl hi).nonempty
  apply N.not_meets_both_halves_of_isSeparating hN hU hcomponent havoid
  exact ⟨⟨x, hxU, hx.1, hx.2.1, by linarith [hx.2.2]⟩,
    ⟨y, hpositive hy, hy⟩⟩

theorem BalancedNeckChain.exists_outer_frontier_no_return_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
      ∀ (C : BalancedNeckChain g ε) (N : EpsilonNeck g), ε ≤ ε₀ →
        N.epsilon = ε → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∀ b ∈ C.shape.active,
          N.center ∈ closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹) →
          N.center ∉ C.unionOpen → ∀ i ∈ C.shape.active, i ≤ b →
            Disjoint N.carrier ((C.neck i).region (-ε⁻¹) (-ε⁻¹ / 2)) := by
  obtain ⟨ε₀, hε₀, hsmall, hexclude⟩ := EpsilonNeck.exists_negative_half_exclusion_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C N hε heq hsep b hb hfront hout i hi hib
  have hεi := C.epsilon_eq i hi
  have houti : N.center ∉ (C.neck i).carrier := by
    intro hx
    exact hout (mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩)
  have hpositive := C.positive_half_subset_component_complement_of_outer_frontier
    hb hfront hout hi hib
  simpa only [hεi] using hexclude (C.neck i) N (hsep i hi)
    (by simpa only [hεi] using hε) (heq.trans hεi.symm) houti
      (by simpa only [hεi] using hpositive)

end PoincareConjecture
