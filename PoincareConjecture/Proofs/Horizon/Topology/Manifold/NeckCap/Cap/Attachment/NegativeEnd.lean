import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.TruncatedDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate



theorem exists_disjoint_closed_core_of_negative_end_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ U : Set M, IsPreconnected U → (U \ C.carrier).Nonempty →
          (∃ s ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
            Disjoint U (C.end_neck.region (-C.epsilon⁻¹) s)) →
          Disjoint U C.closed_core := by
  obtain ⟨ε₀, hε₀, hsmall, htrunc⟩ := exists_truncated_core_domain_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε U hU hout hnegative
  obtain ⟨s, hs, hdisj⟩ := hnegative
  obtain ⟨a, hleft, has⟩ := exists_between hs.1
  have ha : a ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := ⟨hleft, has.trans hs.2⟩
  obtain ⟨hK, hKsub, -, hfront, -, -⟩ := htrunc C hε a ha
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) a)
  have hfrontsub : frontier K ⊆ C.end_neck.region (-C.epsilon⁻¹) s := by
    rw [hfront]
    rintro _ ⟨q, rfl⟩
    have hqa : (q, a) ∈ C.end_neck.cylinderDomain :=
      ⟨mem_univ _, by simpa only [C.end_neck_epsilon] using ha⟩
    refine ⟨C.end_neck.coordinate_map_mem hqa, ?_⟩
    rw [C.end_neck.coordinate_inverse_coordinate_map hqa]
    exact ⟨hleft, has⟩
  have havoid : Disjoint U (frontier Kᶜ) := by
    rw [frontier_compl]
    exact hdisj.mono_right hfrontsub
  obtain ⟨x, hxU, hxout⟩ := hout
  have hx : x ∈ interior Kᶜ := by
    rw [hK.isClosed.isOpen_compl.interior_eq]
    exact fun hxK => hxout (hKsub hxK)
  have hsub := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    hU havoid ⟨x, hxU, hx⟩
  exact disjoint_left.mpr fun y hyU hycore => interior_subset (hsub hyU) (Or.inl hycore)



theorem exists_chain_later_disjoint_closed_core_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ T : BalancedNeckChain g C.epsilon,
        ∀ i ∈ T.shape.active, ∀ j ∈ T.shape.active,
          T.neck i = C.end_neck → i < j → (T.neck j).center ∉ C.carrier →
          Disjoint (T.neck j).carrier C.closed_core := by
  obtain ⟨ε₀, hε₀, hsmall, havoid⟩ :=
    exists_disjoint_closed_core_of_negative_end_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε T i hi j hj hfirst hij hcenter
  apply havoid C hε (T.neck j).carrier (T.neck j).isConnected_carrier.isPreconnected
    ⟨(T.neck j).center,
      (T.neck j).central_sphere_subset (T.neck j).center_on_central_sphere, hcenter⟩
  obtain ⟨s, hs, hdisj⟩ := T.later_disjoint_negative_end i hi j hj hij
  refine ⟨s, ⟨hs.1, hs.2.trans (inv_pos.mpr C.epsilon_pos)⟩, ?_⟩
  simpa only [hfirst] using hdisj

end PoincareConjecture.CapCertificate
