import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.NegativeEnd
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate



theorem exists_chain_intersection_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (T : BalancedNeckChain g C.epsilon) (a : ℤ), a ∈ T.shape.active →
          T.neck a = C.end_neck →
          (∀ j ∈ T.shape.active, a ≤ j) →
          (∀ j ∈ T.shape.active, a < j → (T.neck j).center ∉ C.carrier) →
          C.carrier ∩ (T.unionOpen : Set M) = C.end_neck.carrier ∧
            Disjoint C.closed_core (T.unionOpen : Set M) ∧
            ∃ cylinder : OpenCylinderModel (C.carrier ∩ (T.unionOpen : Set M)),
              cylinder.middleSphere = C.end_neck.central_sphere := by
  obtain ⟨ε₀, hε₀, hsmall, havoid⟩ := exists_chain_later_disjoint_closed_core_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε T a ha hfirst hleast hcenters
  have hdisj : Disjoint C.closed_core (T.unionOpen : Set M) := by
    rw [disjoint_left]
    intro x hxcore hxT
    obtain ⟨j, hjx⟩ := mem_iUnion.mp hxT
    rcases (hleast j.1 j.2).eq_or_lt with haj | haj
    · have hjend : T.neck j.1 = C.end_neck := haj ▸ hfirst
      exact disjoint_left.mp C.disjoint_closed_core_end hxcore (hjend ▸ hjx)
    · exact disjoint_left.mp (havoid C hε T a ha j.1 j.2 hfirst haj
        (hcenters j.1 j.2 haj)) hjx hxcore
  have hend : C.end_neck.carrier ⊆ (T.unionOpen : Set M) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hfirst.symm ▸ hx⟩
  have hinter : C.carrier ∩ (T.unionOpen : Set M) = C.end_neck.carrier := by
    apply Subset.antisymm
    · rintro x ⟨hxC, hxT⟩
      rcases C.carrier_eq_closed_core_union_end ▸ hxC with hxcore | hxend
      · exact False.elim (disjoint_left.mp hdisj hxcore hxT)
      · exact hxend
    · intro x hx
      exact ⟨C.end_neck_subset hx, hend hx⟩
  refine ⟨hinter, hdisj, ?_⟩
  rw [hinter]
  exact ⟨C.end_neck.openCylinderModel, C.end_neck.openCylinderModel_middleSphere⟩

end PoincareConjecture.CapCertificate
