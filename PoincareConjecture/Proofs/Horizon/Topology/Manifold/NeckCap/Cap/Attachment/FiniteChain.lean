import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.ChainTail
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.Certificate










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate



theorem exists_finite_capped_tube_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (T : BalancedNeckChain g C.epsilon) (a b : ℤ),
          T.shape = .finite a b → T.neck a = C.end_neck →
          (∀ j ∈ T.shape.active, a < j → (T.neck j).center ∉ C.carrier) →
          ∃ A : CappedTubeCertificate g, A.cap = C ∧
            A.tube.epsilon = C.epsilon ∧ HEq A.tube.chain T ∧
            A.carrier = C.carrier ∪ (T.unionOpen : Set M) := by
  obtain ⟨ε₁, hε₁, hsmall, hattach⟩ :=
    exists_outgoing_chain_capTubeAttachment_threshold.{u}
  obtain ⟨ε₂, hε₂, -, htube⟩ :=
    BalancedNeckChain.exists_finite_tubeCertificate_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε T a b hshape hfirst hcenters
  obtain ⟨j, hj⟩ := T.active_nonempty
  have hj' : j ∈ Icc a b := by simpa only [hshape, ChainShape.active] using hj
  have ha : a ∈ T.shape.active := by
    simpa only [hshape, ChainShape.active, mem_Icc] using
      (show a ≤ a ∧ a ≤ b from ⟨le_rfl, hj'.1.trans hj'.2⟩)
  have hleast : ∀ j ∈ T.shape.active, a ≤ j := by
    intro j hj
    exact (show j ∈ Icc a b by simpa only [hshape, ChainShape.active] using hj).1
  obtain ⟨tube, hepsilon, hchain, hcarrier⟩ := htube T
    (hε.trans (min_le_right _ _)) a b hshape ∅ (empty_subset _)
  obtain ⟨side, ⟨attachment⟩⟩ := hattach C (hε.trans (min_le_left _ _))
    T a ha hfirst hleast hcenters tube hcarrier
  have hend : C.end_neck.carrier ⊆ tube.carrier := by
    rw [hcarrier]
    intro x hx
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hfirst.symm ▸ hx⟩
  have hcenter : C.end_neck.center ∈ C.end_neck.carrier :=
    C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere
  let A : CappedTubeCertificate g :=
    { carrier := C.carrier ∪ tube.carrier
      cap := C
      tube := tube
      cap_subset := subset_union_left
      tube_subset := subset_union_right
      carrier_eq_union := rfl
      connected := C.isConnected_carrier.union
        ⟨C.end_neck.center, C.end_neck_subset hcenter, hend hcenter⟩
        tube.cylinder.isConnected_carrier
      attachment_side := side
      attachment := attachment }
  exact ⟨A, rfl, hepsilon, hchain, congrArg (C.carrier ∪ ·) hcarrier⟩

end PoincareConjecture.CapCertificate
