import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.FrontierNeck











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate




theorem exists_frontier_neck_extension_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C : CapCertificate g) (P : EpsilonNeck g), C.epsilon ≤ ε₀ →
          P.epsilon = C.epsilon → P.center ∈ frontier C.carrier →
          ∃ Q : EpsilonNeck g, Q.SameUpToReversal P ∧ Q.IsSeparating ∧
            Disjoint C.closed_core Q.carrier ∧
            C.carrier ∩ Q.carrier = C.end_neck.carrier ∩ Q.carrier ∧
            frontier C.carrier ⊆ Q.carrier ∧
            closure (Q.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆ C.carrier ∧
            frontier (C.carrier ∪ Q.carrier) = frontier Q.carrier \ C.carrier ∧
            frontier (C.carrier ∪ Q.carrier) ⊆
              frontier Q.carrier ∩ closure (Q.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) := by
  obtain ⟨ε₁, hε₁, hsmall, hoverlap⟩ := exists_frontier_neck_overlap_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hfrontier⟩ := exists_frontier_carrier_subset_closure_positive_end.{u}
  obtain ⟨ε₃, hε₃, -, hcapture⟩ :=
    EpsilonNeck.exists_closure_positive_quarter_subset_of_central_sphere_contact.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C P hε heq hp
  obtain ⟨Q, hsame, hsep, hdisj, hinter, -, hnegative⟩ :=
    hoverlap C P (hε.trans (min_le_left _ _)) heq hp
  have hQε : Q.epsilon = C.epsilon := hsame.epsilon_eq.trans heq
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hfrontC := hfrontier C
    (hε.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcontact : P.center ∈ closure
      (C.end_neck.region (C.end_neck.epsilon⁻¹ / 2) C.end_neck.epsilon⁻¹) := by
    simpa only [C.end_neck_epsilon] using hfrontC hp
  have hcapt := hcapture C.end_neck P
    (C.end_neck_epsilon.trans_le
      (hε.trans ((min_le_right _ _).trans (min_le_right _ _))))
    (heq.trans C.end_neck_epsilon.symm)
    ⟨P.center, hcontact, P.center_on_central_sphere⟩
  rw [C.end_neck_epsilon] at hcapt
  have hswallow : frontier C.carrier ⊆ Q.carrier := by
    rw [hsame.carrier_eq]
    exact hfrontC.trans hcapt
  have ha : -C.end_neck.epsilon⁻¹ < -(0.2 : ℝ) * C.epsilon⁻¹ := by
    rw [C.end_neck_epsilon]
    linarith
  have hb : (0.6 : ℝ) * C.epsilon⁻¹ < C.end_neck.epsilon⁻¹ := by
    rw [C.end_neck_epsilon]
    linarith
  have hcompact := C.end_neck.isCompact_coordinate_slab ha hb
  have hnegativeSlab : Q.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ⊆
      C.end_neck.coordinate_map ''
        (univ ×ˢ Icc (-(0.2 : ℝ) * C.epsilon⁻¹) ((0.6 : ℝ) * C.epsilon⁻¹)) := by
    intro x hx
    have h := hnegative hx
    exact (C.end_neck.mem_coordinate_slab_iff ha hb).mpr ⟨h.1, h.2.1.le, h.2.2.le⟩
  have hclosedNegative : closure (Q.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) ⊆
      C.carrier :=
    (closure_minimal hnegativeSlab hcompact.isClosed).trans
      ((C.end_neck.coordinate_slab_subset_carrier ha hb).trans C.end_neck_subset)
  have hfrontEq : frontier (C.carrier ∪ Q.carrier) = frontier Q.carrier \ C.carrier := by
    rw [(C.carrier_open.union Q.carrier_open).frontier_eq, Q.carrier_open.frontier_eq,
      closure_union]
    ext x
    constructor
    · rintro ⟨hxC | hxQ, hout⟩
      · have hxnotC : x ∉ C.carrier := fun h => hout (Or.inl h)
        have hxfront : x ∈ frontier C.carrier :=
          C.carrier_open.frontier_eq.symm ▸ ⟨hxC, hxnotC⟩
        exact False.elim (hout (Or.inr (hswallow hxfront)))
      · exact ⟨⟨hxQ, fun h => hout (Or.inr h)⟩, fun h => hout (Or.inl h)⟩
    · rintro ⟨⟨hxQ, hxnotQ⟩, hxnotC⟩
      exact ⟨Or.inr hxQ, fun h => h.elim hxnotC hxnotQ⟩
  refine ⟨Q, hsame, hsep, hdisj, hinter, hswallow, hclosedNegative, hfrontEq, ?_⟩
  intro x hx
  obtain ⟨hxQ, hxnotC⟩ := hfrontEq ▸ hx
  refine ⟨hxQ, ?_⟩
  have hends := Q.frontier_subset_closure_ends
    (a := -C.epsilon⁻¹ / 2) (b := C.epsilon⁻¹ / 2)
    (by rw [hQε]; linarith) (by rw [hQε]; linarith) hxQ
  rw [hQε] at hends
  exact hends.resolve_left (fun hneg => hxnotC (hclosedNegative hneg))

end PoincareConjecture.CapCertificate
