import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.ChainTail
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.FiniteChain











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate




theorem exists_opposite_cylinder_tails_of_compact_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ →
        ∀ (U : Set M) (T : OpenCylinderModel U),
          C.end_neck.carrier ⊆ U → Disjoint C.closed_core U →
          IsOpen U → (frontier (C.carrier ∪ U)).Nonempty →
          IsCompact (C.carrier ∪ U ∪ D.carrier) →
          ∃ side : Bool,
            (∃ a ∈ Ioo (0 : ℝ) 1, T.tail side a ⊆ C.carrier) ∧
            ∃ b ∈ Ioo (0 : ℝ) 1, T.tail (!side) b ⊆ D.carrier := by
  obtain ⟨ε₀, hε₀, hsmall, htrunc⟩ := exists_truncated_core_domain_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε U T hend hdis hU hfront hcompact
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  obtain ⟨hK, hKC, -, hfrontK, -, hcoreK⟩ :=
    htrunc C hε 0 ⟨neg_neg_of_pos hR, hR⟩
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) 0)
  let A := C.carrier ∪ U
  let Y := A ∪ D.carrier
  have hAopen : IsOpen A := C.carrier_open.union hU
  have hAc : A = C.closed_core ∪ U := by
    rw [show A = C.carrier ∪ U from rfl, C.carrier_eq_closed_core_union_end,
      union_assoc, union_eq_right.mpr hend]
  have hfrontK' : frontier K = C.end_neck.central_sphere :=
    hfrontK.trans C.end_neck.centralSphere_range
  let S := (Y \ D.carrier) \ interior K
  have hS : IsCompact S :=
    (hcompact.diff D.carrier_open).diff isOpen_interior
  have hSU : S ⊆ U := by
    intro x hx
    have hxA : x ∈ A := hx.1.1.resolve_right hx.1.2
    rw [hAc] at hxA
    exact hxA.resolve_left (fun hc => hx.2 (hcoreK hc))
  obtain ⟨a, ha, hneg, hpos, hslab, hmiddle⟩ :=
    T.exists_tails_disjoint_of_isCompact
      (hS.union C.end_neck.isCompact_central_sphere)
      (union_subset hSU (C.end_neck.central_sphere_subset.trans hend))
  have ha01 : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  have hb01 : 1 - a ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ha.1, ha.2]
  have hside (V : Set M) (hV : IsPreconnected V)
      (havoid : Disjoint V (S ∪ C.end_neck.central_sphere)) :
      V ⊆ interior K ∨ V ⊆ Kᶜ := by
    apply hV.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset)
    intro x hx
    by_cases hxK : x ∈ K
    · left
      by_contra hnot
      exact disjoint_left.mp havoid hx (Or.inr (hfrontK' ▸
        (show x ∈ frontier K from ⟨subset_closure hxK, hnot⟩)))
    · exact Or.inr hxK
  have houtside {V : Set M} (hVU : V ⊆ U)
      (havoid : Disjoint V (S ∪ C.end_neck.central_sphere))
      (hout : V ⊆ Kᶜ) : V ⊆ D.carrier := by
    intro x hx
    by_contra hxD
    have hxS : x ∈ S := ⟨⟨Or.inl (Or.inr (hVU hx)), hxD⟩,
      fun hi => hout hx (interior_subset hi)⟩
    exact disjoint_left.mp havoid hx (Or.inl hxS)
  have hnotBothIn
      (hn : T.tail false a ⊆ interior K)
      (hp : T.tail true (1 - a) ⊆ interior K) : False := by
    have htrap : U ⊆ K ∪ T.coordinate '' (univ ×ˢ Icc a (1 - a)) := by
      intro x hx
      by_cases hxt : x ∈ T.tail false a ∪ T.tail true (1 - a)
      · exact Or.inl (hxt.elim (fun h => interior_subset (hn h))
          (fun h => interior_subset (hp h)))
      · exact Or.inr (hmiddle ⟨hx, hxt⟩)
    have hclosure : closure U ⊆ A :=
      (closure_minimal htrap (hK.union hslab).isClosed).trans
        (union_subset (hKC.trans subset_union_left)
          ((T.coordinate_slab_subset ha.1 hb01.2).trans subset_union_right))
    obtain ⟨x, hx⟩ := hfront
    have hxcl : x ∈ closure A := frontier_subset_closure hx
    rw [hAc, closure_union, C.isClosed_closed_core.closure_eq] at hxcl
    exact (hAopen.frontier_eq ▸ hx).2
      (hxcl.elim (fun h => Or.inl (C.closed_core_subset_carrier h)) (hclosure ·))
  have hnotBothOut (hn : T.tail false a ⊆ Kᶜ)
      (hp : T.tail true (1 - a) ⊆ Kᶜ) : False := by
    have htrap : K ∩ U ⊆ T.coordinate '' (univ ×ˢ Icc a (1 - a)) := by
      rintro x ⟨hxK, hxU⟩
      apply hmiddle
      exact ⟨hxU, fun h => h.elim (fun h => hn h hxK) (fun h => hp h hxK)⟩
    have hclosure : closure (K ∩ U) ⊆ U :=
      (closure_minimal htrap hslab.isClosed).trans
        (T.coordinate_slab_subset ha.1 hb01.2)
    have hboundary : C.boundary_neck.center ∈ C.boundary_sphere :=
      C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
    have hnegative : C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ⊆ K ∩ U := by
      intro x hx
      refine ⟨Or.inr (subset_closure ⟨hx.1, hx.2.1, ?_⟩), hend hx.1⟩
      linarith [hx.2.2]
    have hwitness : C.boundary_neck.center ∈ closure (K ∩ U) :=
      closure_mono hnegative (C.boundary_subset_negative_end_closure hboundary)
    exact disjoint_left.mp hdis (C.boundary_subset_closed_core hboundary) (hclosure hwitness)
  rcases hside (T.tail false a) (T.isConnected_tail false ha01).isPreconnected hneg with hn | hn
  · rcases hside (T.tail true (1 - a))
        (T.isConnected_tail true hb01).isPreconnected hpos with hp | hp
    · exact (hnotBothIn hn hp).elim
    · exact ⟨false, ⟨a, ha01, hn.trans (interior_subset.trans hKC)⟩,
        1 - a, hb01, houtside (T.tail_subset true hb01) hpos hp⟩
  · rcases hside (T.tail true (1 - a))
        (T.isConnected_tail true hb01).isPreconnected hpos with hp | hp
    · exact ⟨true, ⟨1 - a, hb01, hp.trans (interior_subset.trans hKC)⟩,
        a, ha01, houtside (T.tail_subset false ha01) hneg hn⟩
    · exact (hnotBothOut hn hp).elim




theorem exists_finite_chain_opposite_attachment_tails_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T → ∀ b : ℤ, T.shape = .finite 0 b →
          Disjoint D.closed_core C.carrier →
          (frontier (C.carrier ∪ (T.unionOpen : Set M)) ∩ D.core).Nonempty →
          ∀ {X : Set M} (tube : EpsilonTubeCertificate g X),
            tube.carrier = (T.unionOpen : Set M) →
            ∃ side : Bool, Nonempty (CapTubeAttachment C tube side) ∧
              ∃ a ∈ Ioo (0 : ℝ) 1, tube.cylinder.tail (!side) a ⊆ D.carrier := by
  obtain ⟨ε₁, hε₁, hsmall, hclose⟩ := exists_finite_chain_closing_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hinter⟩ := exists_chain_intersection_threshold.{u}
  obtain ⟨ε₃, hε₃, -, htails⟩ :=
    exists_opposite_cylinder_tails_of_compact_closing_threshold.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε hDC H T hT b hshape hdis hcontact X tube hcarrier
  have h₁ := hε.trans (min_le_left _ _)
  have h₂ := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₃ := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨-, hcompact⟩ := hclose C D h₁ hDC H T hT b hshape hdis hcontact
  obtain ⟨heq, havoid, model, -⟩ := hinter C h₂ T 0 hT.zero_active hT.first_neck
    hT.nonnegative (fun j hj hpos => (hT.centers j hj hpos).2)
  rw [← hcarrier] at heq havoid hcompact
  have hend : C.end_neck.carrier ⊆ tube.carrier := fun x hx => (heq.symm ▸ hx).2
  have hU : IsOpen tube.carrier := hcarrier.symm ▸ T.unionOpen.isOpen
  have hfront : (frontier (C.carrier ∪ tube.carrier)).Nonempty := by
    rw [hcarrier]
    exact hcontact.mono inter_subset_left
  obtain ⟨side, hfirst, hsecond⟩ :=
    htails C D h₃ tube.carrier tube.cylinder hend havoid hU hfront hcompact
  refine ⟨side, ⟨⟨?_, hfirst, ?_⟩⟩, hsecond⟩
  · rw [hcarrier]
    exact model
  · have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
    exact ⟨C.epsilon⁻¹ / 2, ⟨by linarith, by linarith⟩,
      (C.end_neck.region_subset_carrier _ _).trans hend⟩

end PoincareConjecture.CapCertificate
