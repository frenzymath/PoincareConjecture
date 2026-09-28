import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.ChainIntersection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Tails
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Regions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_cylinder_tail_in_cap_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (U : Set M) (T : OpenCylinderModel U),
          C.end_neck.carrier ⊆ U → Disjoint C.closed_core U →
          ∃ side : Bool, ∃ a ∈ Ioo (0 : ℝ) 1, T.tail side a ⊆ C.carrier := by
  obtain ⟨ε₀, hε₀, hsmall, htrunc⟩ := exists_truncated_core_domain_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε U T hend hdisj
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  obtain ⟨hK, hKC, -, hfront, -, -⟩ := htrunc C hε 0 ⟨neg_neg_of_pos hR, hR⟩
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) 0)
  have hKclosed : IsClosed K := hK.isClosed
  have hfront' : frontier K = C.end_neck.central_sphere :=
    hfront.trans C.end_neck.centralSphere_range
  obtain ⟨a, ha, hneg, hpos, hslab, hmiddle⟩ := T.exists_tails_disjoint_of_isCompact
    C.end_neck.isCompact_central_sphere (C.end_neck.central_sphere_subset.trans hend)
  have ha01 : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
  have hb01 : 1 - a ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ha.1, ha.2]
  have hside (V : Set M) (hV : IsPreconnected V)
      (havoid : Disjoint V C.end_neck.central_sphere) :
      V ⊆ interior K ∨ V ⊆ Kᶜ := by
    apply hV.subset_or_subset isOpen_interior hKclosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset)
    intro x hx
    by_cases hxK : x ∈ K
    · left
      by_contra hnot
      exact disjoint_left.mp havoid hx (hfront' ▸
        (show x ∈ frontier K from ⟨subset_closure hxK, hnot⟩))
    · exact Or.inr hxK
  rcases hside (T.tail false a) (T.isConnected_tail false ha01).isPreconnected hneg with
      hnegin | hnegout
  · exact ⟨false, a, ha01, hnegin.trans (interior_subset.trans hKC)⟩
  rcases hside (T.tail true (1 - a)) (T.isConnected_tail true hb01).isPreconnected hpos with
      hposin | hposout
  · exact ⟨true, 1 - a, hb01, hposin.trans (interior_subset.trans hKC)⟩
  have htrap : K ∩ U ⊆ T.coordinate '' (univ ×ˢ Icc a (1 - a)) := by
    rintro x ⟨hxK, hxU⟩
    apply hmiddle
    exact ⟨hxU, fun h => h.elim (fun hnegx => hnegout hnegx hxK)
      (fun hposx => hposout hposx hxK)⟩
  have hclosure : closure (K ∩ U) ⊆ U :=
    (closure_minimal htrap hslab.isClosed).trans
      (T.coordinate_slab_subset ha.1 hb01.2)
  have hboundary : C.boundary_neck.center ∈ C.boundary_sphere :=
    C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
  have hnegativeSubset : C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ⊆ K ∩ U := by
    intro x hx
    refine ⟨Or.inr (subset_closure ⟨hx.1, hx.2.1, ?_⟩), hend hx.1⟩
    linarith [hx.2.2]
  have hwitness : C.boundary_neck.center ∈ closure (K ∩ U) :=
    closure_mono hnegativeSubset (C.boundary_subset_negative_end_closure hboundary)
  exact False.elim (disjoint_left.mp hdisj (C.boundary_subset_closed_core hboundary)
    (hclosure hwitness))

theorem exists_outgoing_chain_capTubeAttachment_threshold :
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
          ∀ {X : Set M} (tube : EpsilonTubeCertificate g X),
            tube.carrier = (T.unionOpen : Set M) →
            ∃ side : Bool, Nonempty (CapTubeAttachment C tube side) := by
  obtain ⟨ε₁, hε₁, hsmall, hinter⟩ := exists_chain_intersection_threshold.{u}
  obtain ⟨ε₂, hε₂, -, htail⟩ := exists_cylinder_tail_in_cap_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε T a ha hfirst hleast hcenters X tube hcarrier
  obtain ⟨heq, hdisj, model, -⟩ := hinter C (hε.trans (min_le_left _ _))
    T a ha hfirst hleast hcenters
  rw [← hcarrier] at heq hdisj
  have hmodel : OpenCylinderModel (C.carrier ∩ tube.carrier) := by
    rw [hcarrier]
    exact model
  have hend : C.end_neck.carrier ⊆ tube.carrier := by
    intro x hx
    exact (heq.symm ▸ hx).2
  obtain ⟨side, s, hs, hsub⟩ := htail C (hε.trans (min_le_right _ _))
    tube.carrier tube.cylinder hend hdisj
  refine ⟨side, ⟨⟨hmodel, ⟨s, hs, hsub⟩, ?_⟩⟩⟩
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  exact ⟨C.epsilon⁻¹ / 2, ⟨by linarith, by linarith⟩,
    (C.end_neck.region_subset_carrier _ _).trans hend⟩

end PoincareConjecture.CapCertificate
