import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Noncompact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Cover.InvolutionQuotient
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

private theorem exists_enclosure_of_puncture_chart
    {Q : Type*} [TopologicalSpace Q] [T2Space Q] [CompactSpace Q]
    (p : Q) (e : OpenPartialHomeomorph Q (EuclideanSpace ℝ (Fin 3)))
    (hp : p ∈ e.source) {S : Set Q} (hS : IsCompact S) (hpS : p ∉ S) :
    ∃ U : Set Q, IsOpen U ∧ IsCompact (closure U) ∧
      closure U ⊆ ({p}ᶜ : Set Q) ∧ S ⊆ U ∧ IsConnected (frontier U) := by
  have hO := e.symm.isOpen_inter_preimage hS.isClosed.isOpen_compl
  have hpO : e p ∈ e.target ∩ e.symm ⁻¹' Sᶜ := by
    exact ⟨e.map_source hp, by simpa only [mem_preimage, e.left_inv hp, mem_compl_iff] using hpS⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hpO)
  have hsource : Metric.closedBall (e p) r ⊆ e.symm.source :=
    hball.trans inter_subset_left
  let B : Set Q := e.symm '' Metric.ball (e p) r
  let K : Set Q := e.symm '' Metric.closedBall (e p) r
  have hB : IsOpen B := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans hsource)
  have hK : IsCompact K := (isCompact_closedBall (e p) r).image_of_continuousOn
    (e.continuousOn_symm.mono hsource)
  have hBK : B ⊆ K := image_mono Metric.ball_subset_closedBall
  have hpB : p ∈ B := ⟨e p, Metric.mem_ball_self hr, e.left_inv hp⟩
  have hcl : closure Kᶜ ⊆ Bᶜ :=
    closure_minimal (compl_subset_compl.mpr hBK) hB.isClosed_compl
  have hKt : K ⊆ e.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_target (hsource hx)
  have hFt : frontier K ⊆ e.source := by
    apply frontier_subset_closure.trans
    rwa [hK.isClosed.closure_eq]
  have hfront := e.symm.image_frontier_eq_target_inter_of_closure_subset
    (D := Metric.closedBall (e p) r) (by simpa using hsource)
  change e.symm '' frontier (Metric.closedBall (e p) r) = e.source ∩ frontier K at hfront
  rw [inter_eq_right.mpr hFt] at hfront
  refine ⟨Kᶜ, hK.isClosed.isOpen_compl, isClosed_closure.isCompact, ?_, ?_, ?_⟩
  · intro x hx heq
    exact hcl hx (heq ▸ hpB)
  · intro x hxS hxK
    obtain ⟨y, hy, rfl⟩ := hxK
    exact (hball hy).2 hxS
  · rw [frontier_compl, ← hfront, frontier_closedBall _ hr.ne']
    apply (isConnected_sphere (E := EuclideanSpace ℝ (Fin 3)) ?_ (e p) hr.le).image
      _ (e.continuousOn_symm.mono (Metric.sphere_subset_closedBall.trans hsource))
    rw [← Module.finrank_eq_rank]
    norm_num

private theorem projectiveThree_t2Space : T2Space RealProjectiveThree := by
  have hq := Poincare.Topology.isOpenQuotientMap_of_pair_fibers
    realProjectiveThreeSetoid Neg.neg continuous_neg (fun _ _ => Iff.rfl)
  apply (t2Space_iff_of_isOpenQuotientMap hq).mpr
  have hrel : {z : UnitThreeSphere × UnitThreeSphere |
      Quotient.mk' z.1 = (Quotient.mk' z.2 : RealProjectiveThree)} =
      {z | z.1 = z.2} ∪ {z | z.1 = -z.2} := by
    ext z
    exact Quotient.eq
  rw [hrel]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst continuous_snd.neg)

private theorem exists_projectiveThree_chart (p : RealProjectiveThree) :
    ∃ e : OpenPartialHomeomorph RealProjectiveThree (EuclideanSpace ℝ (Fin 3)),
      p ∈ e.source := by
  have hl : IsLocalHomeomorph (Quotient.mk realProjectiveThreeSetoid) :=
    Poincare.Topology.Orientation.ProjectivePlane.involutionQuotient_isLocalHomeomorph
      realProjectiveThreeSetoid (Homeomorph.neg UnitThreeSphere) neg_neg
      (ne_neg_of_mem_unit_sphere ℝ) (fun _ _ => Iff.rfl)
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective p
  obtain ⟨q, ha, hq⟩ := hl a
  refine ⟨q.symm.trans (chartAt (EuclideanSpace ℝ (Fin 3)) a), ?_⟩
  rw [OpenPartialHomeomorph.trans_source]
  have hqa : Quotient.mk realProjectiveThreeSetoid a = q a := congrFun hq a
  rw [hqa]
  exact ⟨q.map_source ha, by simpa only [mem_preimage, q.left_inv ha] using mem_chart_source _ a⟩

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in
private theorem exists_projective_topological_coordinates (C : CapCertificate g)
    (hkind : C.model_kind = .puncturedProjective) :
    ∃ e : OpenPartialHomeomorph M RealProjectiveThree,
      e.source = C.carrier ∧ e.target = ({C.puncture}ᶜ : Set RealProjectiveThree) := by
  classical
  letI : T2Space RealProjectiveThree := projectiveThree_t2Space
  letI : T1Space RealProjectiveThree := T2Space.t1Space
  have model : CapModelEquivalence .puncturedProjective C.puncture C.carrier :=
    hkind ▸ C.model_equivalence
  let : TopologicalSpace model.model := model.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model.model := model.model_charted
  let : IsManifold (𝓡 3) ∞ model.model := model.model_manifold
  let F : C.carrier ≃ₜ model.model := {
    toFun := fun x => model.forward x.val
    invFun := fun y => ⟨model.inverse y, model.inverse_mem y⟩
    left_inv := fun x => Subtype.ext (model.left_inverse x x.property)
    right_inv := model.right_inverse
    continuous_toFun := continuousOn_iff_continuous_domRestrict.mp model.forward_smooth.continuousOn
    continuous_invFun := (continuousOn_univ.mp model.inverse_smooth.continuousOn).subtype_mk _ }
  let H : C.carrier ≃ₜ PuncturedRealProjectiveThree C.puncture :=
    (F.trans model.standard_model).trans Homeomorph.ulift
  let : Nonempty C.carrier := ⟨⟨C.core_nonempty.choose,
    C.core_subset_carrier C.core_nonempty.choose_spec⟩⟩
  let : Nonempty (PuncturedRealProjectiveThree C.puncture) := Nonempty.map H inferInstance
  let c : OpenPartialHomeomorph C.carrier M :=
    C.carrier_open.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  let p : OpenPartialHomeomorph (PuncturedRealProjectiveThree C.puncture) RealProjectiveThree :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  have hcs : c.source = univ := rfl
  have hct : c.target = C.carrier := by
    change Subtype.val '' (univ : Set C.carrier) = C.carrier
    simp
  have hps : p.source = univ := rfl
  have hpt : p.target = ({C.puncture}ᶜ : Set RealProjectiveThree) := by
    change Subtype.val '' (univ : Set (PuncturedRealProjectiveThree C.puncture)) = _
    ext x
    simp
  let e := c.symm.trans (H.toOpenPartialHomeomorph.trans p)
  refine ⟨e, ?_, ?_⟩
  · simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      hct, hps, Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  · simp only [e, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      hcs, hpt, Homeomorph.toOpenPartialHomeomorph_target, preimage_univ, inter_univ]

theorem CapCertificate.exists_enclosing_region_projective (C : CapCertificate g)
    (hkind : C.model_kind = .puncturedProjective) {S : Set M}
    (hS : IsCompact S) (hSC : S ⊆ C.carrier) :
    ∃ U : Set M, IsOpen U ∧ IsCompact (closure U) ∧
      closure U ⊆ C.carrier ∧ S ⊆ U ∧ IsConnected (frontier U) := by
  letI : T2Space RealProjectiveThree := projectiveThree_t2Space
  letI : T1Space RealProjectiveThree := T2Space.t1Space
  obtain ⟨e, hs, ht⟩ := exists_projective_topological_coordinates C hkind
  have heS : IsCompact (e '' S) := hS.image_of_continuousOn
    (e.continuousOn.mono (hs.symm ▸ hSC))
  have hpS : C.puncture ∉ e '' S := by
    rintro ⟨x, hx, heq⟩
    have hmem := ht ▸ e.map_source (hs.symm ▸ hSC hx)
    exact hmem heq
  obtain ⟨chart, hp⟩ := exists_projectiveThree_chart C.puncture
  obtain ⟨U, hU, hcompact, hUp, hSU, hconn⟩ :=
    exists_enclosure_of_puncture_chart C.puncture chart hp heS hpS
  have hsource : closure U ⊆ e.symm.source := by
    simpa only [e.symm_source, ht] using hUp
  obtain ⟨hopen, hc, hcl, hfront⟩ :=
    e.symm.image_region_of_isCompact_closure hU hcompact hsource
  refine ⟨e.symm '' U, hopen, hc, ?_, ?_, ?_⟩
  · rw [hcl]
    rintro _ ⟨x, hx, rfl⟩
    exact hs ▸ e.map_target (hsource hx)
  · intro x hx
    exact ⟨e x, hSU (mem_image_of_mem _ hx), e.left_inv (hs.symm ▸ hSC hx)⟩
  · rw [hfront]
    exact hconn.image _ (e.continuousOn_symm.mono (frontier_subset_closure.trans hsource))

end PoincareConjecture
