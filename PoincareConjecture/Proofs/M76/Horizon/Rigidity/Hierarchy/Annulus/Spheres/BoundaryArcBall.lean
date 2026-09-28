import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Geometry.BoundaryArcBall
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.ClosedComponent











set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_hamiltonZero_closed_second_component_boundary_arc_ball
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3) (phi : C(H0, H0))
    {R : Set X0} (hI : IsPLIrreducible e R)
    {u v a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    {theta theta' : C0}
    (hpair : (theta = (a : C0) ∧ theta' = (b : C0)) ∨
      (theta = (b : C0) ∧ theta' = (a : C0)))
    (heN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p u v))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p u v) =
      ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v) ∩
        frontier R) ∪
      ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}) ∪
        (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta'})))
    (hcyclic : ∀ x : ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}),
      IsCyclic (FundamentalGroup ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}) x))
    {S U : Set X0} (hSne : S.Nonempty)
    (hS : S ⊆ R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ S,
      connectedComponentIn (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}) x = S)
    (hrim : Disjoint S (frontier R)) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ D D' S' : Set X0, Nonempty (ChartwisePLBall e D S) ∧
      Nonempty (ChartwisePLBall e D' S') ∧ IsCompact D ∧ IsCompact D' ∧
      D' ⊆ interior R ∧ D ⊆ interior D' ∧ S ⊆ interior D' ∧ D' ⊆ D ∪ U ∧ S' ⊆ U ∧
      ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧ upper < p ∧
        a ∉ Icc lower upper ∧ b ∉ Icc lower upper ∧
        hamiltonZeroSecondCircleMap phi '' S' = AddCircle.closedIntervalArc p lower upper := by
  classical
  let : TopologicalSpace.MetrizableSpace X0 := (Q0).isEmbedding.metrizableSpace
  let : MetricSpace X0 := TopologicalSpace.metrizableSpaceMetric X0
  let q := hamiltonZeroSecondCircleMap phi
  let N := R ∩ q ⁻¹' AddCircle.closedIntervalArc p u v
  let F := R ∩ q ⁻¹' {theta}
  let F' := R ∩ q ⁻¹' {theta'}
  have hR : IsCompact R :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset hI.1.closed (subset_univ _)
  have hN : IsCompact N := hR.inter_right
    ((AddCircle.isCompact_closedIntervalArc p u v).isClosed.preimage q.continuous)
  have habC : (a : C0) ≠ (b : C0) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
      (show a ∈ Ico 0 (0 + p) by constructor <;> linarith)
      (show b ∈ Ico 0 (0 + p) by constructor <;> linarith)).mp h)
  have hne : theta ≠ theta' := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact habC
    · exact habC.symm
  have hSint : S ⊆ interior R := by
    intro x hx
    by_contra hn
    apply disjoint_left.mp hrim hx
    rw [hI.1.closed.frontier_eq]
    exact ⟨(hS hx).1, hn⟩
  obtain ⟨sph⟩ := exists_hamiltonZero_closed_second_component_sphere e phi hR heN
    hfront hne hSne hS hcomponent hrim hcyclic
  obtain ⟨D, hDcompact, hDint, ⟨ball⟩⟩ :=
    hI.exists_compact_ball_subset_interior hSint ⟨sph⟩
  have hSF : S ⊆ frontier N := fun x hx =>
    hfront.symm.subset (Or.inr (Or.inl (hS hx)))
  have hNne : N.Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    exact ⟨x, heN.closed.frontier_subset (hSF hx)⟩
  obtain ⟨s, f, Kmodel, Amodel, Hmodel, g, HBmodel, _, _, _, _, hAmodel, _⟩ :=
    heN.exists_original_frontier_surface_model hN hNne
  let : LocallyPathConnectedSpace Amodel.space :=
    Amodel.locallyPathConnectedSpace_of_finite hAmodel
  let : LocallyPathConnectedSpace (frontier N) :=
    HBmodel.isQuotientMap.locallyPathConnectedSpace
  have hF : IsClosed F := hI.1.closed.inter (isClosed_singleton.preimage q.continuous)
  have hF' : IsClosed F' := hI.1.closed.inter (isClosed_singleton.preimage q.continuous)
  let G := (N ∩ frontier R) ∪ F'
  have hG : IsClosed G := (heN.closed.inter isClosed_frontier).union hF'
  have hsplit : frontier N = F ∪ G := by
    rw [show frontier N = (N ∩ frontier R) ∪ (F ∪ F') from hfront]
    ext x
    simp only [G, mem_union]
    tauto
  have hdis : Disjoint S G := by
    apply disjoint_left.mpr
    intro x hx hxG
    rcases hxG with hxold | hxother
    · exact disjoint_left.mp hrim hx hxold.2
    · exact hne ((hS hx).2.symm.trans hxother.2)
  have hwhole := connectedComponentIn_eq_of_closed_piece hF hG hsplit hS hcomponent hdis
  obtain ⟨x0, hx0⟩ := hSne
  have hSo : IsOpen ((Subtype.val : frontier N → X0) ⁻¹' S) := by
    rw [← hwhole x0 hx0, connectedComponentIn_eq_image (hSF hx0),
      preimage_image_eq _ Subtype.val_injective]
    exact isOpen_connectedComponent
  obtain ⟨V, hV, hVS⟩ := isOpen_induced_iff.mp hSo
  have hVS' (x : X0) (hx : x ∈ frontier N) : x ∈ V ↔ x ∈ S :=
    Iff.of_eq (congrArg
      (fun A : Set (frontier N) => (⟨x, hx⟩ : frontier N) ∈ A) hVS)
  let chart := AddCircle.openPartialHomeomorphCoe p (0 : ℝ)
  let W : Set X0 := V ∩ (U ∩ (interior R ∩ q ⁻¹' chart.target))
  have hW : IsOpen W := hV.inter (hU.inter
    (isOpen_interior.inter (chart.open_target.preimage q.continuous)))
  have haT : (a : C0) ∈ chart.target := chart.map_source (by
    change 0 < a ∧ a < 0 + p
    exact ⟨ha, by linarith⟩)
  have hbT : (b : C0) ∈ chart.target := chart.map_source (by
    change 0 < b ∧ b < 0 + p
    exact ⟨ha.trans hab, by linarith⟩)
  have hthetaT : theta ∈ chart.target := by
    rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact haT
    · exact hbT
  have hSW : S ⊆ W := by
    intro x hx
    refine ⟨(hVS' x (hSF hx)).mpr hx, hSU hx, hSint hx, ?_⟩
    change q x ∈ chart.target
    rw [show q x = theta from (hS hx).2]
    exact hthetaT
  have hcut (x : X0) (hx : x ∈ W) : x ∈ frontier N ↔ x ∈ S :=
    ⟨fun hxf => (hVS' x hxf).mp hx.1, fun hxS => hSF hxS⟩
  obtain ⟨t, K, HB, c, r, hK, hr, hrhalf, hc, hi, hbase, hmaps, hf, hopen, _⟩ :=
    sph.exists_small_component_bicollar hR hI.1 heN hSint hW hSW hcut
  have hsub : K.space ×ˢ Icc (-r) r ⊆ K.space ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_interval_product hK (by linarith : -r < r)
  have hcsmall : PolyhedralPLInCharts e c (K.space ×ˢ Icc (-r) r) :=
    hJs ▸ hc.restrict_finite J hJ (hJs.subset.trans hsub)
  have hismall : Topology.IsEmbedding
      (fun z : (K.space ×ˢ Icc (-r) r : Set ((t → ℝ × V3) × ℝ)) => c z) :=
    hi.comp (Topology.IsEmbedding.subtypeVal.codRestrict _ (fun z => hsub z.property))
  obtain ⟨level, hlevel, hlevel0, D', ⟨ballNew⟩, hDD', hD'sub⟩ :=
    ball.exists_bicollar_enlargement sph hI.1.cover hI.1.compatible K hK HB c hr
      hcsmall hismall hbase (hopen r hr le_rfl)
  let S' : Set X0 := c '' (K.space ×ˢ {level})
  have hlevelI : level ∈ Icc (-r) r := by
    rcases hlevel with rfl | rfl <;> constructor <;> linarith
  have hS'small : S' ⊆ c '' (K.space ×ˢ Icc (-r) r) :=
    image_mono (prod_mono Subset.rfl (singleton_subset_iff.mpr hlevelI))
  have hsmallW : c '' (K.space ×ˢ Icc (-r) r) ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hmaps hz).1
  have hsmallint : c '' (K.space ×ˢ Icc (-r) r) ⊆ interior R := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hmaps hz).2
  have hS'W : S' ⊆ W := hS'small.trans hsmallW
  have hS'notfront : Disjoint S' (frontier N) := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hxfront
    have hzt : z.2 = level := hz.2
    exact hlevel0 (hzt.symm.trans ((hf z ⟨hz.1, hzt.symm ▸ hlevelI⟩).mp hxfront))
  have hphases : (R ∩ q ⁻¹' {(a : C0)}) ∪ (R ∩ q ⁻¹' {(b : C0)}) = F ∪ F' := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact union_comm _ _
  have hmarked : (R ∩ q ⁻¹' {(a : C0)}) ∪ (R ∩ q ⁻¹' {(b : C0)}) ⊆ frontier N := by
    rw [hphases, show frontier N = (N ∩ frontier R) ∪ (F ∪ F') from hfront]
    exact subset_union_right
  have havoid (x : X0) (hx : x ∈ S') : q x ≠ (a : C0) ∧ q x ≠ (b : C0) := by
    have hxR : x ∈ R := interior_subset (hsmallint (hS'small hx))
    exact ⟨fun heq => disjoint_left.mp hS'notfront hx (hmarked (Or.inl ⟨hxR, heq⟩)),
      fun heq => disjoint_left.mp hS'notfront hx (hmarked (Or.inr ⟨hxR, heq⟩))⟩
  obtain ⟨sphereNew⟩ := ballNew.nonempty_boundarySphere
  have hS'compact : IsCompact S' := ballNew.isCompact.of_isClosed_subset
    (by change IsClosed (c '' (K.space ×ˢ {level}))
        rw [← ballNew.frontier_eq]
        exact isClosed_frontier) ballNew.boundary_subset
  have harc := AddCircle.exists_closed_arc_of_compact_connected p hS'compact
    sphereNew.isConnected q q.continuous.continuousOn
    (fun x hx => (hS'W hx).2.2.2) a b havoid
  exact ⟨D, D', S', ⟨ball⟩, ⟨ballNew⟩, hDcompact, ballNew.isCompact,
    hD'sub.trans (union_subset hDint hsmallint), hDD', ball.boundary_subset.trans hDD',
    hD'sub.trans (union_subset_union_right D (fun x hx => (hsmallW hx).2.1)),
    (fun x hx => (hS'W hx).2.1), harc⟩

end PoincareConjecture.M76
