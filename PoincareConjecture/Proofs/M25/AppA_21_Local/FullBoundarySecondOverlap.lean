import PoincareConjecture.Proofs.M25.AppA_1_Necks.ContainedSliceCylinder
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.TwoHalfCylinders
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapSecondFullBoundary

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

set_option maxHeartbeats 600000 in

set_option linter.unusedVariables false in

theorem CapCertificate.exists_full_boundary_second_overlap_cylinder :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C0 C1 : CapCertificate g) (D : BalancedNeckChain g C0.epsilon)
        {b : ℤ},
      C0.epsilon ≤ epsilon0 → C1.epsilon = C0.epsilon →
      D.shape = ChainShape.finite 0 b →
      (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) →
      let U : Set M := ⋃ i ∈ D.shape.active, (D.neck i).carrier
      let V : TopologicalSpace.Opens M :=
        ⟨C0.carrier ∪ U, C0.carrier_open.union
          (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)⟩
      C0.carrier ∩ U = C0.end_neck.carrier →
      Disjoint C0.closed_core C1.carrier →
      C1.boundary_sphere ⊆ (V : Set M) →
      ∀ d : V ≃ₜ (⟨C0.carrier, C0.carrier_open⟩ : TopologicalSpace.Opens M),
      ∀ y : M, y ∈ C1.core → y ∈ closure (V : Set M) →
      y ∉ (V : Set M) →
      Nonempty (OpenCylinderModel (C1.carrier ∩ U)) := by
  obtain ⟨ec, hcp, hccap, cylinder⟩ :=
    BalancedNeckChain.exists_cylinder_chart_at_contained_slice.{u}
  obtain ⟨eg, hgp, _, graph⟩ := EpsilonNeck.exists_contained_slice_graph.{u}
  refine ⟨min ec eg, lt_min hcp hgp, (min_le_left _ _).trans hccap, ?_⟩
  intro M _ _ _ _ _ _ g C0 C1 D b he he1 hshape hsep
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let U : Set M := ⋃ i ∈ D.shape.active, (D.neck i).carrier
  have hUopen : IsOpen U :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open
  let Uo : TopologicalSpace.Opens M := ⟨U, hUopen⟩
  let V : TopologicalSpace.Opens M := ⟨C0.carrier ∪ U, C0.carrier_open.union hUopen⟩
  change C0.carrier ∩ U = C0.end_neck.carrier →
    Disjoint C0.closed_core C1.carrier → C1.boundary_sphere ⊆ (V : Set M) →
    ∀ d : V ≃ₜ (⟨C0.carrier, C0.carrier_open⟩ : TopologicalSpace.Opens M),
    ∀ y : M, y ∈ C1.core → y ∈ closure (V : Set M) → y ∉ (V : Set M) →
      Nonempty (OpenCylinderModel (C1.carrier ∩ U))
  intro hfirst hdisjoint hboundary d y hycore hyclosure hyout
  obtain ⟨_, hendU, _, _, _, _, _⟩ :=
    C0.full_end_subset_of_boundary_in_cap_extension C1 Uo V rfl hfirst d
      hdisjoint hboundary y hycore hyclosure hyout
  change C1.end_neck.carrier ⊆ U at hendU
  obtain ⟨R, hR, heR, _, hRsphere, hcore, hend⟩ := C1.exists_outward_boundary_neck
  let L : ℝ := C0.epsilon⁻¹
  let s : ℝ := L / 2
  let E := C1.end_neck
  have hL : 0 < L := inv_pos.mpr C0.epsilon_pos
  have hs : s ∈ Ioo (-L) L := by dsimp only [s]; constructor <;> linarith
  have hspos : 0 < s := half_pos hL
  have hRe : R.epsilon = C0.epsilon := heR.trans he1
  have hEe : E.epsilon = C0.epsilon := C1.end_neck_epsilon.trans he1
  let S : Set M := range (fun q : UnitTwoSphere => R.coordinate_map (q, s))
  have hSE : S ⊆ E.carrier := by
    rintro x ⟨q, rfl⟩
    have hq : (q, s) ∈ R.cylinderDomain := by
      rw [EpsilonNeck.cylinderDomain, hRe]
      exact ⟨mem_univ _, hs⟩
    have hx : R.coordinate_map (q, s) ∈ R.region 0 C1.epsilon⁻¹ := by
      refine ⟨R.coordinate_map_mem hq, ?_⟩
      rw [R.coordinate_inverse_coordinate_map hq, he1]
      exact ⟨hspos, hs.2⟩
    exact (show R.coordinate_map (q, s) ∈ R.carrier ∩ E.carrier from hend.symm ▸ hx).2
  have hSU : S ⊆ U := hSE.trans hendU
  have hSC : S ⊆ C1.carrier := hSE.trans C1.end_neck_subset
  obtain ⟨P, hPs, hPt, hP, hPi, hPimage⟩ :=
    cylinder D hshape (le_min_iff.mp he).1 hsep R hRe s hs hSU
  change P.source = U at hPs
  change P '' S = univ ×ˢ ({0} : Set ℝ) at hPimage
  have hEsmall : E.epsilon ≤ eg := by
    rw [hEe]
    exact (le_min_iff.mp he).2
  have hRsmall : R.epsilon ≤ eg := by
    rw [hRe]
    exact (le_min_iff.mp he).2
  have hsR : s ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by rwa [hRe]
  obtain ⟨⟨h, hh, hdom, hgraph⟩, _⟩ :=
    graph E R hEsmall hRsmall s hsR (fun q => hSE (mem_range_self q))
  have hd (q : UnitTwoSphere) : h q ∈ Ioo (-L) L := by
    simpa only [hEe] using hdom q
  change range (fun q => E.coordinate_map (q, h q)) = S at hgraph
  let q0 := (R.coordinate_inverse R.center).1
  let a := R.coordinate_map (q0, -L / 2)
  let c := R.coordinate_map (q0, (s + L) / 2)
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ c
  let W : Set M := (V : Set M) ∪ C1.carrier
  have hconst : ∀ q : UnitTwoSphere, s ∈ Ico (0 : ℝ) C1.epsilon⁻¹ := by
    intro q
    rw [he1]
    exact ⟨hspos.le, hs.2⟩
  obtain ⟨hne, hAfront, hBfront, _, hAcap, _, _, hBV, _, _, hcover, _, _, _, _⟩ :=
    C0.compact_union_component_of_common_outward_graph C1 V d R hR hcore
      (fun _ => s) continuous_const hconst R s hsR rfl
      (fun x hx => Or.inr (hSU hx)) y hycore hyclosure hyout
  simp only [he1] at hne hAfront hBfront hAcap hBV hcover
  change A ≠ B at hne
  change frontier A = S at hAfront
  change frontier B = S at hBfront
  change closure A ⊆ C1.carrier at hAcap
  change closure B ⊆ (V : Set M) at hBV
  change W = closure A ∪ closure B at hcover
  have hAeq := (C1.outward_graph_compact_side R hR hcore
    (fun _ => s) continuous_const hconst).1
  change C1.core ∪ R.coordinate_map ''
    {z : RoundCylinderSpace | -C1.epsilon⁻¹ < z.2 ∧ z.2 < s} =
      connectedComponentIn Sᶜ (R.coordinate_map (q0, -C1.epsilon⁻¹ / 2)) at hAeq
  rw [he1] at hAeq
  change C1.core ∪ R.coordinate_map ''
    {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < s} = A at hAeq
  have hKinside : C1.closed_core ⊆ A := by
    intro x hx
    rw [← hAeq]
    by_cases hxc : x ∈ C1.core
    · exact Or.inl hxc
    have hxb : x ∈ C1.boundary_sphere := by
      rw [← C1.core_frontier_eq_boundary]
      refine ⟨subset_closure hx, ?_⟩
      simpa only [← C1.core_eq_interior_closed_core] using hxc
    have hxs : x ∈ R.central_sphere := hRsphere.symm ▸ hxb
    rw [R.central_sphere_eq] at hxs
    obtain ⟨z, hz, hzx⟩ := hxs
    have hz0 : z.2 = 0 := hz.2
    exact Or.inr ⟨z, by
      change -L < z.2 ∧ z.2 < s
      rw [hz0]
      exact ⟨neg_lt_zero.mpr hL, hspos⟩, hzx⟩
  have hSclosed : IsClosed S := by
    rw [← hAfront]
    exact isClosed_frontier
  have hAopen : IsOpen A := hSclosed.isOpen_compl.connectedComponentIn
  have hBopen : IsOpen B := hSclosed.isOpen_compl.connectedComponentIn
  have hAS : A ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hBS : B ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hxA hxB
    exact hne ((connectedComponentIn_eq hxA).trans (connectedComponentIn_eq hxB).symm)
  have hparts : W = (A ∪ S) ∪ B := by
    rw [hcover, closure_eq_self_union_frontier, closure_eq_self_union_frontier,
      hAfront, hBfront]
    ext x
    simp only [mem_union]
    tauto
  have side {T : Set M} (hT : IsConnected T) (hTW : T ⊆ W)
      (hTS : Disjoint T S) : T ⊆ A ∨ T ⊆ B := by
    apply hT.isPreconnected.subset_or_subset hAopen hBopen hAB
    intro x hx
    rcases hparts ▸ hTW hx with (hxA | hxS) | hxB
    · exact Or.inl hxA
    · exact False.elim (disjoint_left.mp hTS hx hxS)
    · exact Or.inr hxB
  have hzero : range (fun q : UnitTwoSphere => P.symm (q, 0)) = S := by
    apply Subset.antisymm
    · rintro x ⟨q, rfl⟩
      have hq : (q, (0 : ℝ)) ∈ P '' S := hPimage.symm ▸ ⟨mem_univ _, rfl⟩
      obtain ⟨x, hx, hpx⟩ := hq
      have hinv : P.symm (q, 0) = x := by
        rw [← hpx]
        exact P.left_inv (hPs.symm ▸ hSU hx)
      change P.symm (q, 0) ∈ S
      rwa [hinv]
    · intro x hx
      have hp : P x ∈ univ ×ˢ ({0} : Set ℝ) := hPimage ▸ mem_image_of_mem P hx
      have hp0 : (P x).2 = 0 := hp.2
      refine ⟨(P x).1, ?_⟩
      change P.symm ((P x).1, 0) = x
      rw [← hp0, Prod.mk.eta]
      exact P.left_inv (hPs.symm ▸ hSU hx)
  let Zm : Set RoundCylinderSpace := univ ×ˢ Ioo (-1 : ℝ) 0
  let Zp : Set RoundCylinderSpace := univ ×ˢ Ioo (0 : ℝ) 1
  let Um := P.symm '' Zm
  let Up := P.symm '' Zp
  have hZm : Zm ⊆ P.target := by
    intro z hz
    rw [hPt]
    exact ⟨mem_univ _, hz.2.1, hz.2.2.trans (by norm_num)⟩
  have hZp : Zp ⊆ P.target := by
    intro z hz
    rw [hPt]
    exact ⟨mem_univ _, (show (-1 : ℝ) < 0 by norm_num).trans hz.2.1, hz.2.2⟩
  have hUmU : Um ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact hPs ▸ P.map_target (hZm hz)
  have hUpU : Up ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact hPs ▸ P.map_target (hZp hz)
  have hUm : IsConnected Um :=
    (isConnected_univ.prod (isConnected_Ioo (by norm_num : (-1 : ℝ) < 0))).image
      P.symm (P.symm.continuousOn.mono hZm)
  have hUp : IsConnected Up :=
    (isConnected_univ.prod (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))).image
      P.symm (P.symm.continuousOn.mono hZp)
  have hPzero {x : M} (hx : x ∈ S) : (P x).2 = 0 :=
    (show P x ∈ univ ×ˢ ({0} : Set ℝ) from hPimage ▸ mem_image_of_mem P hx).2
  have hUmS : Disjoint Um S := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hxS
    have h := hPzero hxS
    rw [P.right_inv (hZm hz)] at h
    exact (ne_of_lt hz.2.2) h
  have hUpS : Disjoint Up S := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hxS
    have h := hPzero hxS
    rw [P.right_inv (hZp hz)] at h
    exact (ne_of_gt hz.2.1) h
  have hUdecomp : U = (Um ∪ S) ∪ Up := by
    apply Subset.antisymm
    · intro x hx
      have hxs : x ∈ P.source := hPs.symm ▸ hx
      have hp : P x ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := hPt ▸ P.map_source hxs
      rcases lt_trichotomy (P x).2 0 with hm | hz | hp'
      · exact Or.inl (Or.inl ⟨P x, ⟨mem_univ _, hp.2.1, hm⟩, P.left_inv hxs⟩)
      · apply Or.inl
        apply Or.inr
        rw [← hzero]
        refine ⟨(P x).1, ?_⟩
        change P.symm ((P x).1, 0) = x
        rw [← hz, Prod.mk.eta, P.left_inv hxs]
      · exact Or.inr ⟨P x, ⟨mem_univ _, hp', hp.2.2⟩, P.left_inv hxs⟩
    · exact union_subset (union_subset hUmU hSU) hUpU
  have hAU : (U ∩ A).Nonempty :=
    mem_closure_iff.mp
      ((show R.coordinate_map (q0, s) ∈ frontier A from
        hAfront.symm ▸ mem_range_self q0).1) U hUopen (hSU (mem_range_self q0))
  have hBU : (U ∩ B).Nonempty :=
    mem_closure_iff.mp
      ((show R.coordinate_map (q0, s) ∈ frontier B from
        hBfront.symm ▸ mem_range_self q0).1) U hUopen (hSU (mem_range_self q0))
  have hchoices : (Um ⊆ A ∧ Up ⊆ B) ∨ (Up ⊆ A ∧ Um ⊆ B) := by
    rcases side hUm (fun x hx => Or.inl (Or.inr (hUmU hx))) hUmS with hm | hm <;>
      rcases side hUp (fun x hx => Or.inl (Or.inr (hUpU hx))) hUpS with hp | hp
    · obtain ⟨x, hxU, hxB⟩ := hBU
      rcases hUdecomp ▸ hxU with (hxm | hxS) | hxp
      · exact False.elim (disjoint_left.mp hAB (hm hxm) hxB)
      · exact False.elim (hBS hxB hxS)
      · exact False.elim (disjoint_left.mp hAB (hp hxp) hxB)
    · exact Or.inl ⟨hm, hp⟩
    · exact Or.inr ⟨hp, hm⟩
    · obtain ⟨x, hxU, hxA⟩ := hAU
      rcases hUdecomp ▸ hxU with (hxm | hxS) | hxp
      · exact False.elim (disjoint_left.mp hAB hxA (hm hxm))
      · exact False.elim (hAS hxA hxS)
      · exact False.elim (disjoint_left.mp hAB hxA (hp hxp))
  let Dm : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < h z.1}
  let Dp : Set RoundCylinderSpace := {z | h z.1 < z.2 ∧ z.2 < L}
  let Em := E.coordinate_map '' Dm
  let Ep := E.coordinate_map '' Dp
  have hDm : Dm ⊆ E.cylinderDomain := by
    intro z hz
    rw [EpsilonNeck.cylinderDomain, hEe]
    exact ⟨mem_univ _, hz.1, hz.2.trans (hd z.1).2⟩
  have hDp : Dp ⊆ E.cylinderDomain := by
    intro z hz
    rw [EpsilonNeck.cylinderDomain, hEe]
    exact ⟨mem_univ _, (hd z.1).1.trans hz.1, hz.2⟩
  have hEmE : Em ⊆ E.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact E.coordinate_map_mem (hDm hz)
  have hEpE : Ep ⊆ E.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact E.coordinate_map_mem (hDp hz)
  have hEm : IsConnected Em :=
    (isConnected_between_continuous_graphs continuous_const hh.continuous
      (fun q => (hd q).1)).image E.coordinate_map
        (E.coordinate_map_smooth.continuousOn.mono hDm)
  have hEp : IsConnected Ep :=
    (isConnected_between_continuous_graphs hh.continuous continuous_const
      (fun q => (hd q).2)).image E.coordinate_map
        (E.coordinate_map_smooth.continuousOn.mono hDp)
  have hSheight {x : M} (hx : x ∈ S) :
      (E.coordinate_inverse x).2 = h (E.coordinate_inverse x).1 := by
    obtain ⟨q, rfl⟩ := hgraph.symm ▸ hx
    rw [E.coordinate_inverse_map (q, h q) (hdom q)]
  have hEmS : Disjoint Em S := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    have h := hSheight hx
    rw [E.coordinate_inverse_coordinate_map (hDm hz)] at h
    exact (ne_of_lt hz.2) h
  have hEpS : Disjoint Ep S := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    have h := hSheight hx
    rw [E.coordinate_inverse_coordinate_map (hDp hz)] at h
    exact (ne_of_gt hz.1) h
  have hEdecomp : E.carrier = (Em ∪ S) ∪ Ep := by
    apply Subset.antisymm
    · intro x hx
      have hz : (E.coordinate_inverse x).2 ∈ Ioo (-L) L := by
        simpa only [hEe] using (E.coordinate_inverse_mem x hx).2
      rcases lt_trichotomy (E.coordinate_inverse x).2
        (h (E.coordinate_inverse x).1) with hm | heq | hp
      · exact Or.inl (Or.inl ⟨E.coordinate_inverse x, ⟨hz.1, hm⟩,
          E.coordinate_map_inverse hx⟩)
      · apply Or.inl
        apply Or.inr
        rw [← hgraph]
        refine ⟨(E.coordinate_inverse x).1, ?_⟩
        change E.coordinate_map
          ((E.coordinate_inverse x).1, h (E.coordinate_inverse x).1) = x
        rw [← heq, Prod.mk.eta, E.coordinate_map_inverse hx]
      · exact Or.inr ⟨E.coordinate_inverse x, ⟨hp, hz.2⟩,
          E.coordinate_map_inverse hx⟩
    · exact union_subset (union_subset hEmE hSE) hEpE
  obtain ⟨qm, _, hmin⟩ :=
    isCompact_univ.exists_isMinOn univ_nonempty hh.continuous.continuousOn
  let v : ℝ := (-L + h qm) / 2
  have hv : v ∈ Ioo (-L) L := by
    have hq := hd qm
    dsimp only [v]
    constructor <;> linarith only [hq.1, hq.2]
  have hvh (q : UnitTwoSphere) : v < h q := by
    have hq := (hd qm).1
    have hm : h qm ≤ h q := hmin (mem_univ q)
    dsimp only [v]
    linarith only [hq, hm]
  have htail : E.region (-L) v ⊆ Em := by
    intro x hx
    exact ⟨E.coordinate_inverse x, ⟨hx.2.1, hx.2.2.trans (hvh _)⟩,
      E.coordinate_map_inverse hx.1⟩
  let p := C1.boundary_neck.center
  have hpboundary : p ∈ C1.boundary_sphere := by
    rw [C1.boundary_eq_neck_sphere]
    exact C1.boundary_neck.center_on_central_sphere
  have hpK : p ∈ C1.closed_core := by
    rw [← C1.core_frontier_eq_boundary] at hpboundary
    exact C1.closed_core_compact.isClosed.frontier_subset hpboundary
  have hpcl : p ∈ closure Em := by
    apply closure_mono htail
    simpa only [he1] using
      C1.boundary_subset_closure_end_region (by simpa only [he1] using hv) hpboundary
  obtain ⟨xm, hxmA, hxmEm⟩ :=
    mem_closure_iff.mp hpcl A hAopen (hKinside hpK)
  have hEmA : Em ⊆ A := by
    rcases side hEm (fun x hx => Or.inr (C1.end_neck_subset (hEmE hx))) hEmS with hm | hm
    · exact hm
    · exact False.elim (disjoint_left.mp hAB hxmA (hm hxmEm))
  obtain ⟨xp, hxpC, hxpB⟩ := mem_closure_iff.mp
    ((show R.coordinate_map (q0, s) ∈ frontier B from
      hBfront.symm ▸ mem_range_self q0).1)
    C1.carrier C1.carrier_open (hSC (mem_range_self q0))
  have hCBtoEp : C1.carrier ∩ B ⊆ Ep := by
    intro x hx
    have hxE : x ∈ E.carrier := by
      by_contra hn
      have hxK : x ∈ C1.closed_core := by
        rw [C1.closed_core_eq_complement_end]
        exact ⟨hx.1, hn⟩
      exact disjoint_left.mp hAB (hKinside hxK) hx.2
    rcases hEdecomp ▸ hxE with (hxm | hxS) | hxp
    · exact False.elim (disjoint_left.mp hAB (hEmA hxm) hx.2)
    · exact False.elim (hBS hx.2 hxS)
    · exact hxp
  have hEpB : Ep ⊆ B := by
    rcases side hEp (fun x hx => Or.inr (C1.end_neck_subset (hEpE hx))) hEpS with hp | hp
    · exact False.elim (disjoint_left.mp hAB (hp (hCBtoEp ⟨hxpC, hxpB⟩)) hxpB)
    · exact hp
  have hoverlap : C1.carrier ∩ U = ((U ∩ A) ∪ S) ∪ Ep := by
    apply Subset.antisymm
    · intro x hx
      rcases hparts ▸ (show x ∈ W from Or.inr hx.1) with (hxA | hxS) | hxB
      · exact Or.inl (Or.inl ⟨hx.2, hxA⟩)
      · exact Or.inl (Or.inr hxS)
      · exact Or.inr (hCBtoEp ⟨hx.1, hxB⟩)
    · rintro x ((⟨hxU, hxA⟩ | hxS) | hxE)
      · exact ⟨hAcap (subset_closure hxA), hxU⟩
      · exact ⟨hSC hxS, hSU hxS⟩
      · exact ⟨C1.end_neck_subset (hEpE hxE), hendU (hEpE hxE)⟩
  have hhalf (j : OpenPartialHomeomorph RoundCylinderSpace M) :
      j '' (univ ×ˢ Ioc (-1 : ℝ) 0) =
        (j '' (univ ×ˢ Ioo (-1 : ℝ) 0)) ∪ range (fun q => j (q, 0)) := by
    apply Subset.antisymm
    · rintro x ⟨⟨q, t⟩, ⟨_, htlo, hthi⟩, rfl⟩
      rcases lt_or_eq_of_le hthi with ht | rfl
      · exact Or.inl ⟨(q, t), ⟨mem_univ _, htlo, ht⟩, rfl⟩
      · exact Or.inr ⟨q, rfl⟩
    · rintro x (⟨z, hz, rfl⟩ | ⟨q, rfl⟩)
      · exact ⟨z, ⟨mem_univ _, hz.2.1, hz.2.2.le⟩, rfl⟩
      · exact ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hintersection {T T' : Set M} (hU : U = (T ∪ S) ∪ T')
      (hTA : T ⊆ A) (hT'B : T' ⊆ B) : U ∩ A = T := by
    apply Subset.antisymm
    · intro x hx
      rcases hU ▸ hx.1 with (hxT | hxS) | hxT'
      · exact hxT
      · exact False.elim (hAS hx.2 hxS)
      · exact False.elim (disjoint_left.mp hAB hx.2 (hT'B hxT'))
    · intro x hx
      exact ⟨hU.symm ▸ Or.inl (Or.inl hx), hTA hx⟩
  have hleft : ∃ e : OpenPartialHomeomorph RoundCylinderSpace M,
      univ ×ˢ Ioc (-1 : ℝ) 0 ⊆ e.source ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
      e '' (univ ×ˢ Ioc (-1 : ℝ) 0) = (U ∩ A) ∪ S ∧
      range (fun q : UnitTwoSphere => e (q, 0)) = S := by
    rcases hchoices with ⟨hm, hp⟩ | ⟨hp, hm⟩
    · refine ⟨P.symm, ?_, hPi, hP, ?_, hzero⟩
      · intro z hz
        rw [P.symm_source, hPt]
        exact ⟨mem_univ _, hz.2.1, hz.2.2.trans_lt (by norm_num)⟩
      · rw [hhalf, hzero, hintersection hUdecomp hm hp]
    · let e := roundCylinderAxialReflection.toHomeomorph.transOpenPartialHomeomorph P.symm
      have hemi : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source :=
        hPi.comp roundCylinderAxialReflection.contMDiff.contMDiffOn (fun _ hz => hz)
      have heinv : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target :=
        roundCylinderAxialReflection.symm.contMDiff.comp_contMDiffOn hP
      have hezero : range (fun q : UnitTwoSphere => e (q, 0)) = S := by
        change range (fun q : UnitTwoSphere => P.symm (q, -(0 : ℝ))) = S
        simpa only [neg_zero] using hzero
      have heimage : e '' (univ ×ˢ Ioo (-1 : ℝ) 0) = Up := by
        apply Subset.antisymm
        · rintro x ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
          refine ⟨(q, -t), ⟨mem_univ _, ?_⟩, rfl⟩
          constructor <;> linarith only [ht.1, ht.2]
        · rintro x ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
          refine ⟨(q, -t), ⟨mem_univ _, ?_⟩, ?_⟩
          · constructor <;> linarith only [ht.1, ht.2]
          · change P.symm (q, - -t) = P.symm (q, t)
            rw [neg_neg]
      refine ⟨e, ?_, hemi, heinv, ?_, hezero⟩
      · intro z hz
        change roundCylinderAxialReflection z ∈ P.target
        rw [hPt]
        change z.1 ∈ univ ∧ -z.2 ∈ Ioo (-1 : ℝ) 1
        refine ⟨mem_univ _, ?_, ?_⟩ <;> linarith only [hz.2.1, hz.2.2]
      · have hUflip : U = (Up ∪ S) ∪ Um := by
          rw [hUdecomp]
          ext x
          simp only [mem_union]
          tauto
        rw [hhalf, heimage, hezero, hintersection hUflip hp hm]
  obtain ⟨e, hehalf, hesm, heism, heimage, hezero⟩ := hleft
  have hw (q : UnitTwoSphere) : 0 < L - h q := sub_pos.mpr (hd q).2
  let F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ :=
    { toFun := fun z => (z.1, h z.1 + (L - h z.1) * z.2)
      invFun := fun z => (z.1, (z.2 - h z.1) / (L - h z.1))
      left_inv := by
        intro z
        apply Prod.ext
        · rfl
        · change (h z.1 + (L - h z.1) * z.2 - h z.1) / (L - h z.1) = z.2
          field_simp [(hw z.1).ne']
          ring
      right_inv := by
        intro z
        apply Prod.ext
        · rfl
        · change h z.1 + (L - h z.1) * ((z.2 - h z.1) / (L - h z.1)) = z.2
          field_simp [(hw z.1).ne']
          ring
      contMDiff_toFun := contMDiff_fst.prodMk
        ((hh.comp contMDiff_fst).add
          ((contMDiff_const.sub (hh.comp contMDiff_fst)).mul contMDiff_snd))
      contMDiff_invFun := contMDiff_fst.prodMk
        ((contMDiff_snd.sub (hh.comp contMDiff_fst)).div₀
          (contMDiff_const.sub (hh.comp contMDiff_fst)) (fun z => (hw z.1).ne')) }
  let f := F.toHomeomorph.transOpenPartialHomeomorph E.coordinatePartialHomeomorph
  have hfhalf : univ ×ˢ Ico (0 : ℝ) 1 ⊆ f.source := by
    intro z hz
    change F z ∈ E.cylinderDomain
    rw [EpsilonNeck.cylinderDomain, hEe]
    change z.1 ∈ univ ∧ -L < h z.1 + (L - h z.1) * z.2 ∧
      h z.1 + (L - h z.1) * z.2 < L
    have hlow := mul_nonneg (hw z.1).le hz.2.1
    have hhigh := mul_lt_mul_of_pos_left hz.2.2 (hw z.1)
    exact ⟨mem_univ _, by linarith only [(hd z.1).1, hlow],
      by linarith only [hhigh]⟩
  have hfsm : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f f.source :=
    E.coordinate_map_smooth.comp F.contMDiff.contMDiffOn (fun _ hz => hz)
  have hfism : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f.symm f.target :=
    F.symm.contMDiff.comp_contMDiffOn E.coordinate_inverse_smooth
  have hfzero : range (fun q : UnitTwoSphere => f (q, 0)) = S := by
    change range (fun q : UnitTwoSphere => E.coordinate_map (q, h q + (L - h q) * 0)) = S
    simpa only [mul_zero, add_zero] using hgraph
  have hfimage : f '' (univ ×ˢ Ico (0 : ℝ) 1) = Ep ∪ S := by
    apply Subset.antisymm
    · rintro x ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · apply Or.inr
        rw [← hfzero]
        have ht0' : (0 : ℝ) = t := ht0
        exact ⟨q, by change f (q, 0) = f (q, t); rw [ht0']⟩
      · apply Or.inl
        refine ⟨F (q, t), ?_, rfl⟩
        change h q < h q + (L - h q) * t ∧ h q + (L - h q) * t < L
        have hp := mul_pos (hw q) ht0
        have hu := mul_lt_mul_of_pos_left ht.2 (hw q)
        constructor <;> linarith only [hp, hu]
    · rintro x (⟨⟨q, t⟩, ht, rfl⟩ | hxS)
      · refine ⟨(q, (t - h q) / (L - h q)), ⟨mem_univ _, ?_, ?_⟩, ?_⟩
        · exact (div_pos (sub_pos.mpr ht.1) (hw q)).le
        · exact (div_lt_one (hw q)).mpr (sub_lt_sub_right ht.2 _)
        · change E.coordinate_map (q, h q + (L - h q) * ((t - h q) / (L - h q))) =
            E.coordinate_map (q, t)
          apply congrArg E.coordinate_map
          apply Prod.ext
          · rfl
          · field_simp [(hw q).ne']
            ring
      · obtain ⟨q, rfl⟩ := hfzero.symm ▸ hxS
        exact ⟨(q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hinter : (e '' (univ ×ˢ Ioc (-1 : ℝ) 0)) ∩
      (f '' (univ ×ˢ Ico (0 : ℝ) 1)) = range (fun q : UnitTwoSphere => e (q, 0)) := by
    rw [heimage, hfimage, hezero]
    apply Subset.antisymm
    · rintro x ⟨(hxA | hxS), (hxE | hxS')⟩
      · exact False.elim (disjoint_left.mp hAB hxA.2 (hEpB hxE))
      · exact hxS'
      · exact hxS
      · exact hxS
    · intro x hx
      exact ⟨Or.inr hx, Or.inr hx⟩
  have hunion : (e '' (univ ×ˢ Ioc (-1 : ℝ) 0)) ∪
      (f '' (univ ×ˢ Ico (0 : ℝ) 1)) = C1.carrier ∩ U := by
    rw [heimage, hfimage, hoverlap]
    ext x
    simp only [mem_union]
    tauto
  have hmodel := M25.Topology3D.exists_cylinder_model_of_opposite_half_charts
    e f hehalf hfhalf hesm heism hfsm hfism (hezero.trans hfzero.symm) hinter
  simpa only [hunion] using hmodel

end PoincareConjecture
