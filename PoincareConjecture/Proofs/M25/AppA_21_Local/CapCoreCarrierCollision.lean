import PoincareConjecture.Proofs.M25.AppA_21_Local.CapInwardBoundaryCut
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCoreCollision
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapLowerCutComponent
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SliceProjectionDifferential










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem CapCertificate.exists_two_cap_component_or_disjoint_core_carrier :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C0 C1 : CapCertificate g),
      C0.epsilon ≤ epsilon0 → C1.epsilon = C0.epsilon →
      (¬ (C0.carrier \ C0.end_neck.region
        (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹ ⊆ C1.core)) →
      ∀ (V : Set M), IsPreconnected V → C0.carrier ⊆ V →
      ∀ y : M, y ∈ C1.core → y ∉ V →
      let W := V ∪ C1.carrier
      (W = C0.carrier ∪ C1.carrier ∧ IsCompact W ∧ IsClopen W ∧
        IsConnected W ∧ ∃ z : M, W = connectedComponent z) ∨
      Disjoint C0.closed_core C1.carrier := by
  obtain ⟨epsilonC, hCpos, hCcap, hcollision⟩ :=
    CapCertificate.exists_two_cap_component_or_disjoint_cores.{u}
  obtain ⟨epsilonG, hGpos, _, hcommon⟩ :=
    CapCertificate.exists_common_outward_graph_of_finite_core_frontier.{u}
  obtain ⟨epsilonS, hSpos, _, hslice⟩ :=
    EpsilonNeck.exists_contained_slice_graph.{u}
  refine ⟨min epsilonC (min epsilonG epsilonS), lt_min hCpos (lt_min hGpos hSpos),
    (min_le_left _ _).trans hCcap, ?_⟩
  intro M _ _ _ _ _ _ g C0 C1 hsmall hepsilon hno V hV hC0V y hy hyV
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L := C0.epsilon⁻¹
  let W := V ∪ C1.carrier
  let Good : Prop := W = C0.carrier ∪ C1.carrier ∧ IsCompact W ∧ IsClopen W ∧
    IsConnected W ∧ ∃ z : M, W = connectedComponent z
  change Good ∨ Disjoint C0.closed_core C1.carrier
  have hsmallC : C0.epsilon ≤ epsilonC := hsmall.trans (min_le_left _ _)
  have hsmallG : C0.epsilon ≤ epsilonG :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsmallS : C0.epsilon ≤ epsilonS :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  rcases hcollision C0 C1 hsmallC hepsilon hno V hV hC0V y hy hyV with hgood | hcores
  · exact Or.inl hgood
  by_cases hdisjoint : Disjoint C0.closed_core C1.carrier
  · exact Or.inr hdisjoint
  apply Or.inl
  by_contra hnotGood
  have hL : 0 < L := inv_pos.mpr C0.epsilon_pos
  have hL1 : 0 < C1.epsilon⁻¹ := inv_pos.mpr C1.epsilon_pos
  have hcore0K : C0.core ⊆ C0.closed_core := by
    rw [C0.core_eq_interior_closed_core]
    exact interior_subset
  have hcore1K : C1.core ⊆ C1.closed_core := by
    rw [C1.core_eq_interior_closed_core]
    exact interior_subset
  have hK1C : C1.closed_core ⊆ C1.carrier := by
    rw [C1.closed_core_eq_complement_end]
    exact sdiff_subset
  have hy0out : y ∉ C0.carrier := fun hx => hyV (hC0V hx)
  have hy1K : y ∈ C1.closed_core := hcore1K hy
  have hy1end : y ∉ C1.end_neck.carrier := by
    rw [C1.closed_core_eq_complement_end] at hy1K
    exact hy1K.2
  have hpack (hc : IsCompact (C0.carrier ∪ C1.carrier))
      (ho : IsClopen (C0.carrier ∪ C1.carrier))
      (hn : IsConnected (C0.carrier ∪ C1.carrier))
      (he : ∃ z : M, C0.carrier ∪ C1.carrier = connectedComponent z) : Good := by
    obtain ⟨x, hx⟩ := C0.core_nonempty
    have hxC := C0.m25_core_subset_carrier hx
    have hVsub : V ⊆ C0.carrier ∪ C1.carrier :=
      hV.subset_isClopen ho ⟨x, hC0V hxC, Or.inl hxC⟩
    have hWeq : V ∪ C1.carrier = C0.carrier ∪ C1.carrier :=
      Subset.antisymm (union_subset hVsub subset_union_right)
        (union_subset_union_left _ hC0V)
    change V ∪ C1.carrier = C0.carrier ∪ C1.carrier ∧
      IsCompact (V ∪ C1.carrier) ∧ IsClopen (V ∪ C1.carrier) ∧
      IsConnected (V ∪ C1.carrier) ∧
      ∃ z : M, V ∪ C1.carrier = connectedComponent z
    rw [hWeq]
    exact ⟨rfl, hc, ho, hn, he⟩
  have hswapped : ¬ (C1.carrier \ C1.end_neck.region
      (C1.epsilon⁻¹ / 2) C1.epsilon⁻¹ ⊆ C0.core) := by
    intro hsub
    have hycut : y ∈ C1.carrier \ C1.end_neck.region
        (C1.epsilon⁻¹ / 2) C1.epsilon⁻¹ :=
      ⟨C1.m25_core_subset_carrier hy, fun hx => hy1end hx.1⟩
    exact hy0out (C0.m25_core_subset_carrier (hsub hycut))

  have hcontact (p : M) (hpcore : p ∈ C0.core)
      (hpfront : p ∈ frontier C1.carrier) : Good := by
    have hpout : p ∉ C1.carrier := by
      rw [C1.carrier_open.frontier_eq] at hpfront
      exact hpfront.2
    have hpcl : p ∈ closure C1.carrier := frontier_subset_closure hpfront
    have hptail : p ∈ closure (C1.end_neck.region 0 C1.epsilon⁻¹) :=
      (C1.end_neck_lower_cut_topology
        (show (0 : ℝ) ∈ Ioo (-C1.epsilon⁻¹) C1.epsilon⁻¹ from
          ⟨neg_lt_zero.mpr hL1, hL1⟩)).2.2.2.2.2.2 hpfront
    have hmeet : (C1.carrier ∩ C0.boundary_sphere).Nonempty := by
      by_contra hnone
      have havoid : Disjoint C1.carrier C0.boundary_sphere := by
        apply disjoint_left.mpr
        intro x hxC hxS
        exact hnone ⟨x, hxC, hxS⟩
      have hsub := C0.subset_core_of_avoids_boundary
        C1.m25_isConnected_carrier.isPreconnected havoid ⟨p, hpcl, hpcore⟩
      exact hy0out (C0.m25_core_subset_carrier
        (hsub (C1.m25_core_subset_carrier hy)))
    have hsingle {i : ℤ} (hi : i ∈ (ChainShape.finite 0 0).active)
        (hi1 : i + 1 ∈ (ChainShape.finite 0 0).active) : False := by
      change 0 ≤ i ∧ i ≤ 0 at hi
      change 0 ≤ i + 1 ∧ i + 1 ≤ 0 at hi1
      omega
    let D : BalancedNeckChain g C1.epsilon := {
      shape := .finite 0 0
      neck := fun _ => C1.end_neck
      source_necks := {C1.end_neck}
      selected := by
        intro _ _
        refine ⟨C1.end_neck, mem_singleton _, rfl, rfl, rfl, rfl, rfl,
          1, Or.inl rfl, ?_⟩
        intro z _
        simp only [one_mul]
      active_nonempty := ⟨0, le_rfl, le_rfl⟩
      epsilon_eq := fun _ _ => C1.end_neck_epsilon
      centers_distinct := by
        intro i hi j hj hij
        change 0 ≤ i ∧ i ≤ 0 at hi
        change 0 ≤ j ∧ j ≤ 0 at hj
        omega
      adjacent_overlap := fun _ hi hi1 => (hsingle hi hi1).elim
      overlap_contains_quarters := fun _ hi hi1 => (hsingle hi hi1).elim
      overlap_within_three_quarters := fun _ hi hi1 => (hsingle hi hi1).elim
      later_disjoint_negative_end := by
        intro i hi j hj hij
        change 0 ≤ i ∧ i ≤ 0 at hi
        change 0 ≤ j ∧ j ≤ 0 at hj
        omega
      balanced_center_distance := fun _ hi hi1 => (hsingle hi hi1).elim }
    let Vsingle : TopologicalSpace.Opens M :=
      ⟨C1.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier),
        C1.carrier_open.union
          (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)⟩
    have hVsingle : (Vsingle : Set M) = C1.carrier := by
      apply union_eq_left.mpr
      intro x hx
      obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hx
      exact C1.end_neck_subset hi
    have hpsingle : p ∉ (Vsingle : Set M) := by simpa only [hVsingle] using hpout
    have hmeetsingle : ((Vsingle : Set M) ∩ C0.boundary_sphere).Nonempty := by
      simpa only [hVsingle] using hmeet
    obtain ⟨d, _, _, hpclosure, R1, f1, N1, s1, hR1, _, _, _, hR1core, _,
        hf1, hf1dom, hs1, hlevel1, hSV1, _⟩ :=
      hcommon C1 C0 D (hepsilon.trans_le hsmallG) hepsilon.symm rfl rfl
        (fun _ _ => C1.end_neck_isSeparating)
        (by
          intro i hi hi0
          change 0 ≤ i ∧ i ≤ 0 at hi
          omega)
        (fun _ hi hi1 => (hsingle hi hi1).elim)
        hswapped p hpcore hptail hpsingle hmeetsingle
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, ho, hn, he⟩ :=
      C1.compact_union_component_of_common_outward_graph C0 Vsingle d.toHomeomorph
        R1 hR1 hR1core f1 hf1.continuous hf1dom N1 s1 hs1 hlevel1 hSV1
        p hpcore hpclosure hpsingle
    rw [hVsingle, union_comm C1.carrier C0.carrier] at hc ho hn he
    exact hpack hc ho hn ⟨_, he⟩
  have havoidFront : Disjoint C0.core (frontier C1.carrier) := by
    apply disjoint_left.mpr
    intro p hp hpf
    exact hnotGood (hcontact p hp hpf)
  obtain ⟨p, hpK0, hpC1⟩ := Set.not_disjoint_iff.mp hdisjoint
  have hpcl : p ∈ closure C0.core := C0.m25_closure_core_eq_closed_core.symm ▸ hpK0
  obtain ⟨x0, hx0C1, hx0core⟩ :=
    mem_closure_iff.mp hpcl C1.carrier C1.carrier_open hpC1
  obtain ⟨R, hR, heR, _, _, hRcore, _⟩ := C0.exists_outward_boundary_neck
  obtain ⟨hcoreA, _⟩ := C0.outward_graph_compact_side R hR hRcore
    (fun _ => 0) continuous_const (fun _ => ⟨le_rfl, hL⟩)
  have himagecore : R.coordinate_map ''
      {z : RoundCylinderSpace | -C0.epsilon⁻¹ < z.2 ∧ z.2 < 0} ⊆ C0.core := by
    rintro x ⟨z, hz, rfl⟩
    have hzs : z ∈ R.cylinderDomain := by
      refine ⟨mem_univ _, ?_⟩
      simpa only [heR] using
        (show z.2 ∈ Ioo (-C0.epsilon⁻¹) C0.epsilon⁻¹ from
          ⟨hz.1, hz.2.trans hL⟩)
    have hxnegative : R.coordinate_map z ∈ R.region (-C0.epsilon⁻¹) 0 := by
      refine ⟨R.coordinate_map_mem hzs, ?_⟩
      rw [R.coordinate_inverse_coordinate_map hzs]
      exact hz
    exact (hRcore.symm ▸ hxnegative).2
  have hcoreConnected : IsPreconnected C0.core := by
    rw [union_eq_left.mpr himagecore] at hcoreA
    rw [hcoreA]
    exact isPreconnected_connectedComponentIn
  have hcore0C1 : C0.core ⊆ C1.carrier := by
    apply hcoreConnected.subset_of_closure_inter_subset C1.carrier_open
      ⟨x0, hx0core, hx0C1⟩
    intro x hx
    by_contra hxout
    apply disjoint_left.mp havoidFront hx.2
    rw [C1.carrier_open.frontier_eq]
    exact ⟨hx.1, hxout⟩
  let N := C1.end_neck
  have hN : N.epsilon = C0.epsilon := C1.end_neck_epsilon.trans hepsilon
  have hK1N : Disjoint C1.closed_core N.carrier := by
    apply disjoint_left.mpr
    intro x hx hxN
    rw [C1.closed_core_eq_complement_end] at hx
    exact hx.2 hxN
  have hcore0N : C0.core ⊆ N.carrier := by
    intro x hx
    by_contra hxN
    apply disjoint_left.mp hcores (hcore0K hx)
    rw [C1.closed_core_eq_complement_end]
    exact ⟨hcore0C1 hx, hxN⟩
  let t := -L / 2
  let q := (R.coordinate_inverse R.center).1
  let S := range (fun v : UnitTwoSphere => R.coordinate_map (v, t))
  let a := R.coordinate_map (q, (t - L) / 2)
  let b := R.coordinate_map (q, t / 2)
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ b
  let Omega := connectedComponent R.center
  have ht : t ∈ Ioo (-C0.epsilon⁻¹) 0 := by
    change -L < -L / 2 ∧ -L / 2 < 0
    constructor <;> linarith only [hL]
  obtain ⟨_, hAcompact, hAclcore, _, _, hne, hAfront, hBfront, _, _, hcover⟩ :=
    C0.inward_boundary_slice_compact_component R hR hRcore ht
  change IsCompact (closure A) at hAcompact
  change closure A ⊆ C0.core at hAclcore
  change A ≠ B at hne
  change frontier A = S at hAfront
  change frontier B = S at hBfront
  change A ∪ S ∪ B = Omega at hcover
  have hSclA : S ⊆ closure A := by rw [← hAfront]; exact frontier_subset_closure
  have hScore : S ⊆ C0.core := hSclA.trans hAclcore
  have hSN : S ⊆ N.carrier := hScore.trans hcore0N
  have htR : t ∈ Ioo (-R.epsilon⁻¹) R.epsilon⁻¹ := by
    rw [heR]
    exact ⟨ht.1, ht.2.trans hL⟩
  obtain ⟨⟨f, hf, hfdom, hlevel⟩, _⟩ := hslice N R
    (by simpa only [hN] using hsmallS) (by simpa only [heR] using hsmallS)
    t htR (fun v => hSN ⟨v, rfl⟩)
  change range (fun v => N.coordinate_map (v, f v)) = S at hlevel
  have hfbound (v : UnitTwoSphere) : -L < f v ∧ f v < L := by
    change f v ∈ Ioo (-C0.epsilon⁻¹) C0.epsilon⁻¹
    simpa only [hN] using hfdom v
  have hSphere : IsCompact (univ : Set UnitTwoSphere) := isCompact_univ
  obtain ⟨vmin, _, hmin⟩ :=
    hSphere.exists_isMinOn ⟨q, mem_univ _⟩ hf.continuous.continuousOn
  obtain ⟨vmax, _, hmax⟩ :=
    hSphere.exists_isMaxOn ⟨q, mem_univ _⟩ hf.continuous.continuousOn
  let ell := (-L + f vmin) / 2
  let r := (f vmax + L) / 2
  have hellLower : -L < ell := by
    dsimp only [ell]
    linarith only [(hfbound vmin).1]
  have hellf (v : UnitTwoSphere) : ell < f v := by
    have hm : f vmin ≤ f v := hmin (mem_univ v)
    dsimp only [ell]
    linarith only [hm, (hfbound vmin).1]
  have hfr (v : UnitTwoSphere) : f v < r := by
    have hm : f v ≤ f vmax := hmax (mem_univ v)
    dsimp only [r]
    linarith only [hm, (hfbound vmax).2]
  have hrUpper : r < L := by
    dsimp only [r]
    linarith only [(hfbound vmax).2]
  have hell : ell ∈ Ioo (-L) L :=
    ⟨hellLower, (hellf q).trans (hfbound q).2⟩
  have hr : r ∈ Ioo (-L) L := ⟨(hfbound q).1.trans (hfr q), hrUpper⟩
  have hSmem (x : M) : x ∈ S ↔ x ∈ N.carrier ∧
      (N.coordinate_inverse x).2 = f (N.coordinate_inverse x).1 := by
    rw [← hlevel]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hfdom v⟩, ?_⟩
      rw [N.coordinate_inverse_map (v, f v) (hfdom v)]
    · rintro ⟨hxN, hheight⟩
      refine ⟨(N.coordinate_inverse x).1, ?_⟩
      have hz : ((N.coordinate_inverse x).1, f (N.coordinate_inverse x).1) =
          N.coordinate_inverse x := Prod.ext rfl hheight.symm
      change N.coordinate_map ((N.coordinate_inverse x).1, f (N.coordinate_inverse x).1) = x
      rw [hz]
      exact N.coordinate_map_inverse hxN
  let Gminus := N.coordinate_map ''
    {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < f z.1}
  let Gplus := N.coordinate_map ''
    {z : RoundCylinderSpace | f z.1 < z.2 ∧ z.2 < L}
  have hminusDom {z : RoundCylinderSpace} (hz : -L < z.2 ∧ z.2 < f z.1) :
      z ∈ N.cylinderDomain := by
    refine ⟨mem_univ _, ?_⟩
    rw [hN]
    exact ⟨hz.1, hz.2.trans (hfbound z.1).2⟩
  have hplusDom {z : RoundCylinderSpace} (hz : f z.1 < z.2 ∧ z.2 < L) :
      z ∈ N.cylinderDomain := by
    refine ⟨mem_univ _, ?_⟩
    rw [hN]
    exact ⟨(hfbound z.1).1.trans hz.1, hz.2⟩
  have hminusConnected : IsConnected Gminus := by
    apply (isConnected_between_continuous_graphs
      (f := fun _ : UnitTwoSphere => -L) (g := f)
      continuous_const hf.continuous (fun v => (hfbound v).1)).image
    exact N.coordinate_map_smooth.continuousOn.mono (fun _ hz => hminusDom hz)
  have hplusConnected : IsConnected Gplus := by
    apply (isConnected_between_continuous_graphs
      (f := f) (g := fun _ : UnitTwoSphere => L)
      hf.continuous continuous_const (fun v => (hfbound v).2)).image
    exact N.coordinate_map_smooth.continuousOn.mono (fun _ hz => hplusDom hz)
  have hminusAvoid : Gminus ⊆ Sᶜ := by
    rintro x ⟨z, hz, rfl⟩ hxS
    have hs := ((hSmem (N.coordinate_map z)).mp hxS).2
    rw [N.coordinate_inverse_coordinate_map (hminusDom hz)] at hs
    exact hz.2.ne hs
  have hplusAvoid : Gplus ⊆ Sᶜ := by
    rintro x ⟨z, hz, rfl⟩ hxS
    have hs := ((hSmem (N.coordinate_map z)).mp hxS).2
    rw [N.coordinate_inverse_coordinate_map (hplusDom hz)] at hs
    exact hz.1.ne' hs
  have hNcover : N.carrier ⊆ Gminus ∪ S ∪ Gplus := by
    intro x hx
    have hxheight : (N.coordinate_inverse x).2 ∈ Ioo (-L) L := by
      simpa only [hN] using (N.coordinate_inverse_mem x hx).2
    rcases lt_trichotomy (N.coordinate_inverse x).2
        (f (N.coordinate_inverse x).1) with hlo | heq | hhi
    · exact Or.inl (Or.inl ⟨N.coordinate_inverse x, ⟨hxheight.1, hlo⟩,
        N.coordinate_map_inverse hx⟩)
    · exact Or.inl (Or.inr ((hSmem x).mpr ⟨hx, heq⟩))
    · exact Or.inr ⟨N.coordinate_inverse x, ⟨hhi, hxheight.2⟩,
        N.coordinate_map_inverse hx⟩
  have hAsub : A ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hxA hxB
    exact hne ((connectedComponentIn_eq hxA).trans (connectedComponentIn_eq hxB).symm)
  have hside {T : Set M} {c : M} (hT : IsPreconnected T) (hTS : T ⊆ Sᶜ)
      (hmeet : (T ∩ connectedComponentIn Sᶜ c).Nonempty) :
      T ⊆ connectedComponentIn Sᶜ c := by
    obtain ⟨x, hxT, hxC⟩ := hmeet
    rw [connectedComponentIn_eq hxC]
    exact hT.subset_connectedComponentIn hxT hTS
  let pS := R.coordinate_map (q, t)
  have hpS : pS ∈ S := ⟨q, rfl⟩
  have hpOmega : pS ∈ Omega := by
    rw [← hcover]
    exact Or.inl (Or.inr hpS)
  have hC1Omega : C1.carrier ⊆ Omega := by
    change C1.carrier ⊆ connectedComponent R.center
    rw [connectedComponent_eq hpOmega]
    exact C1.m25_isConnected_carrier.subset_connectedComponent (C1.end_neck_subset (hSN hpS))
  have hK1B : C1.closed_core ⊆ B := by
    intro x hx
    have hxcover := hC1Omega (hK1C hx)
    rw [← hcover] at hxcover
    rcases hxcover with (hxA | hxS) | hxB
    · exact (disjoint_left.mp hcores
        (hcore0K (hAclcore (subset_closure hxA))) hx).elim
    · exact (disjoint_left.mp hcores (hcore0K (hScore hxS)) hx).elim
    · exact hxB
  obtain ⟨x1, hx1core⟩ := C1.core_nonempty
  have hx1K : x1 ∈ C1.closed_core := hcore1K hx1core
  have hx1B : x1 ∈ B := hK1B hx1K

  let Uell := C1.closed_core ∪ N.region (-L) ell
  have hell1 : ell ∈ Ioo (-C1.epsilon⁻¹) C1.epsilon⁻¹ := by
    simpa only [hepsilon] using hell
  have hUellPre : IsPreconnected Uell := by
    obtain ⟨heq, _, _, _⟩ := C1.end_neck_lower_cut_eq_negative_component hell1
    have hpre : IsPreconnected
        (C1.closed_core ∪ C1.end_neck.region (-C1.epsilon⁻¹) ell) := by
      rw [heq]
      exact isPreconnected_connectedComponentIn
    simpa only [hepsilon] using hpre
  have hUellAvoid : Uell ⊆ Sᶜ := by
    rintro x (hxK | hxlow) hxS
    · exact disjoint_left.mp hK1N hxK (hSN hxS)
    · have hlt := hxlow.2.2.trans (hellf (N.coordinate_inverse x).1)
      exact hlt.ne ((hSmem x).mp hxS).2
  have hUellB : Uell ⊆ B :=
    hside hUellPre hUellAvoid ⟨x1, Or.inl hx1K, hx1B⟩
  let s := (ell - L) / 2
  have hs : -L < s ∧ s < ell := by
    dsimp only [s]
    constructor <;> linarith only [hell.1]
  have hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [hN]
    exact ⟨hs.1, hs.2.trans hell.2⟩
  have hwLow : N.coordinate_map (q, s) ∈ N.region (-L) ell := by
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hsN⟩, ?_⟩
    rw [N.coordinate_inverse_map (q, s) hsN]
    exact hs
  have hwMinus : N.coordinate_map (q, s) ∈ Gminus :=
    ⟨(q, s), ⟨hs.1, hs.2.trans (hellf q)⟩, rfl⟩
  have hminusB : Gminus ⊆ B := hside hminusConnected.isPreconnected hminusAvoid
    ⟨N.coordinate_map (q, s), hwMinus, hUellB (Or.inr hwLow)⟩
  obtain ⟨x2, hx2N, hx2A⟩ := mem_closure_iff.mp (hSclA hpS)
    N.carrier N.carrier_open (hSN hpS)
  have hx2Plus : x2 ∈ Gplus := by
    rcases hNcover hx2N with (hxminus | hxS) | hxplus
    · exact (disjoint_left.mp hAB hx2A (hminusB hxminus)).elim
    · exact (hAsub hx2A hxS).elim
    · exact hxplus
  have hplusA : Gplus ⊆ A :=
    hside hplusConnected.isPreconnected hplusAvoid ⟨x2, hx2Plus, hx2A⟩
  let Ur := C1.closed_core ∪ N.region (-L) r
  let Kr := C1.carrier \ N.region r L
  have hr1 : r ∈ Ioo (-C1.epsilon⁻¹) C1.epsilon⁻¹ := by
    simpa only [hepsilon] using hr
  obtain ⟨hKrC, hUrOpen, hUrclosure, _, hUrfront, _, _⟩ :=
    C1.end_neck_lower_cut_topology hr1
  simp only [hepsilon] at hKrC hUrOpen hUrclosure hUrfront
  change Kr ⊆ C1.carrier at hKrC
  change IsOpen Ur at hUrOpen
  change closure Ur = Kr at hUrclosure
  change frontier Ur = N.coordinate_map '' (univ ×ˢ ({r} : Set ℝ)) at hUrfront
  have hKrCompact : IsCompact Kr := by
    simpa only [hepsilon] using C1.isCompact_end_neck_lower_cut hr1
  have hUrfrontA : frontier Ur ⊆ A := by
    intro x hx
    rw [hUrfront] at hx
    rcases hx with ⟨⟨v, z⟩, ⟨_, hz⟩, rfl⟩
    have hz' : z = r := hz
    subst z
    exact hplusA ⟨(v, r), ⟨hfr v, hrUpper⟩, rfl⟩
  have hBUr : B ⊆ Ur := by
    have hBpre : IsPreconnected B := isPreconnected_connectedComponentIn
    apply hBpre.subset_of_closure_inter_subset hUrOpen ⟨x1, hx1B, Or.inl hx1K⟩
    intro x hx
    by_contra hxout
    have hxf : x ∈ frontier Ur := by
      rw [hUrOpen.frontier_eq]
      exact ⟨hx.1, hxout⟩
    exact disjoint_left.mp hAB (hUrfrontA hxf) hx.2
  have hBclKr : closure B ⊆ Kr := by
    rw [← hUrclosure]
    exact closure_mono hBUr
  have hBcompact : IsCompact (closure B) :=
    hKrCompact.of_isClosed_subset isClosed_closure hBclKr
  have hBclC1 : closure B ⊆ C1.carrier := hBclKr.trans hKrC
  have hclA : closure A = A ∪ S := by rw [closure_eq_self_union_frontier, hAfront]
  have hclB : closure B = B ∪ S := by rw [closure_eq_self_union_frontier, hBfront]
  have hOmegaClosure : Omega = closure A ∪ closure B := by
    rw [hclA, hclB, ← hcover]
    apply Subset.antisymm
    · rintro x (hxAS | hxB)
      · exact Or.inl hxAS
      · exact Or.inr (Or.inl hxB)
    · rintro x (hxAS | (hxB | hxS))
      · exact Or.inl hxAS
      · exact Or.inr hxB
      · exact Or.inl (Or.inr hxS)
  have hOmegaCompact : IsCompact Omega := by
    rw [hOmegaClosure]
    exact hAcompact.union hBcompact
  have hOmegaClopen : IsClopen Omega := isClopen_connectedComponent
  have hOmegaConnected : IsConnected Omega := isConnected_connectedComponent
  have hOmegaCaps : Omega ⊆ C0.carrier ∪ C1.carrier := by
    rw [hOmegaClosure]
    exact union_subset
      (fun _ hx => Or.inl (C0.m25_core_subset_carrier (hAclcore hx)))
      (fun _ hx => Or.inr (hBclC1 hx))
  have hC0Omega : C0.carrier ⊆ Omega := by
    change C0.carrier ⊆ connectedComponent R.center
    rw [connectedComponent_eq hpOmega]
    exact C0.m25_isConnected_carrier.subset_connectedComponent
      (C0.m25_core_subset_carrier (hScore hpS))
  have hcapsOmega : C0.carrier ∪ C1.carrier = Omega :=
    Subset.antisymm (union_subset hC0Omega hC1Omega) hOmegaCaps
  apply hnotGood
  apply hpack
  · simpa only [hcapsOmega] using hOmegaCompact
  · simpa only [hcapsOmega] using hOmegaClopen
  · simpa only [hcapsOmega] using hOmegaConnected
  · exact ⟨R.center, hcapsOmega⟩

end PoincareConjecture
