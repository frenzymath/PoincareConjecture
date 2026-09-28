import PoincareConjecture.Proofs.M25.AppA_21_Local.CylinderExteriorTail
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCommonSphereProducer
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapLastSliceCores
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapChainIntersection











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem CapCertificate.exists_opposite_tube_tail_of_finite_core_frontier :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C0 C1 : CapCertificate g) (D : BalancedNeckChain g C0.epsilon)
        {b : ℤ},
      C0.epsilon ≤ epsilon0 → C1.epsilon = C0.epsilon →
      D.shape = ChainShape.finite 0 b → D.neck 0 = C0.end_neck →
      (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) →
      (∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∉ C0.carrier) →
      (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
        closure ((D.neck i).region (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹) ⊆
            (D.neck (i + 1)).carrier ∧
          closure ((D.neck (i + 1)).region
              (-C0.epsilon⁻¹) (-C0.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) →
      (¬ (C0.carrier \ C0.end_neck.region
        (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹ ⊆ C1.core)) →
      ∀ K : CappedTubeCertificate g,
      K.cap = C0 →
      K.tube.carrier = (⋃ i ∈ D.shape.active, (D.neck i).carrier) →
      Disjoint C0.closed_core C1.closed_core →
      ∀ y : M, y ∈ C1.core →
      y ∈ closure ((D.neck b).region 0 C0.epsilon⁻¹) →
      y ∉ K.carrier → (K.carrier ∩ C1.boundary_sphere).Nonempty →
      ∃ (side : Bool) (t a0 a1 : ℝ),
        t ∈ Ioo (-C0.epsilon⁻¹) 0 ∧
        a0 ∈ Ioo (0 : ℝ) 1 ∧ a1 ∈ Ioo (0 : ℝ) 1 ∧
        K.tube.cylinder.tail side a0 ⊆
          C0.end_neck.region (-C0.epsilon⁻¹) t ∧
        K.tube.cylinder.tail (!side) a1 ⊆ C1.carrier ∧
        Nonempty (CapTubeAttachment C0 K.tube side) := by
  obtain ⟨epsilon0, hpos, hcap, hgraph⟩ :=
    CapCertificate.exists_common_outward_graph_of_finite_core_frontier.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g C0 C1 D b hsmall hepsilon hshape hstart hsep
    hcenters hquarters hno K hKcap hKU hcores y hycore hyclosure hyout hmeet
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let L := C0.epsilon⁻¹
  let U : Set M := ⋃ i ∈ D.shape.active, (D.neck i).carrier
  let V : Set M := C0.carrier ∪ U
  let T := K.tube.cylinder
  have hL : 0 < L := inv_pos.mpr C0.epsilon_pos
  have hnonneg : (0 : ℤ) ≤ b := by
    obtain ⟨i, hi⟩ := D.active_nonempty
    rw [hshape] at hi
    exact hi.1.trans hi.2
  have hzero : (0 : ℤ) ∈ D.shape.active := by
    rw [hshape]
    exact ⟨le_rfl, hnonneg⟩
  have hb : b ∈ D.shape.active := by
    rw [hshape]
    exact ⟨hnonneg, le_rfl⟩
  have hfirst : ∀ i ∈ D.shape.active, (0 : ℤ) ≤ i := by
    intro i hi
    rw [hshape] at hi
    exact hi.1
  have hNU : C0.end_neck.carrier ⊆ U := by
    intro x hx
    exact mem_iUnion₂.mpr ⟨0, hzero, by simpa only [hstart] using hx⟩
  have hlastU : (D.neck b).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨b, hb, hx⟩
  have hinter : C0.carrier ∩ U = C0.end_neck.carrier :=
    C0.inter_chain_union_eq_end_neck D hzero hfirst hstart hcenters
  have hcoreC : C0.closed_core ⊆ C0.carrier := by
    rw [C0.closed_core_eq_complement_end]
    exact sdiff_subset
  have hcoreU : Disjoint C0.closed_core U := by
    apply disjoint_left.mpr
    intro x hxCore hxU
    rw [C0.closed_core_eq_complement_end] at hxCore
    apply hxCore.2
    rw [← hinter]
    exact ⟨hxCore.1, hxU⟩
  have hVU : V \ U = C0.closed_core := by
    ext x
    constructor
    · rintro ⟨hxC | hxU, hxout⟩
      · rw [C0.closed_core_eq_complement_end]
        exact ⟨hxC, fun hxN => hxout (hNU hxN)⟩
      · exact False.elim (hxout hxU)
    · intro hx
      exact ⟨Or.inl (hcoreC hx), fun hxU => disjoint_left.mp hcoreU hx hxU⟩
  have hKcarrier : K.carrier = V := by
    simpa only [V, U, hKcap, hKU] using K.carrier_eq_union
  have hyVout : y ∉ V := fun hy => hyout (hKcarrier.symm ▸ hy)
  have hboundary : (V ∩ C1.boundary_sphere).Nonempty := by
    simpa only [hKcarrier] using hmeet
  obtain ⟨_, _, _, _, R, f, N, s, hR, _, _, hRs, hRcore, _, hf, hfdom,
    _, hlevel, hSV, hcases⟩ :=
    hgraph C0 C1 D hsmall hepsilon hshape hstart hsep hcenters hquarters hno
      y hycore hyclosure hyVout hboundary
  let S := range (fun q : UnitTwoSphere => R.coordinate_map (q, f q))
  let Acore := connectedComponentIn Sᶜ
    (R.coordinate_map ((R.coordinate_inverse R.center).1, -C1.epsilon⁻¹ / 2))
  change S ⊆ V at hSV
  obtain ⟨hside, hAcFormula, hAcCompact, hAcC1, _, _, _, _, hAcFront, _⟩ :=
    C1.outward_graph_compact_side R hR hRcore f hf.continuous hfdom
  change C1.core ∪ R.coordinate_map ''
      {z : RoundCylinderSpace | -C1.epsilon⁻¹ < z.2 ∧ z.2 < f z.1} = Acore at hside
  change closure Acore = C1.closed_core ∪ R.coordinate_map ''
      {z : RoundCylinderSpace | 0 ≤ z.2 ∧ z.2 ≤ f z.1} at hAcFormula
  change IsCompact (closure Acore) at hAcCompact
  change closure Acore ⊆ C1.carrier at hAcC1
  change frontier Acore = S at hAcFront
  have hSclosed : IsClosed S := by rw [← hAcFront]; exact isClosed_frontier
  have hAcOpen : IsOpen Acore := hSclosed.isOpen_compl.connectedComponentIn
  have hAcFrontCompact : IsCompact (frontier Acore) :=
    hAcCompact.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hcoreAc : C1.core ⊆ Acore := by
    intro x hx
    rw [← hside]
    exact Or.inl hx
  have hC1coreClosed : C1.core ⊆ C1.closed_core := by
    rw [C1.core_eq_interior_closed_core]
    exact interior_subset
  have hboundaryCore : C1.boundary_sphere ⊆ C1.closed_core := by
    rw [← C1.core_frontier_eq_boundary]
    exact C1.closed_core_compact.isClosed.frontier_subset
  have hgeometric : S ⊆ U ∧ Disjoint C0.closed_core (closure Acore) := by
    rcases hcases with hfull | hmixed
    · obtain ⟨_, _, _, hfzero⟩ := hfull
      have hSboundary : S = C1.boundary_sphere := by
        simpa only [S, hfzero] using R.coordinate_zero_range.trans hRs
      have hclosureEq : closure Acore = C1.closed_core := by
        rw [hAcFormula]
        apply union_eq_left.mpr
        rintro x ⟨⟨q, r⟩, hz, rfl⟩
        have hrle : r ≤ 0 := by simpa only [hfzero] using hz.2
        have hrzero : r = 0 := le_antisymm hrle hz.1
        subst r
        apply hboundaryCore
        rw [← hRs, ← R.coordinate_zero_range]
        exact ⟨q, rfl⟩
      refine ⟨?_, by simpa only [hclosureEq] using hcores⟩
      intro x hxS
      by_contra hxU
      have hx0 : x ∈ C0.closed_core := hVU ▸ ⟨hSV hxS, hxU⟩
      exact disjoint_left.mp hcores hx0 (hboundaryCore (hSboundary ▸ hxS))
    · obtain ⟨_, _, _, _, _, _, _, hN, hs, _, _⟩ := hmixed
      have ht : 3 * L / 4 ∈ Ioo (L / 2) L := by
        constructor <;> linarith only [hL]
      have htDom : 3 * L / 4 ∈ Ioo (-L) L := by
        constructor <;> linarith only [hL]
      have hlevelLast :
          range (fun q : UnitTwoSphere => (D.neck b).coordinate_map (q, 3 * L / 4)) =
            S := by
        simpa only [hN, hs, L, S] using hlevel.symm
      have hSU : S ⊆ U := by
        rw [← hlevelLast]
        rintro x ⟨q, rfl⟩
        apply hlastU
        apply (D.neck b).coordinate_map_mem
        refine ⟨mem_univ _, ?_⟩
        simpa only [D.epsilon_eq b hb] using htDom
      let q := ((D.neck b).coordinate_inverse (D.neck b).center).1
      let Aminus := connectedComponentIn Sᶜ
        ((D.neck b).coordinate_map (q, (3 * L / 4 - L) / 2))
      let Bplus := connectedComponentIn Sᶜ
        ((D.neck b).coordinate_map (q, (3 * L / 4 + L) / 2))
      let K0 := C0.carrier \ C0.end_neck.region (L / 2) L
      obtain ⟨hnegative, hpositive, _, _⟩ :=
        C0.closed_cores_disjoint_of_last_slice_outward_graph C1 D hshape hstart
          hsep ht R hR hRcore f hf.continuous hfdom hlevelLast y hycore hyclosure hyVout
      change K0 ⊆ connectedComponentIn
        (range (fun v : UnitTwoSphere => (D.neck b).coordinate_map (v, 3 * L / 4)))ᶜ
          ((D.neck b).coordinate_map (q, (3 * L / 4 - L) / 2)) at hnegative
      change C1.closed_core ⊆ closure (connectedComponentIn
        (range (fun v : UnitTwoSphere => (D.neck b).coordinate_map (v, 3 * L / 4)))ᶜ
          ((D.neck b).coordinate_map (q, (3 * L / 4 + L) / 2))) at hpositive
      rw [hlevelLast] at hnegative hpositive
      have hK0A : K0 ⊆ Aminus := hnegative
      have hC1B : C1.closed_core ⊆ closure Bplus := hpositive
      obtain ⟨w, hwAc, hwB⟩ := mem_closure_iff.mp (hC1B (hC1coreClosed hycore))
        Acore hAcOpen (hcoreAc hycore)
      have hAB : Acore = Bplus :=
        (connectedComponentIn_eq hwAc).trans (connectedComponentIn_eq hwB).symm
      obtain ⟨H, _, hH, _, _, hcomponents, _⟩ :=
        D.exists_ordered_saturated_heights hsep
      obtain ⟨hAeq, hBeq, _⟩ := hcomponents b hb (3 * L / 4) htDom
      change connectedComponentIn
        (range (fun v : UnitTwoSphere => (D.neck b).coordinate_map (v, 3 * L / 4)))ᶜ
          ((D.neck b).coordinate_map (q, (3 * L / 4 - L) / 2)) =
            connectedComponent (D.neck b).center ∩ (H b) ⁻¹' Iio (3 * L / 4) at hAeq
      change connectedComponentIn
        (range (fun v : UnitTwoSphere => (D.neck b).coordinate_map (v, 3 * L / 4)))ᶜ
          ((D.neck b).coordinate_map (q, (3 * L / 4 + L) / 2)) =
            connectedComponent (D.neck b).center ∩ (H b) ⁻¹' Ioi (3 * L / 4) at hBeq
      rw [hlevelLast] at hAeq hBeq
      change Aminus = connectedComponent (D.neck b).center ∩
        (H b) ⁻¹' Iio (3 * L / 4) at hAeq
      change Bplus = connectedComponent (D.neck b).center ∩
        (H b) ⁻¹' Ioi (3 * L / 4) at hBeq
      have hHcont : Continuous (H b) := (hH b hb).1
      have hclosureB : closure Bplus ⊆ {x | 3 * L / 4 ≤ H b x} := by
        apply closure_minimal ?_ (isClosed_le continuous_const hHcont)
        intro x hx
        rw [hBeq] at hx
        exact (show 3 * L / 4 < H b x from hx.2).le
      refine ⟨hSU, ?_⟩
      rw [hAB]
      apply disjoint_left.mpr
      intro x hx0 hxB
      have hxK0 : x ∈ K0 := by
        rw [C0.closed_core_eq_complement_end] at hx0
        exact ⟨hx0.1, fun hx => hx0.2 hx.1⟩
      have hxA := hK0A hxK0
      rw [hAeq] at hxA
      exact (not_le_of_gt (show H b x < 3 * L / 4 from hxA.2)) (hclosureB hxB)
  obtain ⟨hSU, hcoreAcDisjoint⟩ := hgeometric
  have htailU (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
      T.tail side a ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    have hdom : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
      cases side
      · exact ⟨hz.1, hz.2.1, hz.2.2.trans ha.2⟩
      · exact ⟨hz.1, ha.1.trans hz.2.1, hz.2.2⟩
    have hm := (T.homeomorph (z.1, ⟨z.2, hdom.2⟩)).property
    rw [T.coordinate_eq] at hm
    have hm' : T.coordinate z ∈ K.tube.carrier := by
      simpa only [Prod.fst, Prod.snd] using hm
    simpa only [hKU] using hm'
  let H0 : M → ℝ := fun x =>
    if x ∈ C0.end_neck.carrier then (C0.end_neck.coordinate_inverse x).2
    else if x ∈ C0.carrier then -L else L
  have hH0 : Continuous H0 := C0.continuous_saturated_end_height
  have hcoord0 (x : M) (hx : x ∈ C0.end_neck.carrier) :
      (C0.end_neck.coordinate_inverse x).2 ∈ Ioo (-L) L := by
    simpa only [C0.end_neck_epsilon] using (C0.end_neck.coordinate_inverse_mem x hx).2
  have hH0end {x : M} (hx : x ∈ C0.end_neck.carrier) :
      H0 x = (C0.end_neck.coordinate_inverse x).2 := by
    simp only [H0, if_pos hx]
  have hH0core {x : M} (hx : x ∈ C0.closed_core) : H0 x = -L := by
    rw [C0.closed_core_eq_complement_end] at hx
    simp only [H0, if_neg hx.2, if_pos hx.1]
  have hH0out {x : M} (hx : x ∉ C0.carrier) : H0 x = L := by
    have hxN : x ∉ C0.end_neck.carrier := fun hxN => hx (C0.end_neck_subset hxN)
    simp only [H0, if_neg hxN, if_neg hx]
  have hH0lower (x : M) (hx : x ∉ C0.closed_core) : -L < H0 x := by
    by_cases hxN : x ∈ C0.end_neck.carrier
    · rw [hH0end hxN]
      exact (hcoord0 x hxN).1
    · have hxC : x ∉ C0.carrier := by
        intro hxC
        apply hx
        rw [C0.closed_core_eq_complement_end]
        exact ⟨hxC, hxN⟩
      rw [hH0out hxC]
      linarith only [hL]
  obtain ⟨d, hd, hdBound⟩ := hAcCompact.exists_forall_le' hH0.continuousOn
    (a := -L) (fun x hx => hH0lower x
      (fun hx0 => disjoint_left.mp hcoreAcDisjoint hx0 hx))
  obtain ⟨t, htLow, htMin⟩ := exists_between (lt_min hd (neg_lt_zero.mpr hL))
  have htZero : t < 0 := htMin.trans_le (min_le_right _ _)
  have htd : t < d := htMin.trans_le (min_le_left _ _)
  have htDom : t ∈ Ioo (-L) L := ⟨htLow, htZero.trans hL⟩
  have htNeck : t ∈ Ioo (-C0.end_neck.epsilon⁻¹) C0.end_neck.epsilon⁻¹ := by
    simpa only [C0.end_neck_epsilon] using htDom
  let A0 := C0.closed_core ∪ C0.end_neck.region (-L) t
  have hcut := C0.end_neck_lower_cut_topology htDom
  have hA0open : IsOpen A0 := hcut.2.1
  have hA0front : frontier A0 =
      C0.end_neck.coordinate_map '' (univ ×ˢ ({t} : Set ℝ)) := hcut.2.2.2.2.1
  have hA0frontCompact : IsCompact (frontier A0) := by
    rw [hA0front]
    simpa only [Icc_self] using
      C0.end_neck.isCompact_coordinate_slab htNeck.1 htNeck.2
  have hA0frontU : frontier A0 ⊆ U := by
    rw [hA0front]
    rintro x ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hst : s = t := hs
    subst s
    exact hNU (C0.end_neck.coordinate_map_mem ⟨mem_univ _, htNeck⟩)
  have hA0height (x : M) (hx : x ∈ A0) : H0 x < t := by
    rcases hx with hxCore | hxEnd
    · rw [hH0core hxCore]
      exact htLow
    · rw [hH0end hxEnd.1]
      exact hxEnd.2.2
  have hA0Ac : Disjoint A0 (closure Acore) := by
    apply disjoint_left.mpr
    intro x hx0 hxAc
    exact (not_lt_of_ge (hdBound x hxAc)) ((hA0height x hx0).trans htd)
  let p := C0.boundary_neck.center
  have hpBoundary : p ∈ C0.boundary_sphere := by
    rw [C0.boundary_eq_neck_sphere]
    exact C0.boundary_neck.center_on_central_sphere
  have hpCore : p ∈ C0.closed_core := by
    apply C0.closed_core_compact.isClosed.frontier_subset
    rw [C0.core_frontier_eq_boundary]
    exact hpBoundary
  have hpOut : p ∉ U := fun hpU => disjoint_left.mp hcoreU hpCore hpU
  have hpClosure : p ∈ closure U :=
    closure_mono (fun _ hx => hNU hx.1)
      (C0.boundary_subset_closure_end_region htDom hpBoundary)
  obtain ⟨side0, a0, ha0, htail0⟩ :=
    T.exists_tail_subset_of_compact_frontier hA0open hA0frontCompact
      (by rw [hKU]; exact hA0frontU) p (Or.inl hpCore)
      (by rw [hKU]; exact hpClosure) (by rw [hKU]; exact hpOut)
  have htail0negative : T.tail side0 a0 ⊆ C0.end_neck.region (-L) t := by
    intro x hx
    rcases htail0 hx with hxCore | hxEnd
    · exact False.elim (disjoint_left.mp hcoreU hxCore (htailU side0 ha0 hx))
    · exact hxEnd
  have hyClosureU : y ∈ closure U :=
    closure_mono (fun _ hx => hlastU hx.1) hyclosure
  have hyOutU : y ∉ U := fun hyU => hyVout (Or.inr hyU)
  obtain ⟨side1, a1, ha1, htail1⟩ :=
    T.exists_tail_subset_of_compact_frontier hAcOpen hAcFrontCompact
      (by rw [hKU, hAcFront]; exact hSU) y (hcoreAc hycore)
      (by rw [hKU]; exact hyClosureU) (by rw [hKU]; exact hyOutU)
  have htail1cap : T.tail side1 a1 ⊆ C1.carrier :=
    htail1.trans (subset_closure.trans hAcC1)
  have hne : side1 ≠ side0 := by
    intro hsides
    have hcommon : (T.tail side0 a0 ∩ T.tail side1 a1).Nonempty := by
      subst side1
      let q := (C0.end_neck.coordinate_inverse C0.end_neck.center).1
      cases side0
      · let v := min a0 a1 / 2
        have hv0 : 0 < v := half_pos (lt_min ha0.1 ha1.1)
        have hvMin : v < min a0 a1 := half_lt_self (lt_min ha0.1 ha1.1)
        refine ⟨T.coordinate (q, v), ?_, ?_⟩
        · exact ⟨(q, v), ⟨mem_univ _, hv0, hvMin.trans_le (min_le_left _ _)⟩, rfl⟩
        · exact ⟨(q, v), ⟨mem_univ _, hv0, hvMin.trans_le (min_le_right _ _)⟩, rfl⟩
      · let v := (max a0 a1 + 1) / 2
        have hmax : max a0 a1 < 1 := max_lt ha0.2 ha1.2
        have hvMax : max a0 a1 < v := by dsimp only [v]; linarith only [hmax]
        have hv1 : v < 1 := by dsimp only [v]; linarith only [hmax]
        refine ⟨T.coordinate (q, v), ?_, ?_⟩
        · exact ⟨(q, v), ⟨mem_univ _, (le_max_left _ _).trans_lt hvMax, hv1⟩, rfl⟩
        · exact ⟨(q, v), ⟨mem_univ _, (le_max_right _ _).trans_lt hvMax, hv1⟩, rfl⟩
    obtain ⟨x, hx0, hx1⟩ := hcommon
    exact disjoint_left.mp hA0Ac (htail0 hx0) (subset_closure (htail1 hx1))
  have hsideOpposite : side1 = !side0 := by
    cases side0 <;> cases side1
    · exact (hne rfl).elim
    · rfl
    · rfl
    · exact (hne rfl).elim
  have htailOpposite : T.tail (!side0) a1 ⊆ C1.carrier := by
    rw [← hsideOpposite]
    exact htail1cap
  have hattachment : CapTubeAttachment C0 K.tube K.attachment_side := by
    simpa only [hKcap] using K.attachment
  let firstAttachment : CapTubeAttachment C0 K.tube side0 := {
    overlap_model := hattachment.overlap_model
    tube_tail := ⟨a0, ha0,
      fun _ hx => C0.end_neck_subset (htail0negative hx).1⟩
    cap_tail := hattachment.cap_tail }
  exact ⟨side0, t, a0, a1, ⟨htLow, htZero⟩, ha0, ha1,
    htail0negative, htailOpposite, ⟨firstAttachment⟩⟩

end PoincareConjecture
