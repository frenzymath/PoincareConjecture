import PoincareConjecture.Proofs.M25.AppA_1_Necks.MiddleFrontier
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicFiniteChain
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.RelativeSuccessorHeight
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Int.Init

set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff
universe u
namespace PoincareConjecture.BalancedNeckChain

theorem exists_terminal_isSeparating_of_backward_chain :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) (b : ℤ),
      C.shape = ChainShape.backward b → epsilon ≤ epsilon0 →
      (closure ((C.neck (b - 1)).region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆
          (C.neck b).carrier ∧
        closure ((C.neck b).region
            (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆ (C.neck (b - 1)).carrier) →
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        ((C.neck (i + 1)).center ∈
              closure ((C.neck i).region 0 epsilon⁻¹) ∧
            (C.neck (i + 1)).center ∉ (C.neck i).carrier) ∨
          ((C.neck i).center ∈
              closure ((C.neck (i + 1)).region (-epsilon⁻¹) 0) ∧
            (C.neck i).center ∉ (C.neck (i + 1)).carrier)) →
      (C.neck b).IsSeparating := by
  obtain ⟨epsilonM, hMpos, hMcap, hfrontier⟩ :=
    exists_frontier_subset_exposed_end_closures.{u}
  obtain ⟨epsilonH, hHpos, _, hsuccessor⟩ :=
    EpsilonNeck.exists_relative_successor_height_continuity.{u}
  refine ⟨min epsilonM epsilonH, lt_min hMpos hHpos,
    (min_le_left _ _).trans hMcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C b hshape heps hquarters hincidence
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := epsilon⁻¹
  let N := C.neck b
  let R := C.neck (b - 1)
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let V : Set M := ⋃ i ∈ Iic (b - 1), (C.neck i).carrier
  let G : M → ℝ := fun x =>
    if x ∈ N.carrier then (N.coordinate_inverse x).2 else -L
  have heM : epsilon ≤ epsilonM := heps.trans (min_le_left _ _)
  have heH : epsilon ≤ epsilonH := heps.trans (min_le_right _ _)
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ≤ b := by
    rw [hshape]
    rfl
  have hb : b ∈ C.shape.active := (hactive b).mpr le_rfl
  have hbprev : b - 1 ∈ C.shape.active := (hactive (b - 1)).mpr (by omega)
  have hNe : N.epsilon = epsilon := C.epsilon_eq b hb
  have hRe : R.epsilon = epsilon := C.epsilon_eq (b - 1) hbprev
  have hepos : 0 < epsilon := hNe ▸ N.epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hcarrierU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hNU : N.carrier ⊆ U := hcarrierU b hb
  have hRU : R.carrier ⊆ U := hcarrierU (b - 1) hbprev
  have hGin (x : M) (hx : x ∈ N.carrier) :
      G x = (N.coordinate_inverse x).2 := by
    simp only [G, if_pos hx]
  have hGout (x : M) (hx : x ∉ N.carrier) : G x = -L := by
    simp only [G, if_neg hx]
  change closure (R.region (L / 2) L) ⊆ N.carrier ∧
    closure (N.region (-L) (-L / 2)) ⊆ R.carrier at hquarters

  let restrict (s : ChainShape) (hs : s.active.Nonempty)
      (hsub : s.active ⊆ C.shape.active) : BalancedNeckChain g epsilon := {
    shape := s
    neck := C.neck
    source_necks := C.source_necks
    selected := fun i hi => C.selected i (hsub hi)
    active_nonempty := hs
    epsilon_eq := fun i hi => C.epsilon_eq i (hsub hi)
    centers_distinct := by
      intro i hi j hj hij
      exact C.centers_distinct (hsub hi) (hsub hj) hij
    adjacent_overlap := fun i hi hn => C.adjacent_overlap i (hsub hi) (hsub hn)
    overlap_contains_quarters := fun i hi hn =>
      C.overlap_contains_quarters i (hsub hi) (hsub hn)
    overlap_within_three_quarters := fun i hi hn =>
      C.overlap_within_three_quarters i (hsub hi) (hsub hn)
    later_disjoint_negative_end := fun i hi j hj hij =>
      C.later_disjoint_negative_end i (hsub hi) j (hsub hj) hij
    balanced_center_distance := fun i hi hn =>
      C.balanced_center_distance i (hsub hi) (hsub hn) }
  have hfinite (j : ℤ) (hjb : j ≤ b) :
      ContinuousOn G (⋃ i ∈ Icc j b, (C.neck i).carrier) := by
    let Cj := restrict (.finite j b) ⟨j, le_rfl, hjb⟩
      (fun i hi => (hactive i).mpr hi.2)
    let Uj : Set M := ⋃ i ∈ Icc j b, (C.neck i).carrier
    let P : ℤ → Prop := fun i => ∃ F : M → ℝ,
      ContinuousOn F Uj ∧
      (∀ x ∈ (C.neck i).carrier, F x = ((C.neck i).coordinate_inverse x).2) ∧
      (∀ x ∈ Uj, x ∉ (C.neck i).carrier → F x = -L ∨ F x = L) ∧
      (∀ x ∈ ⋃ k ∈ Icc j i, (C.neck k).carrier,
        x ∉ (C.neck i).carrier → F x = -L)
    have hNUj (i : ℤ) (hi : i ∈ Icc j b) : (C.neck i).carrier ⊆ Uj :=
      fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
    have hbase : P j := by
      refine ⟨fun x => if x ∈ (C.neck j).carrier then
        ((C.neck j).coordinate_inverse x).2 else L, ?_, ?_, ?_, ?_⟩
      · exact (Cj.continuousOn_initial_height_of_finite rfl).1
      · intro x hx
        simp only [if_pos hx]
      · intro x _ hx
        exact Or.inr (if_neg hx)
      · intro x hx hxout
        obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
        have hkj : k = j := le_antisymm hk.2 hk.1
        exact False.elim (hxout (by simpa only [hkj] using hxk))
    have hadvance (i : ℤ) (hi : i ∈ Icc j b) (hn : i + 1 ∈ Icc j b)
        (h : P i) : P (i + 1) := by
      obtain ⟨F, hFc, hFin, hFout, hFpast⟩ := h
      have hiC : i ∈ C.shape.active := (hactive i).mpr hi.2
      have hnC : i + 1 ∈ C.shape.active := (hactive (i + 1)).mpr hn.2
      have hei := C.epsilon_eq i hiC
      have hen := C.epsilon_eq (i + 1) hnC
      have hNi : (C.neck i).epsilon ≤ epsilonH := by
        rw [hei]
        exact heH
      have hquarter :
          (C.neck i).region ((C.neck i).epsilon⁻¹ / 2) (C.neck i).epsilon⁻¹ ⊆
            (C.neck (i + 1)).carrier := by
        simpa only [hei] using (C.overlap_contains_quarters i hiC hnC).1
      have hoverlap : (C.neck i).carrier ∩ (C.neck (i + 1)).carrier ⊆
          (C.neck i).region (-(C.neck i).epsilon⁻¹ / 2) (C.neck i).epsilon⁻¹ ∩
            (C.neck (i + 1)).region (-(C.neck i).epsilon⁻¹)
              ((C.neck i).epsilon⁻¹ / 2) := by
        simpa only [hei] using C.overlap_within_three_quarters i hiC hnC
      let Fnext : M → ℝ := fun x => if x ∈ (C.neck (i + 1)).carrier then
        ((C.neck (i + 1)).coordinate_inverse x).2
        else if F x < 3 * L / 4 then -L else L
      refine ⟨Fnext, ?_, ?_, ?_, ?_⟩
      · have hc := hsuccessor (C.neck i) (C.neck (i + 1)) hNi
          (hen.trans hei.symm) hquarter hoverlap Uj (hNUj i hi) (hNUj (i + 1) hn)
          F hFc hFin (by simpa only [hei] using hFout)
        simpa only [Fnext, L, hei] using hc
      · intro x hx
        simp only [Fnext, if_pos hx]
      · intro x _ hx
        dsimp only [Fnext]
        rw [if_neg hx]
        by_cases hf : F x < 3 * L / 4
        · exact Or.inl (if_pos hf)
        · exact Or.inr (if_neg hf)
      · intro x hx hxout
        obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
        have hkne : k ≠ i + 1 := by
          intro hki
          exact hxout (by simpa only [hki] using hxk)
        have hkupper : k ≤ i + 1 := hk.2
        have hki : k ≤ i := by omega
        have hxpast : x ∈ ⋃ k ∈ Icc j i, (C.neck k).carrier :=
          mem_iUnion₂.mpr ⟨k, ⟨hk.1, hki⟩, hxk⟩
        have hbelow : F x < 3 * L / 4 := by
          by_cases hxold : x ∈ (C.neck i).carrier
          · have hxcoord : ((C.neck i).coordinate_inverse x).2 ∈ Ioo (-L) L := by
              simpa only [hei] using ((C.neck i).coordinate_inverse_mem x hxold).2
            have hhalf : ((C.neck i).coordinate_inverse x).2 ≤ L / 2 := by
              by_contra h
              have hs : L / 2 < ((C.neck i).coordinate_inverse x).2 :=
                lt_of_not_ge h
              exact hxout ((C.overlap_contains_quarters i hiC hnC).1
                ⟨hxold, hs, hxcoord.2⟩)
            rw [hFin x hxold]
            linarith only [hhalf, hL]
          · rw [hFpast x hxpast hxold]
            linarith only [hL]
        simp only [Fnext, if_neg hxout, if_pos hbelow]
    have hexists (i : ℤ) (hi : i ∈ Icc j b) : P i := by
      refine Int.leInduction (m := j) (motive := fun k _ => k ≤ b → P k)
        (fun _ => hbase) ?_ i hi.1 hi.2
      intro k hjk ih hkb
      exact hadvance k ⟨hjk, by omega⟩ ⟨by omega, hkb⟩ (ih (by omega))
    obtain ⟨F, hFc, hFin, _, hFpast⟩ := hexists b ⟨hjb, le_rfl⟩
    apply hFc.congr
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · rw [hGin x hxN]
      exact (hFin x hxN).symm
    · rw [hGout x hxN]
      exact (hFpast x hx hxN).symm
  have hUopen : IsOpen U :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  have hGc : ContinuousOn G U := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
    have hjb : j ≤ b := (hactive j).mp hj
    have hUjopen : IsOpen (⋃ i ∈ Icc j b, (C.neck i).carrier) :=
      isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
    exact (hfinite j hjb).continuousAt
      (hUjopen.mem_nhds (mem_iUnion₂.mpr ⟨j, ⟨le_rfl, hjb⟩, hxj⟩))
  have hzero (x : M) : G x = 0 ↔ x ∈ N.central_sphere := by
    constructor
    · intro hx
      by_cases hxN : x ∈ N.carrier
      · apply (N.mem_central_sphere_iff x).mpr
        exact ⟨hxN, (hGin x hxN).symm.trans hx⟩
      · rw [hGout x hxN] at hx
        linarith only [hL, hx]
    · intro hx
      obtain ⟨hxN, hh⟩ := (N.mem_central_sphere_iff x).mp hx
      exact (hGin x hxN).trans hh
  let Cpast := restrict (.backward (b - 1)) ⟨b - 1, by
    change b - 1 ≤ b - 1
    exact le_rfl⟩ (by
    intro i hi
    apply (hactive i).mpr
    change i ≤ b - 1 at hi
    omega)
  have hfrontV : frontier V ⊆ closure (R.region 0 L) := by
    have hf := hfrontier Cpast heM (by
      intro i hi hn
      change i ≤ b - 1 at hi
      change i + 1 ≤ b - 1 at hn
      exact hincidence i ((hactive i).mpr (by omega))
        ((hactive (i + 1)).mpr (by omega)))
    exact hf
  have hVU : V ⊆ U := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hcarrierU i ((hactive i).mpr (by change i ≤ b - 1 at hi; omega)) hxi

  have hslab (A : EpsilonNeck g) (heA : A.epsilon = epsilon)
      {c d : ℝ} (hc : -L < c) (hd : d < L) :
      IsClosed (A.coordinate_map '' (univ ×ˢ Icc c d)) ∧
        A.coordinate_map '' (univ ×ˢ Icc c d) ⊆ A.carrier := by
    constructor
    · exact (A.isCompact_coordinate_slab (by rw [heA]; exact hc)
        (by rw [heA]; exact hd)).isClosed
    · rintro x ⟨z, hz, rfl⟩
      apply A.coordinate_map_mem
      refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [heA]
      · exact hc.trans_le hz.2.1
      · exact hz.2.2.trans_lt hd
  let Kp := R.coordinate_map '' (univ ×ˢ Icc (0 : ℝ) (L / 2))
  have hKp := hslab R hRe (c := 0) (d := L / 2)
    (by linarith only [hL]) (by linarith only [hL])
  have hposcover : R.region 0 L ⊆ Kp ∪ R.region (L / 2) L := by
    intro x hx
    by_cases hh : (R.coordinate_inverse x).2 ≤ L / 2
    · exact Or.inl ⟨R.coordinate_inverse x,
        ⟨mem_univ _, hx.2.1.le, hh⟩, R.coordinate_map_inverse hx.1⟩
    · exact Or.inr ⟨hx.1, lt_of_not_ge hh, hx.2.2⟩
  have hposclosure : closure (R.region 0 L) ⊆ U := by
    intro x hx
    have hh := closure_mono hposcover hx
    rw [closure_union, hKp.1.closure_eq] at hh
    exact hh.elim (fun h => hRU (hKp.2 h)) (fun h => hNU (hquarters.1 h))
  have hVclosure : closure V ⊆ U := by
    intro x hx
    rw [closure_eq_self_union_frontier] at hx
    exact hx.elim (fun h => hVU h) (fun h => hposclosure (hfrontV h))
  let Km := N.coordinate_map '' (univ ×ˢ Icc (-L / 2) (0 : ℝ))
  have hKm := hslab N hNe (c := -L / 2) (d := 0)
    (by linarith only [hL]) (by linarith only [hL])
  have hnegcover : N.region (-L) 0 ⊆ N.region (-L) (-L / 2) ∪ Km := by
    intro x hx
    by_cases hh : (N.coordinate_inverse x).2 < -L / 2
    · exact Or.inl ⟨hx.1, hx.2.1, hh⟩
    · exact Or.inr ⟨N.coordinate_inverse x,
        ⟨mem_univ _, le_of_not_gt hh, hx.2.2.le⟩, N.coordinate_map_inverse hx.1⟩
  have hnegclosure : closure (N.region (-L) 0) ⊆ U := by
    intro x hx
    have hh := closure_mono hnegcover hx
    rw [closure_union, hKm.1.closure_eq] at hh
    exact hh.elim (fun h => hRU (hquarters.2 h)) (fun h => hNU (hKm.2 h))
  have hUconnected : IsConnected U := by
    apply IsConnected.biUnion_of_chain C.active_nonempty
    · rw [hshape]
      exact ordConnected_Iic
    · intro i _
      exact (C.neck i).isConnected_carrier
    · intro i hi hn
      change i + 1 ∈ C.shape.active at hn
      change ((C.neck i).carrier ∩ (C.neck (i + 1)).carrier).Nonempty
      exact C.adjacent_overlap i hi hn
  have hUcomponent : U ⊆ connectedComponent N.center :=
    hUconnected.subset_connectedComponent (hNU (N.central_sphere_subset
      N.center_on_central_sphere))
  let D := connectedComponent N.center \ N.central_sphere
  let A : Set M := U ∩ G ⁻¹' Iio 0
  have hAopen : IsOpen A := hGc.isOpen_inter_preimage hUopen isOpen_Iio
  have hAD : A ⊆ D := by
    intro x hx
    refine ⟨hUcomponent hx.1, ?_⟩
    intro hxS
    exact (ne_of_lt hx.2) ((hzero x).mpr hxS)
  have hAside : A ⊆ N.region (-L) 0 ∪ V := by
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · left
      have hh : (N.coordinate_inverse x).2 ∈ Ioo (-L) L := by
        simpa only [hNe] using (N.coordinate_inverse_mem x hxN).2
      refine ⟨hxN, hh.1, ?_⟩
      rw [← hGin x hxN]
      exact hx.2
    · right
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx.1
      have hib : i ≤ b := (hactive i).mp hi
      have hine : i ≠ b := by
        intro h
        exact hxN (by simpa only [h] using hxi)
      exact mem_iUnion₂.mpr ⟨i, show i ∈ Iic (b - 1) from by
        change i ≤ b - 1
        omega, hxi⟩
  have hAclosure : closure A ⊆ U := by
    intro x hx
    have hh := closure_mono hAside hx
    rw [closure_union] at hh
    exact hh.elim (fun h => hnegclosure h) (fun h => hVclosure h)
  have hAclD : closure A ∩ D ⊆ A := by
    intro x hx
    have hxU := hAclosure hx.1
    have hle : G x ≤ 0 := by
      by_contra h
      have hpos : 0 < G x := lt_of_not_ge h
      obtain ⟨y, hypos, hyA⟩ := (mem_closure_iff.mp hx.1)
        (U ∩ G ⁻¹' Ioi 0) (hGc.isOpen_inter_preimage hUopen isOpen_Ioi) ⟨hxU, hpos⟩
      exact lt_asymm (show G y < 0 from hyA.2) (show 0 < G y from hypos.2)
    refine ⟨hxU, ?_⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact False.elim (hx.2.2 ((hzero x).mp heq))
  let q := (N.coordinate_inverse N.center).1
  have hpoint (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      N.coordinate_map (q, t) ∈ U ∧ G (N.coordinate_map (q, t)) = t := by
    have htN : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hNe]
      exact ht
    have hxN := N.coordinate_map_mem
      (show (q, t) ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨mem_univ _, htN⟩)
    refine ⟨hNU hxN, ?_⟩
    rw [hGin _ hxN, N.coordinate_inverse_map (q, t) htN]
  let m := N.coordinate_map (q, -L / 2)
  let p := N.coordinate_map (q, L / 2)
  obtain ⟨hmU, hmG⟩ := hpoint (-L / 2)
    ⟨by linarith only [hL], by linarith only [hL]⟩
  obtain ⟨hpU, hpG⟩ := hpoint (L / 2)
    ⟨by linarith only [hL], by linarith only [hL]⟩
  have hmA : m ∈ A := by
    refine ⟨hmU, ?_⟩
    change G m < 0
    rw [hmG]
    linarith only [hL]
  have hmD : m ∈ D := hAD hmA
  have hpD : p ∈ D := by
    refine ⟨hUcomponent hpU, ?_⟩
    intro hpS
    have hz := (hzero p).mpr hpS
    rw [hpG] at hz
    linarith only [hL, hz]
  have hpnotA : p ∉ A := by
    intro hpA
    have hh : G p < 0 := hpA.2
    rw [hpG] at hh
    linarith only [hL, hh]
  change D.Nonempty ∧ ¬ IsConnected D
  refine ⟨⟨m, hmD⟩, ?_⟩
  intro hD
  exact hpnotA (hD.isPreconnected.subset_of_closure_inter_subset
    hAopen ⟨m, hmD, hmA⟩ hAclD hpD)

end PoincareConjecture.BalancedNeckChain
