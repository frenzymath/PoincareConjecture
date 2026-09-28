import PoincareConjecture.Proofs.M25.AppA_1_Necks.MiddleFrontier
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicFiniteChain
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false
open Set Topology
open scoped Manifold ContDiff
universe u
namespace PoincareConjecture.BalancedNeckChain

theorem N1b_initial_isSeparating_of_forward_chain :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) (a : ℤ),
      C.shape = ChainShape.forward a → epsilon ≤ epsilon0 →
      (closure ((C.neck a).region (epsilon⁻¹ / 2) epsilon⁻¹) ⊆
          (C.neck (a + 1)).carrier ∧
        closure ((C.neck (a + 1)).region
            (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ⊆ (C.neck a).carrier) →
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        ((C.neck (i + 1)).center ∈
              closure ((C.neck i).region 0 epsilon⁻¹) ∧
            (C.neck (i + 1)).center ∉ (C.neck i).carrier) ∨
          ((C.neck i).center ∈
              closure ((C.neck (i + 1)).region (-epsilon⁻¹) 0) ∧
            (C.neck i).center ∉ (C.neck (i + 1)).carrier)) →
      (C.neck a).IsSeparating := by
  obtain ⟨epsilonM, hMpos, hMcap, hfrontier⟩ :=
    exists_frontier_subset_exposed_end_closures.{u}
  refine ⟨epsilonM, hMpos, hMcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a hshape heps hquarters hincidence
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := epsilon⁻¹
  let N := C.neck a
  let N1 := C.neck (a + 1)
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let V : Set M := ⋃ i ∈ Ici (a + 1), (C.neck i).carrier
  let G : M → ℝ := fun x =>
    if x ∈ N.carrier then (N.coordinate_inverse x).2 else L
  have heM : epsilon ≤ epsilonM := heps
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ a ≤ i := by
    rw [hshape]
    rfl
  have ha : a ∈ C.shape.active := (hactive a).mpr le_rfl
  have ha1 : a + 1 ∈ C.shape.active := (hactive (a + 1)).mpr (by omega)
  have hNe : N.epsilon = epsilon := C.epsilon_eq a ha
  have hN1e : N1.epsilon = epsilon := C.epsilon_eq (a + 1) ha1
  have hepos : 0 < epsilon := hNe ▸ N.epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hcarrierU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hNU : N.carrier ⊆ U := hcarrierU a ha
  have hN1U : N1.carrier ⊆ U := hcarrierU (a + 1) ha1
  have hGin (x : M) (hx : x ∈ N.carrier) :
      G x = (N.coordinate_inverse x).2 := by
    simp only [G, if_pos hx]
  have hGout (x : M) (hx : x ∉ N.carrier) : G x = L := by
    simp only [G, if_neg hx]
  change closure (N.region (L / 2) L) ⊆ N1.carrier ∧
    closure (N1.region (-L) (-L / 2)) ⊆ N.carrier at hquarters

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
  have hfinite (j : ℤ) (haj : a ≤ j) :
      ContinuousOn G (⋃ i ∈ Icc a j, (C.neck i).carrier) := by
    let Cj := restrict (.finite a j) ⟨a, le_rfl, haj⟩
      (fun i hi => (hactive i).mpr hi.1)
    exact (Cj.continuousOn_initial_height_of_finite rfl).1
  have hUopen : IsOpen U :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  have hGc : ContinuousOn G U := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
    have haj : a ≤ j := (hactive j).mp hj
    have hUjopen : IsOpen (⋃ i ∈ Icc a j, (C.neck i).carrier) :=
      isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
    exact (hfinite j haj).continuousAt
      (hUjopen.mem_nhds (mem_iUnion₂.mpr ⟨j, ⟨haj, le_rfl⟩, hxj⟩))
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
  let Ctail := restrict (.forward (a + 1))
      ⟨a + 1, by change a + 1 ≤ a + 1; exact le_rfl⟩ (by
    intro i hi
    change a + 1 ≤ i at hi
    exact (hactive i).mpr (by omega))
  have hfrontV : frontier V ⊆ closure (N1.region (-L) 0) := by
    have hf := hfrontier Ctail heM (by
      intro i hi hn
      change a + 1 ≤ i at hi
      change a + 1 ≤ i + 1 at hn
      exact hincidence i ((hactive i).mpr (by omega))
        ((hactive (i + 1)).mpr (by omega)))
    change frontier (⋃ i ∈ Ici (a + 1), (C.neck i).carrier) ⊆
      closure ((C.neck (a + 1)).region (-L) 0) at hf
    exact hf
  have hVU : V ⊆ U := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    change a + 1 ≤ i at hi
    exact hcarrierU i ((hactive i).mpr (by omega)) hxi

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
  let Kp := N.coordinate_map '' (univ ×ˢ Icc (0 : ℝ) (L / 2))
  have hKp := hslab N hNe (c := 0) (d := L / 2)
    (by linarith only [hL]) (by linarith only [hL])
  have hposcover : N.region 0 L ⊆ Kp ∪ N.region (L / 2) L := by
    intro x hx
    by_cases hh : (N.coordinate_inverse x).2 ≤ L / 2
    · exact Or.inl ⟨N.coordinate_inverse x,
        ⟨mem_univ _, hx.2.1.le, hh⟩, N.coordinate_map_inverse hx.1⟩
    · exact Or.inr ⟨hx.1, lt_of_not_ge hh, hx.2.2⟩
  have hposclosure : closure (N.region 0 L) ⊆ U := by
    intro x hx
    have hh := closure_mono hposcover hx
    rw [closure_union, hKp.1.closure_eq] at hh
    exact hh.elim (fun h => hNU (hKp.2 h)) (fun h => hN1U (hquarters.1 h))
  let Km := N1.coordinate_map '' (univ ×ˢ Icc (-L / 2) (0 : ℝ))
  have hKm := hslab N1 hN1e (c := -L / 2) (d := 0)
    (by linarith only [hL]) (by linarith only [hL])
  have hnegcover : N1.region (-L) 0 ⊆ N1.region (-L) (-L / 2) ∪ Km := by
    intro x hx
    by_cases hh : (N1.coordinate_inverse x).2 < -L / 2
    · exact Or.inl ⟨hx.1, hx.2.1, hh⟩
    · exact Or.inr ⟨N1.coordinate_inverse x,
        ⟨mem_univ _, le_of_not_gt hh, hx.2.2.le⟩, N1.coordinate_map_inverse hx.1⟩
  have hnegclosure : closure (N1.region (-L) 0) ⊆ U := by
    intro x hx
    have hh := closure_mono hnegcover hx
    rw [closure_union, hKm.1.closure_eq] at hh
    exact hh.elim (fun h => hNU (hquarters.2 h)) (fun h => hN1U (hKm.2 h))
  have hVclosure : closure V ⊆ U := by
    intro x hx
    rw [closure_eq_self_union_frontier] at hx
    exact hx.elim (fun h => hVU h) (fun h => hnegclosure (hfrontV h))
  have hUconnected : IsConnected U := by
    apply IsConnected.biUnion_of_chain C.active_nonempty
    · rw [hshape]
      exact ordConnected_Ici
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
  let A : Set M := U ∩ G ⁻¹' Ioi 0
  have hAopen : IsOpen A := hGc.isOpen_inter_preimage hUopen isOpen_Ioi
  have hAD : A ⊆ D := by
    intro x hx
    refine ⟨hUcomponent hx.1, ?_⟩
    intro hxS
    exact (ne_of_gt hx.2) ((hzero x).mpr hxS)
  have hAside : A ⊆ N.region 0 L ∪ V := by
    intro x hx
    by_cases hxN : x ∈ N.carrier
    · left
      have hh : (N.coordinate_inverse x).2 ∈ Ioo (-L) L := by
        simpa only [hNe] using (N.coordinate_inverse_mem x hxN).2
      refine ⟨hxN, ?_, hh.2⟩
      rw [← hGin x hxN]
      exact hx.2
    · right
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx.1
      have hia : a ≤ i := (hactive i).mp hi
      have hine : i ≠ a := by
        intro h
        exact hxN (by simpa only [h] using hxi)
      exact mem_iUnion₂.mpr ⟨i, show i ∈ Ici (a + 1) from by
        change a + 1 ≤ i
        omega, hxi⟩
  have hAclosure : closure A ⊆ U := by
    intro x hx
    have hh := closure_mono hAside hx
    rw [closure_union] at hh
    exact hh.elim (fun h => hposclosure h) (fun h => hVclosure h)
  have hAclD : closure A ∩ D ⊆ A := by
    intro x hx
    have hxU := hAclosure hx.1
    have hge : 0 ≤ G x := by
      by_contra h
      have hneg : G x < 0 := lt_of_not_ge h
      obtain ⟨y, hypos, hyA⟩ := (mem_closure_iff.mp hx.1)
        (U ∩ G ⁻¹' Iio 0) (hGc.isOpen_inter_preimage hUopen isOpen_Iio) ⟨hxU, hneg⟩
      exact lt_asymm (show G y < 0 from hypos.2) (show 0 < G y from hyA.2)
    refine ⟨hxU, ?_⟩
    rcases lt_or_eq_of_le hge with hgt | heq
    · simpa only [mem_preimage, mem_Ioi] using hgt
    · exact False.elim (hx.2.2 ((hzero x).mp heq.symm))
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
  have hpA : p ∈ A := by
    refine ⟨hpU, ?_⟩
    simpa only [mem_preimage, mem_Ioi] using (show 0 < G p by
      rw [hpG]
      linarith only [hL])
  have hpD : p ∈ D := hAD hpA
  have hmD : m ∈ D := by
    refine ⟨hUcomponent hmU, ?_⟩
    intro hmS
    have hz := (hzero m).mpr hmS
    rw [hmG] at hz
    linarith only [hL, hz]
  have hmnotA : m ∉ A := by
    intro hmA
    have hh : 0 < G m := by
      simpa only [mem_preimage, mem_Ioi] using hmA.2
    rw [hmG] at hh
    linarith only [hL, hh]
  change D.Nonempty ∧ ¬ IsConnected D
  refine ⟨⟨p, hpD⟩, ?_⟩
  intro hD
  exact hmnotA (hD.isPreconnected.subset_of_closure_inter_subset
    hAopen ⟨p, hpD, hpA⟩ hAclD hmD)

end PoincareConjecture.BalancedNeckChain
