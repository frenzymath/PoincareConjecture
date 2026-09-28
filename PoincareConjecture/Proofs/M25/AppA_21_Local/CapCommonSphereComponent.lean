import PoincareConjecture.Proofs.M25.AppA_21_Local.CapGraphCompactSide
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapTubeEnds
import PoincareConjecture.Proofs.M25.AppA_21_Local.Opposite

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.compact_union_component_of_common_outward_graph
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C0 C1 : CapCertificate g) (V : TopologicalSpace.Opens M)
    (d : V ≃ₜ (⟨C0.carrier, C0.carrier_open⟩ : TopologicalSpace.Opens M))
    (R : EpsilonNeck g)
    (hR : R = C1.boundary_neck ∨ R = C1.boundary_neck.reverse)
    (hcore : R.carrier ∩ C1.core = R.region (-C1.epsilon⁻¹) 0)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hfdom : ∀ q, f q ∈ Ico (0 : ℝ) C1.epsilon⁻¹)
    (N : EpsilonNeck g) (s : ℝ)
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hlevel :
      range (fun q : UnitTwoSphere => R.coordinate_map (q, f q)) =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, s)))
    (hSV : range (fun q : UnitTwoSphere =>
      R.coordinate_map (q, f q)) ⊆ (V : Set M))
    (y : M) (hycore : y ∈ C1.core)
    (hyclosure : y ∈ closure (V : Set M)) (hyout : y ∉ (V : Set M)) :
    let L := C1.epsilon⁻¹
    let q := (R.coordinate_inverse R.center).1
    let S := range (fun v : UnitTwoSphere => R.coordinate_map (v, f v))
    let a := R.coordinate_map (q, -L / 2)
    let b := R.coordinate_map (q, (f q + L) / 2)
    let A := connectedComponentIn Sᶜ a
    let B := connectedComponentIn Sᶜ b
    let W := (V : Set M) ∪ C1.carrier
    A ≠ B ∧ frontier A = S ∧ frontier B = S ∧
      IsCompact (closure A) ∧ closure A ⊆ C1.carrier ∧
      C1.closed_core ⊆ closure A ∧ IsCompact (closure B) ∧
      closure B ⊆ (V : Set M) ∧ y ∈ A ∧ y ∉ closure B ∧
      W = closure A ∪ closure B ∧ IsCompact W ∧ IsClopen W ∧
      IsConnected W ∧ W = connectedComponent a := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L := C1.epsilon⁻¹
  let q := (R.coordinate_inverse R.center).1
  let S := range (fun v : UnitTwoSphere => R.coordinate_map (v, f v))
  let a := R.coordinate_map (q, -L / 2)
  let b := R.coordinate_map (q, (f q + L) / 2)
  let A := connectedComponentIn Sᶜ a
  let B := connectedComponentIn Sᶜ b
  let W := (V : Set M) ∪ C1.carrier
  let V0 : TopologicalSpace.Opens M := ⟨C0.carrier, C0.carrier_open⟩
  let Kambient := A ∪ S ∪ B
  change A ≠ B ∧ frontier A = S ∧ frontier B = S ∧
    IsCompact (closure A) ∧ closure A ⊆ C1.carrier ∧
    C1.closed_core ⊆ closure A ∧ IsCompact (closure B) ∧
    closure B ⊆ (V : Set M) ∧ y ∈ A ∧ y ∉ closure B ∧
    W = closure A ∪ closure B ∧ IsCompact W ∧ IsClopen W ∧
    IsConnected W ∧ W = connectedComponent a
  obtain ⟨hUA, _, hAcompact, hAcap, hcorecl, haS, hbS, hne, hAfront, hBfront⟩ :=
    C1.outward_graph_compact_side R hR hcore f hf hfdom
  change C1.core ∪ R.coordinate_map ''
    {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < f z.1} = A at hUA
  change IsCompact (closure A) at hAcompact
  change closure A ⊆ C1.carrier at hAcap
  change C1.closed_core ⊆ closure A at hcorecl
  change a ∉ S at haS
  change b ∉ S at hbS
  change A ≠ B at hne
  change frontier A = S at hAfront
  change frontier B = S at hBfront
  have hcoreA : C1.core ⊆ A := by
    intro x hx
    rw [← hUA]
    exact Or.inl hx
  have hyA : y ∈ A := hcoreA hycore
  have hSclosed : IsClosed S := by
    rw [← hAfront]
    exact isClosed_frontier
  have hAopen : IsOpen A := hSclosed.isOpen_compl.connectedComponentIn
  have hBopen : IsOpen B := hSclosed.isOpen_compl.connectedComponentIn
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hxA hxB
    exact hne ((connectedComponentIn_eq hxA).trans (connectedComponentIn_eq hxB).symm)
  have hSclA : S ⊆ closure A := by
    intro x hx
    exact (show x ∈ frontier A from hAfront.symm ▸ hx).1
  have hScompact : IsCompact S :=
    hAcompact.of_isClosed_subset hSclosed hSclA
  have hSne : S.Nonempty := ⟨R.coordinate_map (q, f q), ⟨q, rfl⟩⟩
  obtain ⟨p, hpS⟩ := hSne
  have hopp := N.opposite_level_components hs
  dsimp only at hopp
  rw [← hlevel] at hopp
  obtain ⟨_, _, hKclopen, hKconnected, hKeq⟩ :=
    hopp a b haS hbS hne
      (fun x hx => ⟨hAfront.symm ▸ hx, hBfront.symm ▸ hx⟩)
  change IsClopen Kambient at hKclopen
  change IsConnected Kambient at hKconnected
  change Kambient = connectedComponent a at hKeq
  have haA : a ∈ A := mem_connectedComponentIn haS
  have hC1K : C1.carrier ⊆ Kambient := by
    apply C1.m25_isConnected_carrier.isPreconnected.subset_of_closure_inter_subset
      hKclopen.isOpen
    · exact ⟨a, hAcap (subset_closure haA), Or.inl (Or.inl haA)⟩
    · intro x hx
      exact hKclopen.isClosed.closure_eq ▸ hx.1
  have hVconnected : IsConnected (V : Set M) := by
    apply isConnected_iff_connectedSpace.mpr
    exact d.connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp C0.m25_isConnected_carrier)
  have hVK : (V : Set M) ⊆ Kambient := by
    apply hVconnected.isPreconnected.subset_of_closure_inter_subset hKclopen.isOpen
    · exact ⟨p, hSV hpS, Or.inl (Or.inr hpS)⟩
    · intro x hx
      exact hKclopen.isClosed.closure_eq ▸ hx.1
  have hWK : W ⊆ Kambient := by
    rintro x (hx | hx)
    · exact hVK hx
    · exact hC1K hx

  let SV : Set V := (Subtype.val : V → M) ⁻¹' S
  let Q0 : Set M := (fun v : V => (d v).val) '' SV
  have hSrange : S ⊆ range (Subtype.val : V → M) := by
    intro x hx
    exact ⟨⟨x, hSV hx⟩, rfl⟩
  have hSVcompact : IsCompact SV :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hScompact hSrange
  have hQ0compact : IsCompact Q0 :=
    hSVcompact.image (continuous_subtype_val.comp d.continuous)
  have hQ0cap : Q0 ⊆ C0.carrier := by
    rintro x ⟨v, _, rfl⟩
    exact (d v).property
  let L0 := C0.epsilon⁻¹
  let N0 := C0.end_neck
  have hL0 : 0 < L0 := inv_pos.mpr C0.epsilon_pos
  have hN0 : N0.epsilon = C0.epsilon := C0.end_neck_epsilon
  obtain ⟨t, ht, hQt⟩ :=
    C0.exists_later_lower_cut_containing_compact hQ0compact hQ0cap
      (d := (0 : ℝ)) ⟨neg_lt_zero.mpr hL0, hL0⟩
  let Kt := C0.carrier \ N0.region t L0
  change t ∈ Ioo (0 : ℝ) L0 at ht
  change Q0 ⊆ interior Kt at hQt
  have hret : t ∈ Ioo (-L0) L0 :=
    ⟨(neg_lt_zero.mpr hL0).trans ht.1, ht.2⟩
  have hKtcompact : IsCompact Kt := C0.isCompact_end_neck_lower_cut hret
  let Ksub : Set V0 := (Subtype.val : V0 → M) ⁻¹' Kt
  let G : V0 → M := fun w => (d.symm w).val
  let P := G '' Ksub
  let T := (V : Set M) \ P
  have hKtrange : Kt ⊆ range (Subtype.val : V0 → M) := by
    intro x hx
    exact ⟨⟨x, hx.1⟩, rfl⟩
  have hKsubcompact : IsCompact Ksub :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hKtcompact hKtrange
  have hG : Continuous G := continuous_subtype_val.comp d.symm.continuous
  have hPcompact : IsCompact P := hKsubcompact.image hG
  have hPV : P ⊆ (V : Set M) := by
    rintro x ⟨w, _, rfl⟩
    exact (d.symm w).property
  have hPclosed : IsClosed P := hPcompact.isClosed
  have hSP : S ⊆ P := by
    intro x hx
    let v : V := ⟨x, hSV hx⟩
    have hv : v ∈ SV := hx
    have hq : (d v).val ∈ Q0 := ⟨v, hv, rfl⟩
    refine ⟨d v, (show (d v).val ∈ Kt from interior_subset (hQt hq)), ?_⟩
    change (d.symm (d v)).val = x
    rw [d.symm_apply_apply]
  have hGmem (w : V0) : G w ∈ P ↔ w.val ∈ Kt := by
    constructor
    · rintro ⟨w', hw', heq⟩
      change (d.symm w').val = (d.symm w).val at heq
      have hv : d.symm w' = d.symm w := Subtype.ext heq
      have hw : w' = w := d.symm.injective hv
      exact hw ▸ hw'
    · intro hw
      exact ⟨w, hw, rfl⟩

  let Z := UnitTwoSphere × Ioo t L0
  let : ConnectedSpace (Ioo t L0) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo ht.2)
  have htailDom (z : Z) :
      (z.1, (z.2 : ℝ)) ∈ N0.cylinderDomain := by
    rw [EpsilonNeck.cylinderDomain, hN0]
    exact ⟨mem_univ _,
      (neg_lt_zero.mpr hL0).trans (ht.1.trans z.2.property.1), z.2.property.2⟩
  let c : Z → V0 := fun z =>
    ⟨N0.coordinate_map (z.1, (z.2 : ℝ)),
      C0.end_neck_subset (N0.coordinate_map_mem (htailDom z))⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    exact N0.coordinate_map_smooth.continuousOn.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) htailDom
  have hcTail (z : Z) : (c z).val ∈ N0.region t L0 := by
    refine ⟨N0.coordinate_map_mem (htailDom z), ?_⟩
    change t < (N0.coordinate_inverse
      (N0.coordinate_map (z.1, (z.2 : ℝ)))).2 ∧
      (N0.coordinate_inverse (N0.coordinate_map (z.1, (z.2 : ℝ)))).2 < L0
    rw [N0.coordinate_inverse_coordinate_map (htailDom z)]
    exact z.2.property
  let F : Z → M := fun z => G (c z)
  have hF : Continuous F := hG.comp hc
  have hTimage : range F = T := by
    apply Subset.antisymm
    · rintro x ⟨z, rfl⟩
      refine ⟨(d.symm (c z)).property, ?_⟩
      intro hzP
      have hzK : (c z).val ∈ Kt := (hGmem (c z)).mp hzP
      exact hzK.2 (hcTail z)
    · intro x hx
      let v : V := ⟨x, hx.1⟩
      let w : V0 := d v
      have hwimage : G w = x := by
        change (d.symm (d v)).val = x
        rw [d.symm_apply_apply]
      have hnotK : w.val ∉ Kt := by
        intro hwK
        have hxP := (hGmem w).mpr hwK
        rw [hwimage] at hxP
        exact hx.2 hxP
      have hwTail : w.val ∈ N0.region t L0 := by
        by_contra hn
        exact hnotK ⟨w.property, hn⟩
      let z : Z := ((N0.coordinate_inverse w.val).1,
        ⟨(N0.coordinate_inverse w.val).2, hwTail.2⟩)
      have hwc : c z = w := by
        apply Subtype.ext
        change N0.coordinate_map (N0.coordinate_inverse w.val) = w.val
        exact N0.coordinate_map_coordinate_inverse hwTail.1
      refine ⟨z, ?_⟩
      change G (c z) = x
      rw [hwc]
      exact hwimage
  have hTconnected : IsConnected T := by
    rw [← hTimage]
    simpa only [image_univ] using
      (isConnected_univ : IsConnected (univ : Set Z)).image F hF.continuousOn
  have hTavoid : T ⊆ Sᶜ := by
    intro x hx hxS
    exact hx.2 (hSP hxS)
  have hyP : y ∉ P := fun h => hyout (hPV h)
  obtain ⟨r, hrOpen, hrV⟩ := mem_closure_iff.mp hyclosure
    (A ∩ Pᶜ) (hAopen.inter hPclosed.isOpen_compl) ⟨hyA, hyP⟩
  have hrT : r ∈ T := ⟨hrV, hrOpen.2⟩
  have hTA : T ⊆ A := by
    change T ⊆ connectedComponentIn Sᶜ a
    rw [connectedComponentIn_eq hrOpen.1]
    exact hTconnected.isPreconnected.subset_connectedComponentIn hrT hTavoid
  have hBVP : B ∩ (V : Set M) ⊆ P := by
    rintro x ⟨hxB, hxV⟩
    by_contra hxP
    exact disjoint_left.mp hAB (hTA ⟨hxV, hxP⟩) hxB
  have hBVmeet : (B ∩ (V : Set M)).Nonempty := by
    have hpclB : p ∈ closure B :=
      (show p ∈ frontier B from hBfront.symm ▸ hpS).1
    obtain ⟨r, hrV, hrB⟩ :=
      mem_closure_iff.mp hpclB (V : Set M) V.isOpen (hSV hpS)
    exact ⟨r, hrB, hrV⟩
  have hVclosure : closure (V : Set M) ∩ B ⊆ (V : Set M) := by
    intro x hx
    have hcl : x ∈ closure ((V : Set M) ∩ B) := hBopen.closure_inter hx
    have hsub : (V : Set M) ∩ B ⊆ P := fun _ h => hBVP ⟨h.2, h.1⟩
    have hxP : x ∈ P := hPclosed.closure_eq ▸ closure_mono hsub hcl
    exact hPV hxP
  have hBV : B ⊆ (V : Set M) :=
    (isPreconnected_connectedComponentIn : IsPreconnected B).subset_of_closure_inter_subset
      V.isOpen hBVmeet hVclosure
  have hBP : B ⊆ P := fun _ hx => hBVP ⟨hx, hBV hx⟩
  have hclBP : closure B ⊆ P := closure_minimal hBP hPclosed
  have hBcompact : IsCompact (closure B) :=
    hPcompact.of_isClosed_subset isClosed_closure hclBP
  have hclBV : closure B ⊆ (V : Set M) := hclBP.trans hPV
  have hyNotclB : y ∉ closure B := fun h => hyout (hclBV h)
  have hAcl : closure A = A ∪ S := by
    rw [closure_eq_self_union_frontier, hAfront]
  have hBcl : closure B = B ∪ S := by
    rw [closure_eq_self_union_frontier, hBfront]
  have hclosures : closure A ∪ closure B = Kambient := by
    rw [hAcl, hBcl]
    change (A ∪ S) ∪ (B ∪ S) = (A ∪ S) ∪ B
    ext x
    simp only [mem_union]
    tauto
  have hclosuresW : closure A ∪ closure B ⊆ W := by
    rintro x (hx | hx)
    · exact Or.inr (hAcap hx)
    · exact Or.inl (hclBV hx)
  have hKW : Kambient ⊆ W := by
    rw [← hclosures]
    exact hclosuresW
  have hWeq : W = Kambient := Subset.antisymm hWK hKW
  have hWclosures : W = closure A ∪ closure B := hWeq.trans hclosures.symm
  have hWcompact : IsCompact W := by
    rw [hWclosures]
    exact hAcompact.union hBcompact
  refine ⟨hne, hAfront, hBfront, hAcompact, hAcap, hcorecl, hBcompact, hclBV,
    hyA, hyNotclB, hWclosures, hWcompact, ?_, ?_, ?_⟩
  · rw [hWeq]
    exact hKclopen
  · rw [hWeq]
    exact hKconnected
  · exact hWeq.trans hKeq

end PoincareConjecture
