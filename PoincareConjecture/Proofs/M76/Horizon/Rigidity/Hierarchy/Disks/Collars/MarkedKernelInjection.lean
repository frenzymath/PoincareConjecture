import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.SignedCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.MarkedRimCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.CollarKernelInjectivity









set_option autoImplicit false
open Set Geometry BrownCollar

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_marked_phase_rim_collar
    {X ι : Type*} [MetricSpace X] (e : ι → OpenPartialHomeomorph X V3)
    {N R S U : Set X} (hN : IsCompact N) (he : PLDomain e N)
    (hS : IsClosed S) (hU : IsClosed U)
    (hfront : frontier N = (N ∩ frontier R) ∪ (S ∪ U))
    (hdis : Disjoint S U) (hne : (S ∩ frontier R).Nonempty)
    (hcorner : ∀ x ∈ S ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧
        (∀ y ∈ G.source, y ∈ N ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ N ∩ frontier R ↔ psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ S ↔ psi (G y) = 0 ∧ lambda (G y) ≤ 0) :
    ∃ V : Set S, IsOpen V ∧
      ∃ c : (↥(S ∩ frontier R) × Ico (0 : ℝ) 1) ≃ₜ V,
        ∀ x, (c (collarBase x) : S) = Set.inclusion inter_subset_left x := by
  have hSF : S ⊆ frontier N := fun _ hx => hfront.symm.subset (Or.inr (Or.inl hx))
  have hSN : S ⊆ N := hSF.trans he.closed.frontier_subset
  let P : Set (frontier N) := Subtype.val ⁻¹' S
  let O : Set (frontier N) := Subtype.val ⁻¹' ((N ∩ frontier R) ∪ U)
  have hPc : IsClosed P := hS.preimage continuous_subtype_val
  have hOc : IsClosed O :=
    ((he.closed.inter isClosed_frontier).union hU).preimage continuous_subtype_val
  have hcover : P ∪ O = univ := by
    apply eq_univ_of_forall
    intro x
    have hx := hfront.subset x.property
    change (x : X) ∈ S ∨ (x : X) ∈ (N ∩ frontier R) ∪ U
    rcases hx with hx | hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  have hrim (x : frontier N) : x ∈ P ∩ O ↔ (x : X) ∈ S ∩ frontier R := by
    change ((x : X) ∈ S ∧ ((x : X) ∈ N ∩ frontier R ∨ (x : X) ∈ U)) ↔ _
    constructor
    · rintro ⟨hx, hold | hother⟩
      · exact ⟨hx, hold.2⟩
      · exact (disjoint_left.mp hdis hx hother).elim
    · intro hx
      exact ⟨hx.1, Or.inl ⟨hSN hx.1, hx.2⟩⟩
  have hcompact : IsCompact (P ∩ O) := by
    rw [show P ∩ O = (Subtype.val : frontier N → X) ⁻¹' (S ∩ frontier R) from Set.ext hrim]
    apply Topology.IsInducing.subtypeVal.isCompact_preimage'
      ((hN.of_isClosed_subset hS hSN).inter_right isClosed_frontier)
    simpa only [Subtype.range_coe] using inter_subset_left.trans hSF
  have hne' : (P ∩ O).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hSF hx.1⟩, (hrim _).mpr hx⟩
  have hlocal (x : ↥(P ∩ O)) :
      ∃ T : OpenPartialHomeomorph (frontier N) (ℝ × ℝ), (x : frontier N) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ P ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0 := by
    have hxrim := (hrim x.val).mp x.property
    obtain ⟨psi, lambda, w, z, G, hpw, hpz, hlz, hxG, hGN, hGO, hGS⟩ :=
      hcorner x.val.val hxrim
    let G' := G.restr Uᶜ
    have hG's : G'.source = G.source ∩ Uᶜ := G.restr_source' Uᶜ hU.isOpen_compl
    have hxG' : x.val.val ∈ G'.source := by
      rw [hG's]
      exact ⟨hxG, fun h => disjoint_left.mp hdis hxrim.1 h⟩
    have hN' (y : X) (hy : y ∈ G'.source) : y ∈ N ↔ 0 ≤ psi (G' y) :=
      hGN y (hG's.subset hy).1
    have hS' (y : X) (hy : y ∈ G'.source) :
        y ∈ S ↔ psi (G' y) = 0 ∧ lambda (G' y) ≤ 0 := hGS y (hG's.subset hy).1
    have hO' (y : X) (hy : y ∈ G'.source) :
        y ∈ (N ∩ frontier R) ∪ U ↔ psi (G' y) = 0 ∧ 0 ≤ lambda (G' y) := by
      rw [mem_union, or_iff_left (hG's.subset hy).2]
      exact hGO y (hG's.subset hy).1
    obtain ⟨T, hxT, hTS, hTO, _⟩ := HamiltonIntervalTorus.exists_intrinsic_signed_rim_chart
      G' psi lambda w z hpw hpz hlz hN' hS' hO' x.val hxG'
    exact ⟨T, hxT, hTS, hTO⟩
  obtain ⟨hboundary, _, A, hpos, _⟩ :=
    HamiltonIntervalTorus.exists_side_collars_of_signed_rim_charts
      hPc hOc hcover hcompact hne' hlocal
  let rimEquiv : ↥(S ∩ frontier R) ≃ₜ ↥(P ∩ O) :=
    { toFun := fun x => ⟨⟨x.val, hSF x.property.1⟩, (hrim _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val, (hrim x.val).mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let rim := rimEquiv.trans (Homeomorph.setCongr hboundary.symm)
  let phase : P ≃ₜ S :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, hSF x.property⟩, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let positive : A.positive ≃ₜ S := (Homeomorph.setCongr hpos).trans phase
  let V : Set S := positive '' A.positive_range
  let c : (↥(S ∩ frontier R) × Ico (0 : ℝ) 1) ≃ₜ V :=
    ((rim.prodCongr (Homeomorph.refl _)).trans A.positive_collar).trans
      (positive.image A.positive_range)
  refine ⟨V, positive.isOpenMap _ A.positive_open, c, ?_⟩
  intro x
  apply Subtype.ext
  change (((A.positive_collar (collarBase (rim x)) : A.positive) : frontier N) : X) = (x : X)
  exact congrArg (fun y : frontier N => (y : X)) (A.positive_base (rim x))

private theorem pi1_injective_of_full_rim_collar
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {B V : Set X} (hB : IsCompact B) (hne : B.Nonempty) (hV : IsOpen V)
    (H : (B × Ico (0 : ℝ) 1) ≃ₜ V)
    (hbase : ∀ x : B, (H (collarBase x) : X) = (x : X))
    (f : C(X, Y))
    (hkernel : ∀ (x : ↥Bᶜ) (gamma : FundamentalGroup ↥Bᶜ x),
      FundamentalGroup.map (f.comp ⟨Subtype.val, continuous_subtype_val⟩) x gamma = 1 →
        FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Bᶜ, X)) x gamma = 1) :
    ∀ x : X, Function.Injective (FundamentalGroup.map f x) := by
  classical
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : Zero B := ⟨hne.to_subtype.some⟩
  let tau : ℝ → ℝ := fun t => min (1 / 2) (max 0 t)
  have htau (t : ℝ) : tau t ∈ Ico (0 : ℝ) 1 :=
    ⟨le_min (by norm_num) (le_max_left _ _), (min_le_left _ _).trans_lt (by norm_num)⟩
  have htauc : Continuous tau := continuous_const.min (continuous_const.max continuous_id)
  have htaueq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1 / 2)) : tau t = t := by
    dsimp only [tau]
    rw [max_eq_right ht.1, min_eq_right ht.2]
  let c : B × ℝ → X := fun z => H (z.1, ⟨tau z.2, htau z.2⟩)
  have hc : Continuous c := continuous_subtype_val.comp (H.continuous.comp
    (continuous_fst.prodMk ((htauc.comp continuous_snd).subtype_mk _)))
  have hi : Topology.IsEmbedding
      (fun z : (univ ×ˢ Icc (0 : ℝ) (1 / 2) : Set (B × ℝ)) => c z) := by
    let : CompactSpace (univ ×ˢ Icc (0 : ℝ) (1 / 2) : Set (B × ℝ)) :=
      isCompact_iff_compactSpace.mp (isCompact_univ.prod isCompact_Icc)
    refine ((hc.comp continuous_subtype_val).isClosedEmbedding ?_).isEmbedding
    intro z w hzw
    have hh := H.injective (Subtype.ext hzw)
    have hfirst := congrArg (fun q : B × Ico (0 : ℝ) 1 => q.1) hh
    have hsecond := congrArg (fun q : B × Ico (0 : ℝ) 1 => (q.2 : ℝ)) hh
    change tau z.val.2 = tau w.val.2 at hsecond
    rw [htaueq _ z.property.2, htaueq _ w.property.2] at hsecond
    exact Subtype.ext (Prod.ext hfirst hsecond)
  let fH : B × Ico (0 : ℝ) 1 → X := fun z => H z
  let W : Set (B × Ico (0 : ℝ) 1) := {z | (z.2 : ℝ) < 1 / 2}
  have hW : IsOpen W := isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  have hfH : Topology.IsOpenEmbedding fH := hV.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding
  have hopen : IsOpen (c '' (univ ×ˢ Ico (0 : ℝ) (1 / 2))) := by
    have himage : c '' (univ ×ˢ Ico (0 : ℝ) (1 / 2)) = fH '' W := by
      apply Subset.antisymm
      · rintro y ⟨z, hz, rfl⟩
        refine ⟨(z.1, ⟨tau z.2, htau z.2⟩), ?_, rfl⟩
        change tau z.2 < 1 / 2
        rw [htaueq _ ⟨hz.2.1, hz.2.2.le⟩]
        exact hz.2.2
      · rintro y ⟨z, hz, rfl⟩
        refine ⟨(z.1, z.2), ⟨mem_univ _, z.2.property.1, hz⟩, ?_⟩
        change (H (z.1, ⟨tau z.2, _⟩) : X) = H z
        apply congrArg Subtype.val
        apply congrArg H
        exact Prod.ext rfl (Subtype.ext (htaueq _ ⟨z.2.property.1, hz.le⟩))
    rw [himage]
    exact hfH.isOpenMap _ hW
  have hzero : c '' (univ ×ˢ ({0} : Set ℝ)) = B := by
    have hczero (z : B) : c (z, 0) = (z : X) := by
      have ht0 : tau 0 = 0 := htaueq _ ⟨le_rfl, by norm_num⟩
      simpa only [c, ht0, collarBase] using hbase z
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      rw [ht0, hczero]
      exact z.property
    · intro hx
      exact ⟨(⟨x, hx⟩, 0), ⟨mem_univ _, rfl⟩, hczero ⟨x, hx⟩⟩
  have h := Poincare.Topology.fundamentalGroup_map_injective_of_collar_kernel_control
    (isCompact_univ : IsCompact (univ : Set B)) (by norm_num : (0 : ℝ) < 1 / 2)
    c hc.continuousOn hi hopen f
  rw [hzero] at h
  exact h hkernel

theorem marked_phase_pi1_injective_of_kernel_control
    {X ι : Type*} [MetricSpace X] (e : ι → OpenPartialHomeomorph X V3)
    {N R S U : Set X} (hN : IsCompact N) (he : PLDomain e N)
    (hS : IsClosed S) (hU : IsClosed U)
    (hfront : frontier N = (N ∩ frontier R) ∪ (S ∪ U))
    (hdis : Disjoint S U)
    (hcorner : ∀ x ∈ S ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧
        (∀ y ∈ G.source, y ∈ N ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ N ∩ frontier R ↔ psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ S ↔ psi (G y) = 0 ∧ lambda (G y) ≤ 0)
    (hMN : S \ frontier R ⊆ N)
    (hkernel : ∀ (x : ↥(S \ frontier R)) (gamma : FundamentalGroup ↥(S \ frontier R) x),
      FundamentalGroup.map (ContinuousMap.inclusion hMN) x gamma = 1 →
        FundamentalGroup.map (ContinuousMap.inclusion (sdiff_subset : S \ frontier R ⊆ S))
          x gamma = 1) :
    ∃ hSN : S ⊆ N, ∀ x : S,
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x) := by
  classical
  have hSF : S ⊆ frontier N := fun _ hx => hfront.symm.subset (Or.inr (Or.inl hx))
  have hSN : S ⊆ N := hSF.trans he.closed.frontier_subset
  let f : C(S, N) := ContinuousMap.inclusion hSN
  let M := S \ frontier R
  refine ⟨hSN, ?_⟩
  by_cases hne : (S ∩ frontier R).Nonempty
  · let B : Set S := Subtype.val ⁻¹' frontier R
    let : CompactSpace S := isCompact_iff_compactSpace.mp (hN.of_isClosed_subset hS hSN)
    have hB : IsCompact B := (isClosed_frontier.preimage continuous_subtype_val).isCompact
    have hBne : B.Nonempty := by
      obtain ⟨x, hx, hxF⟩ := hne
      exact ⟨⟨x, hx⟩, hxF⟩
    obtain ⟨V, hV, H, hbase⟩ := exists_marked_phase_rim_collar
      e hN he hS hU hfront hdis hne hcorner
    let rim : B ≃ₜ ↥(S ∩ frontier R) :=
      { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
        invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let c := (rim.prodCongr (Homeomorph.refl (Ico (0 : ℝ) 1))).trans H
    have hcbase (x : B) : (c (collarBase x) : S) = (x : S) := by
      exact hbase (rim x)
    let incl : C(↥Bᶜ, S) := ⟨Subtype.val, continuous_subtype_val⟩
    let m : C(↥Bᶜ, M) :=
      ⟨fun z => ⟨z.val.val, z.val.property, z.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    apply pi1_injective_of_full_rim_collar hB hBne hV c hcbase f
    intro x gamma hg
    have hNmap : FundamentalGroup.map (ContinuousMap.inclusion hMN)
        (m x) (FundamentalGroup.map m x gamma) = 1 := by
      rw [← MonoidHom.comp_apply, ← FundamentalGroup.map_comp]
      exact hg
    have hSmap := hkernel (m x) (FundamentalGroup.map m x gamma) hNmap
    rw [← MonoidHom.comp_apply, ← FundamentalGroup.map_comp] at hSmap
    exact hSmap
  · have hoff (x : S) : (x : X) ∉ frontier R := fun hx => hne ⟨x, x.property, hx⟩
    let j : C(S, M) := ⟨fun x => ⟨x, x.property, hoff x⟩, continuous_subtype_val.subtype_mk _⟩
    intro x
    apply (injective_iff_map_eq_one (FundamentalGroup.map f x)).mpr
    intro gamma hg
    have hNmap : FundamentalGroup.map (ContinuousMap.inclusion hMN)
        (j x) (FundamentalGroup.map j x gamma) = 1 := by
      rw [← MonoidHom.comp_apply, ← FundamentalGroup.map_comp]
      exact hg
    have hSmap := hkernel (j x) (FundamentalGroup.map j x gamma) hNmap
    rw [← MonoidHom.comp_apply, ← FundamentalGroup.map_comp] at hSmap
    change FundamentalGroup.map (ContinuousMap.id S) x gamma = 1 at hSmap
    rw [FundamentalGroup.map_id] at hSmap
    exact hSmap

end PoincareConjecture.M76
