import PoincareConjecture.Proofs.M76.Wall.PLDomainSideCollars
import PoincareConjecture.Proofs.M76.Wall.SideCollarSigns
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.CollarGluing.OriginalDomainInjection

set_option autoImplicit false
open Set Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem frontier_eq_of_signed_rim_charts
    {X : Type*} [TopologicalSpace X] {S O : Set X}
    (hS : IsClosed S) (hO : IsClosed O) (hcover : S ∪ O = univ)
    (hlocal : ∀ x : ↥(S ∩ O),
      ∃ T : OpenPartialHomeomorph X (ℝ × ℝ), (x : X) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0) :
    frontier S = S ∩ O ∧ O = (interior S)ᶜ := by
  have hcomp : Oᶜ ⊆ S := by
    intro x hx
    exact ((Set.ext_iff.mp hcover x).mpr (mem_univ x)).resolve_right hx
  have hfront : frontier S = S ∩ O := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨hS.frontier_subset hx, ?_⟩
      by_contra hxO
      have hxint : x ∈ interior S :=
        interior_mono hcomp (hO.isOpen_compl.interior_eq.symm ▸ hxO)
      exact hx.2 hxint
    · intro x hx
      obtain ⟨T, hxT, hTS, hTO⟩ := hlocal ⟨x, hx⟩
      let ell := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
      have hell : ell.toAffineMap.linear ≠ 0 := by
        intro h
        have hv := ell.toAffineMap.linearMap_vsub (0, 1) 0
        rw [h] at hv
        norm_num [ell] at hv
      have hz : (T x).2 = 0 := le_antisymm ((hTO x hxT).mp hx.2)
        ((hTS x hxT).mp hx.1)
      exact ((T.isImage_frontier_of_affine_nonneg ell hell hTS).apply_mem_iff hxT).mp hz
  refine ⟨hfront, ?_⟩
  ext x
  constructor
  · intro hxO hxint
    have hxfront : x ∈ frontier S := hfront.symm.subset ⟨interior_subset hxint, hxO⟩
    exact hxfront.2 hxint
  · intro hx
    by_contra hxO
    exact hx (interior_mono hcomp (hO.isOpen_compl.interior_eq.symm ▸ hxO))

theorem exists_side_collars_of_signed_rim_charts
    {X : Type*} [MetricSpace X] {S O : Set X}
    (hS : IsClosed S) (hO : IsClosed O) (hcover : S ∪ O = univ)
    (hcompact : IsCompact (S ∩ O)) (hne : (S ∩ O).Nonempty)
    (hlocal : ∀ x : ↥(S ∩ O),
      ∃ T : OpenPartialHomeomorph X (ℝ × ℝ), (x : X) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0) :
    frontier S = S ∩ O ∧ O = (interior S)ᶜ ∧
      ∃ C : AmbientSideCollars (frontier S), C.positive = S ∧ C.negative = O := by
  obtain ⟨hfront, hother⟩ := frontier_eq_of_signed_rim_charts hS hO hcover hlocal
  have hFc : IsCompact (frontier S) := hfront.symm ▸ hcompact
  have hFne : (frontier S).Nonempty := hfront.symm ▸ hne
  let : CompactSpace (frontier S) := isCompact_iff_compactSpace.mp hFc
  let : Nonempty (frontier S) := hFne.to_subtype
  have hFS : frontier S ⊆ S := hS.frontier_subset
  have hFO : frontier S ⊆ O := hfront.subset.trans inter_subset_right
  have hcharts (x : frontier S) :
      ∃ T : OpenPartialHomeomorph X (ℝ × ℝ), (x : X) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ frontier S ↔ (T y).2 = 0) ∧
        (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0 := by
    obtain ⟨T, hxT, hTS, hTO⟩ := hlocal ⟨x, hfront.subset x.property⟩
    refine ⟨T, hxT, ?_, hTS, hTO⟩
    intro y hy
    rw [hfront, mem_inter_iff, hTS y hy, hTO y hy]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  have hpos (x : frontier S) :
      ∃ c : OpenPartialHomeomorph (frontier S × Ico (0 : ℝ) 1) S,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion hFS a := by
    obtain ⟨T, hxT, hpair, hTS, _⟩ := hcharts x
    exact exists_positive_halfspace_local_collar T hFS hpair hTS x hxT
  have hneg (x : frontier S) :
      ∃ c : OpenPartialHomeomorph (frontier S × Ico (0 : ℝ) 1) O,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion hFO a := by
    obtain ⟨T, hxT, hpair, _, hTO⟩ := hcharts x
    exact exists_negative_halfspace_local_collar T hFO hpair hTO x hxT
  obtain ⟨Up, hUp, _, cp, hcp⟩ := exists_full_collar_of_compact_local_patches
    (Set.inclusion hFS) (Set.inclusion_injective hFS) hpos
  obtain ⟨Um, hUm, _, cm, hcm⟩ := exists_full_collar_of_compact_local_patches
    (Set.inclusion hFO) (Set.inclusion_injective hFO) hneg
  let C : AmbientSideCollars (frontier S) :=
    { neighborhood := univ
      positive := S
      negative := O
      open_neighborhood := isOpen_univ
      base_subset := subset_univ _
      union_eq := hcover
      inter_eq := hfront.symm
      positive_closed := hS.preimage continuous_subtype_val
      negative_closed := hO.preimage continuous_subtype_val
      positive_range := Up
      negative_range := Um
      positive_open := hUp
      negative_open := hUm
      positive_collar := cp
      negative_collar := cm
      positive_base := fun s => congrArg (Subtype.val : S → X) (hcp s)
      negative_base := fun s => congrArg (Subtype.val : O → X) (hcm s) }
  exact ⟨hfront, hother, C, rfl, rfl⟩

theorem exists_bicollar_of_signed_rim_charts
    {X : Type*} [MetricSpace X] {S O : Set X}
    (hS : IsClosed S) (hO : IsClosed O) (hcover : S ∪ O = univ)
    (hcompact : IsCompact (S ∩ O)) (hne : (S ∩ O).Nonempty)
    (hlocal : ∀ x : ↥(S ∩ O),
      ∃ T : OpenPartialHomeomorph X (ℝ × ℝ), (x : X) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0) :
    frontier S = S ∩ O ∧ O = (interior S)ᶜ ∧
      ∃ U : Set X, IsOpen U ∧ frontier S ⊆ U ∧
        ∃ H : (frontier S × Ioo (-1 : ℝ) 1) ≃ₜ U,
          (∀ x, (H (bicollarBase x) : X) = (x : X)) ∧
          (∀ z, (H z : X) ∈ S ↔ 0 ≤ (z.2 : ℝ)) ∧
          (∀ z, (H z : X) ∈ O ↔ (z.2 : ℝ) ≤ 0) ∧
          ∀ z, (H z : X) ∈ frontier S ↔ (z.2 : ℝ) = 0 := by
  obtain ⟨hfront, hother, C, hpos, hneg⟩ :=
    exists_side_collars_of_signed_rim_charts hS hO hcover hcompact hne hlocal
  refine ⟨hfront, hother, C.collarUnion, C.isOpen_collarUnion,
    C.base_subset_positiveImage.trans subset_union_left,
    C.bicollarHomeomorph, C.bicollarHomeomorph_base, ?_, ?_, C.bicollar_mem_base_iff⟩
  · intro z
    simpa only [hpos] using C.bicollar_mem_positive_iff z
  · intro z
    simpa only [hneg] using C.bicollar_mem_negative_iff z

theorem nonempty_openFrontierCollapse_of_open_bicollar
    {X : Type*} [TopologicalSpace X] [T2Space X] {S U : Set X}
    (hS : IsClosed S) (hcompact : IsCompact (frontier S))
    (hne : (frontier S).Nonempty) (hU : IsOpen U)
    (H : (frontier S × Ioo (-1 : ℝ) 1) ≃ₜ U)
    (hbase : ∀ x, (H (bicollarBase x) : X) = (x : X))
    (hpos : ∀ z, (H z : X) ∈ S ↔ 0 ≤ (z.2 : ℝ))
    (hneg : ∀ z, (H z : X) ∈ (interior S)ᶜ ↔ (z.2 : ℝ) ≤ 0)
    (hzero : ∀ z, (H z : X) ∈ frontier S ↔ (z.2 : ℝ) = 0) :
    Nonempty (OpenFrontierCollapse S) := by
  classical
  let E := ↥(frontier S)
  let : CompactSpace E := isCompact_iff_compactSpace.mp hcompact
  let : Zero E := ⟨hne.to_subtype.some⟩
  let tau : ℝ → ℝ := fun t => min (1 / 2) (max (-(1 / 2)) (t / 2))
  have htau (t : ℝ) : tau t ∈ Ioo (-1 : ℝ) 1 := by
    have hm : -(1 / 2 : ℝ) ≤ tau t := le_min (by norm_num) (le_max_left _ _)
    have hp : tau t ≤ (1 / 2 : ℝ) := min_le_left _ _
    constructor <;> linarith
  have htauc : Continuous tau := continuous_const.min
    (continuous_const.max (continuous_id.div_const 2))
  have htaueq (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : tau t = t / 2 := by
    dsimp only [tau]
    rw [max_eq_right (by linarith [ht.1]), min_eq_right (by linarith [ht.2])]
  let c : E × ℝ → X := fun z => H (z.1, ⟨tau z.2, htau z.2⟩)
  have hc : Continuous c := continuous_subtype_val.comp (H.continuous.comp
    (continuous_fst.prodMk ((htauc.comp continuous_snd).subtype_mk _)))
  have hvalue (z : E × ℝ) (hz : z.2 ∈ Icc (-1 : ℝ) 1) :
      c z = (H (z.1, ⟨z.2 / 2, by constructor <;> linarith [hz.1, hz.2]⟩) : X) := by
    dsimp only [c]
    apply congrArg Subtype.val
    apply congrArg H
    exact Prod.ext rfl (Subtype.ext (htaueq z.2 hz))
  have hi : Topology.IsEmbedding
      (fun z : (univ ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z) := by
    let : CompactSpace (univ ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) :=
      isCompact_iff_compactSpace.mp (isCompact_univ.prod isCompact_Icc)
    refine ((hc.comp continuous_subtype_val).isClosedEmbedding ?_).isEmbedding
    intro z w heq
    change c z = c w at heq
    rw [hvalue z z.property.2, hvalue w w.property.2] at heq
    have heq' := H.injective (Subtype.ext heq)
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : E × Ioo (-1 : ℝ) 1 => z.1) heq'
    · have ht := congrArg (fun z : E × Ioo (-1 : ℝ) 1 => (z.2 : ℝ)) heq'
      dsimp at ht
      linarith
  have hopen (eps : ℝ) (heps : 0 < eps) (hepsOne : eps ≤ 1) :
      IsOpen (c '' (univ ×ˢ Ioo (-eps) eps)) := by
    let f : E × Ioo (-1 : ℝ) 1 → X := fun z => H z
    let V : Set (E × Ioo (-1 : ℝ) 1) :=
      {z | -(eps / 2) < (z.2 : ℝ) ∧ (z.2 : ℝ) < eps / 2}
    have hV : IsOpen V := (isOpen_lt continuous_const
      (continuous_subtype_val.comp continuous_snd)).inter
        (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
    have hf : Topology.IsOpenEmbedding f := hU.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding
    have himage : c '' (univ ×ˢ Ioo (-eps) eps) = f '' V := by
      apply Subset.antisymm
      · rintro y ⟨z, hz, rfl⟩
        have hzI : z.2 ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hz.2.1, hz.2.2]
        refine ⟨(z.1, ⟨z.2 / 2, by constructor <;> linarith [hzI.1, hzI.2]⟩),
          ⟨by dsimp; linarith [hz.2.1], by dsimp; linarith [hz.2.2]⟩, ?_⟩
        exact (hvalue z hzI).symm
      · rintro y ⟨z, hz, rfl⟩
        have hzI : 2 * (z.2 : ℝ) ∈ Icc (-1 : ℝ) 1 := by
          constructor <;> linarith [hz.1, hz.2]
        refine ⟨(z.1, 2 * (z.2 : ℝ)), ⟨mem_univ _, ?_, ?_⟩, ?_⟩
        · dsimp; linarith [hz.1]
        · dsimp; linarith [hz.2]
        · rw [hvalue _ hzI]
          change (H (z.1, _) : X) = H z
          congr 2
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            dsimp
            ring
    rw [himage]
    exact hf.isOpenMap V hV
  apply nonempty_openFrontierCollapse_of_bicollar hS
    (isCompact_univ : IsCompact (univ : Set E)) (Homeomorph.Set.univ E) c
    hc.continuousOn hi ?_ ?_ (show (0 : ℝ) < 1 by norm_num) le_rfl hopen
  · intro x
    rw [hvalue _ (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)]
    change (H ((x : E), ⟨(0 : ℝ) / 2, _⟩) : X) = ((x : E) : X)
    simpa only [bicollarBase, zero_div] using hbase x.val
  · intro z
    rw [hvalue z z.property.2]
    rw [hzero, hpos, hneg]
    dsimp
    constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> constructor <;> intro h <;> linarith

theorem nonempty_openFrontierCollapse_of_signed_rim_charts
    {X : Type*} [MetricSpace X] {S O : Set X}
    (hS : IsClosed S) (hO : IsClosed O) (hcover : S ∪ O = univ)
    (hcompact : IsCompact (S ∩ O)) (hne : (S ∩ O).Nonempty)
    (hlocal : ∀ x : ↥(S ∩ O),
      ∃ T : OpenPartialHomeomorph X (ℝ × ℝ), (x : X) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0) :
    frontier S = S ∩ O ∧ O = (interior S)ᶜ ∧ Nonempty (OpenFrontierCollapse S) := by
  obtain ⟨hfront, hother, U, hU, _, H, hbase, hpos, hneg, hzero⟩ :=
    exists_bicollar_of_signed_rim_charts hS hO hcover hcompact hne hlocal
  refine ⟨hfront, hother, nonempty_openFrontierCollapse_of_open_bicollar hS
    (hfront.symm ▸ hcompact) (hfront.symm ▸ hne) hU H hbase hpos ?_ hzero⟩
  simpa only [hother] using hneg

theorem sides_pi1_injective_of_signed_rim_charts
    {X : Type*} [MetricSpace X] {S O : Set X}
    (hS : IsClosed S) (hO : IsClosed O) (hcover : S ∪ O = univ)
    (hcompact : IsCompact (S ∩ O)) (hne : (S ∩ O).Nonempty)
    (hlocal : ∀ x : ↥(S ∩ O),
      ∃ T : OpenPartialHomeomorph X (ℝ × ℝ), (x : X) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0)
    (hpi : ∀ x : ↥(S ∩ O), Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (S ∩ O)) x)) :
    ∀ T ∈ ({S, O} : Set (Set X)), ∀ x : T,
      Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x) := by
  obtain ⟨hfront, hother, ⟨C⟩⟩ :=
    nonempty_openFrontierCollapse_of_signed_rim_charts hS hO hcover hcompact hne hlocal
  have hFpi : ∀ x : frontier S, Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier S)) x) := by
    rw [hfront]
    exact hpi
  have hsides : ∀ T ∈ ({S, (interior S)ᶜ} : Set (Set X)),
      ∃ hFT : frontier S ⊆ T, ∀ x : frontier S,
        Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hFT) x) := by
    intro T hT
    have hFT : frontier S ⊆ T := by
      rcases hT with rfl | rfl
      · exact hS.frontier_subset
      · exact fun _ hx => hx.2
    refine ⟨hFT, ?_⟩
    intro x a b hab
    apply hFpi x
    have h := congrArg (FundamentalGroup.map (VanKampen.inclusion T)
      (ContinuousMap.inclusion hFT x)) hab
    rw [← FundamentalGroup.map_comp_apply, ← FundamentalGroup.map_comp_apply] at h
    exact h
  simpa only [hother] using C.side_ambient_injective hS hsides

end PoincareConjecture.M76.HamiltonIntervalTorus
