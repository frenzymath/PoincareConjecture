import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Bases

noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.GeneralizedRicciFlowBox

variable {S : ℝ → GeneralizedSliceCarrier.{u}}
  {g : ∀ t, RiemannianMetric 3 (S t).carrier} {J : Set ℝ}

def spaceMap (b : GeneralizedRicciFlowBox S g J)
    (p : b.interval × b.carrier.carrier) : Σ t, (S t).carrier :=
  ⟨p.1.val, b.forward p.1.val p.1.property p.2⟩

theorem spaceMap_injective (b : GeneralizedRicciFlowBox S g J) :
    Function.Injective b.spaceMap := by
  rintro ⟨⟨t, ht⟩, x⟩ ⟨⟨s, hs⟩, y⟩ h
  have hts : t = s := congrArg Sigma.fst h
  subst s
  have hxy : b.forward t ht x = b.forward t hs y := eq_of_heq (Sigma.mk.inj h).2
  have : x = y := (b.forward_openEmbedding t ht).injective hxy
  subst y
  rfl

end PoincareConjecture.GeneralizedRicciFlowBox

namespace PoincareConjecture.Surgery.BoxTopology

variable {S : ℝ → GeneralizedSliceCarrier.{u}}
  {g : ∀ t, RiemannianMetric 3 (S t).carrier} {J : Set ℝ}
  {ι : Type v} (B : ι → GeneralizedRicciFlowBox S g J)

@[instance_reducible] def topology : TopologicalSpace (Σ t, (S t).carrier) :=
  ⨆ b, TopologicalSpace.coinduced (B b).spaceMap inferInstance

theorem isOpen_iff (U : Set (Σ t, (S t).carrier)) :
    @IsOpen _ (topology B) U ↔ ∀ b, IsOpen ((B b).spaceMap ⁻¹' U) := by
  exact isOpen_iSup_iff

theorem spaceMap_continuous (b : ι) :
    @Continuous _ _ inferInstance (topology B) (B b).spaceMap :=
  continuous_iSup_rng continuous_coinduced_rng

theorem time_continuous :
    @Continuous _ ℝ (topology B) inferInstance Sigma.fst := by
  rw [topology, continuous_iSup_dom]
  intro b
  rw [continuous_coinduced_dom]
  exact continuous_subtype_val.comp continuous_fst

variable (compat : ∀ b c t ht hc x y,
  (B b).forward t ht x = (B c).forward t hc y →
  ∀ s hs hs', (B b).forward s hs x = (B c).forward s hs' y)

include compat

theorem overlap_isOpen (b c : ι) (U : Set ((B b).interval × (B b).carrier.carrier))
    (hU : IsOpen U) : IsOpen ((B c).spaceMap ⁻¹' ((B b).spaceMap '' U)) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨⟨t, htc⟩, x⟩ ⟨⟨⟨s, hsb⟩, y⟩, hy, he⟩
  have hst : s = t := congrArg Sigma.fst he
  subst s
  have hxy : (B b).forward t hsb y = (B c).forward t htc x :=
    eq_of_heq (Sigma.mk.inj he).2
  obtain ⟨A, V, hA, htA, hV, hyV, hAV⟩ := mem_nhds_prod_iff'.mp (hU.mem_nhds hy)
  obtain ⟨A₀, hA₀, hAeq⟩ := isOpen_induced_iff.mp hA
  obtain ⟨I, hI, hIb⟩ := (B b).relatively_open
  let C : Set (B c).interval := Subtype.val ⁻¹' (I ∩ A₀)
  let D : Set (B c).carrier.carrier :=
    (B c).forward t htc ⁻¹' ((B b).forward t hsb '' V)
  have hC : IsOpen C := (hI.inter hA₀).preimage continuous_subtype_val
  have hD : IsOpen D := ((B b).forward_openEmbedding t hsb).isOpenMap V hV |>.preimage
    ((B c).forward_openEmbedding t htc).continuous
  have htC : (⟨t, htc⟩ : (B c).interval) ∈ C := by
    refine ⟨?_, ?_⟩
    · exact (hIb ▸ hsb).2
    · have : (⟨t, hsb⟩ : (B b).interval) ∈ Subtype.val ⁻¹' A₀ := hAeq ▸ htA
      exact this
  have hxD : x ∈ D := ⟨y, hyV, hxy⟩
  apply Filter.mem_of_superset ((hC.prod hD).mem_nhds ⟨htC, hxD⟩)
  rintro ⟨⟨s, hsc⟩, z⟩ ⟨hsC, zD⟩
  obtain ⟨w, hwV, hwz⟩ := zD
  have hsJ : s ∈ J := (B c).relatively_open.choose_spec.2 ▸ hsc |>.1
  have hsb' : s ∈ (B b).interval := hIb ▸ (show s ∈ J ∩ I from ⟨hsJ, hsC.1⟩)
  refine ⟨(⟨s, hsb'⟩, w), hAV ⟨?_, hwV⟩, ?_⟩
  · rw [← hAeq]
    exact hsC.2
  · exact Sigma.ext rfl (heq_of_eq (compat b c t hsb htc w z hwz s hsb' hsc))

theorem spaceMap_openEmbedding (b : ι) :
    @IsOpenEmbedding _ _ inferInstance (topology B) (B b).spaceMap := by
  let := topology B
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap (spaceMap_continuous B b)
    (B b).spaceMap_injective
  intro U hU
  exact (isOpen_iff B _).mpr fun c => overlap_isOpen B compat b c U hU

variable (covers : ∀ t (x : (S t).carrier),
  ∃ b, ∃ ht : t ∈ (B b).interval, ∃ y, (B b).forward t ht y = x)

include covers

theorem t2Space : @T2Space (Σ t, (S t).carrier) (topology B) := by
  let := topology B
  constructor
  rintro ⟨t, x⟩ ⟨s, y⟩ hne
  by_cases hts : t = s
  · subst s
    have hxy : x ≠ y := fun h => hne (by cases h; rfl)
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hxy
    obtain ⟨b, htb, z, rfl⟩ := covers t x
    obtain ⟨c, htc, w, rfl⟩ := covers t y
    let A := (B b).forward t htb ⁻¹' U
    let C := (B c).forward t htc ⁻¹' V
    refine ⟨(B b).spaceMap '' (univ ×ˢ A), (B c).spaceMap '' (univ ×ˢ C),
      (spaceMap_openEmbedding B compat b).isOpenMap _
        (isOpen_univ.prod (hU.preimage ((B b).forward_openEmbedding t htb).continuous)),
      (spaceMap_openEmbedding B compat c).isOpenMap _
        (isOpen_univ.prod (hV.preimage ((B c).forward_openEmbedding t htc).continuous)),
      ⟨(⟨t, htb⟩, z), ⟨mem_univ _, hxU⟩, rfl⟩,
      ⟨(⟨t, htc⟩, w), ⟨mem_univ _, hyV⟩, rfl⟩, ?_⟩
    apply disjoint_left.mpr
    rintro p ⟨⟨⟨r, hrb⟩, z'⟩, ⟨_, hz'⟩, hbp⟩
      ⟨⟨⟨q, hqc⟩, w'⟩, ⟨_, hw'⟩, hcp⟩
    have he := hbp.trans hcp.symm
    have hrq : r = q := congrArg Sigma.fst he
    subst q
    have he' : (B b).forward r hrb z' = (B c).forward r hqc w' :=
      eq_of_heq (Sigma.mk.inj he).2
    have ht' := compat b c r hrb hqc z' w' he' t htb htc
    exact disjoint_left.mp hUV hz' (ht' ▸ hw')
  · obtain ⟨U, V, hU, hV, htU, hsV, hUV⟩ := t2_separation hts
    exact ⟨Sigma.fst ⁻¹' U, Sigma.fst ⁻¹' V,
      hU.preimage (time_continuous B), hV.preimage (time_continuous B),
      htU, hsV, hUV.preimage _⟩

omit compat in
theorem slice_continuous (t : ℝ) :
    @Continuous _ _ inferInstance (topology B) (@Sigma.mk ℝ (fun s => (S s).carrier) t) := by
  let := topology B
  apply continuous_def.mpr
  intro V hV
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨b, htb, y, rfl⟩ := covers t x
  let f : (B b).carrier.carrier → Σ s, (S s).carrier :=
    fun z => (B b).spaceMap (⟨t, htb⟩, z)
  have hf : Continuous f := (spaceMap_continuous B b).comp
    (continuous_const.prodMk continuous_id)
  have hU : IsOpen (f ⁻¹' V) := hV.preimage hf
  apply Filter.mem_of_superset
    (((B b).forward_openEmbedding t htb).isOpenMap _ hU |>.mem_nhds ⟨y, hx, rfl⟩)
  rintro z ⟨w, hw, rfl⟩
  exact hw

theorem exists_open_extension (t : ℝ) (U : Set (S t).carrier) (hU : IsOpen U) :
    ∃ V, @IsOpen _ (topology B) V ∧ Sigma.mk t ⁻¹' V = U := by
  let := topology B
  let V : Set (Σ s, (S s).carrier) := ⋃ b, ⋃ ht : t ∈ (B b).interval,
    (B b).spaceMap '' (univ ×ˢ ((B b).forward t ht ⁻¹' U))
  refine ⟨V, isOpen_iUnion fun b => isOpen_iUnion fun ht => ?_, ?_⟩
  · exact (spaceMap_openEmbedding B compat b).isOpenMap _
      (isOpen_univ.prod (hU.preimage ((B b).forward_openEmbedding t ht).continuous))
  · ext x
    constructor
    · intro hx
      change Sigma.mk t x ∈ V at hx
      simp only [V, mem_iUnion] at hx
      obtain ⟨b, ht, ⟨⟨s, hs⟩, y⟩, hy, he⟩ := hx
      have hst : s = t := congrArg Sigma.fst he
      subst s
      have he' : (B b).forward t hs y = x := eq_of_heq (Sigma.mk.inj he).2
      exact he' ▸ hy.2
    · intro hx
      obtain ⟨b, ht, y, rfl⟩ := covers t x
      change Sigma.mk t ((B b).forward t ht y) ∈ V
      apply mem_iUnion.mpr
      refine ⟨b, mem_iUnion.mpr ⟨ht, ?_⟩⟩
      exact ⟨(⟨t, ht⟩, y), ⟨mem_univ _, hx⟩, rfl⟩

theorem slice_embedding (t : ℝ) :
    @IsEmbedding _ _ inferInstance (topology B) (@Sigma.mk ℝ (fun s => (S s).carrier) t) := by
  let := topology B
  refine ⟨⟨?_⟩, sigma_mk_injective⟩
  apply TopologicalSpace.ext
  funext U
  apply propext
  rw [isOpen_induced_iff]
  constructor
  · exact exists_open_extension B compat covers t U
  · rintro ⟨V, hV, rfl⟩
    exact hV.preimage (slice_continuous B covers t)

theorem secondCountable [Countable ι] :
    @SecondCountableTopology (Σ t, (S t).carrier) (topology B) := by
  let := topology B
  let U : ι → Set (Σ t, (S t).carrier) := fun b => range (B b).spaceMap
  have (b : ι) : SecondCountableTopology (U b) :=
    (spaceMap_openEmbedding B compat b).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun b => (spaceMap_openEmbedding B compat b).isOpen_range)
  ext ⟨t, x⟩
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨b, ht, y, rfl⟩ := covers t x
  exact ⟨b, (⟨(⟨t, ht⟩, y), rfl⟩ : _ ∈ U b)⟩

end PoincareConjecture.Surgery.BoxTopology
