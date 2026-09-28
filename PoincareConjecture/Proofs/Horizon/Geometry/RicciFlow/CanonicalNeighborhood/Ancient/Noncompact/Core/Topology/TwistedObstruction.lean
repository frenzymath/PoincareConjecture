import PoincareConjecture.Proofs.Horizon.Compat.M33SphereNonempty
import PoincareConjecture.Proofs.M54.Mathlib.VanKampenGeneral
import PoincareConjecture.Proofs.M54.ConnectedSum.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Covering.SimplyConnected














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Topology

namespace PoincareConjecture.CoreTopology

abbrev TwistedStrip := UnitTwoSphere × Ioo (-2 : ℝ) 2

def stripDeck (p : TwistedStrip) : TwistedStrip :=
  (-p.1, ⟨-p.2.val, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩)

theorem stripDeck_continuous : Continuous stripDeck :=
  continuous_fst.neg.prodMk (continuous_snd.subtype_val.neg.subtype_mk _)

@[simp] theorem stripDeck_involutive (p : TwistedStrip) : stripDeck (stripDeck p) = p := by
  ext <;> simp [stripDeck]

def stripCoreInclusion (p : UnitTwoSphere × Icc (-1 : ℝ) 1) : TwistedStrip :=
  (p.1, ⟨p.2.val, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩)

theorem stripCoreInclusion_continuous : Continuous stripCoreInclusion :=
  continuous_fst.prodMk (continuous_snd.subtype_val.subtype_mk _)

def stripPositiveInclusion (p : UnitTwoSphere × Ioo (1 : ℝ) 2) : TwistedStrip :=
  (p.1, ⟨p.2.val, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩)

theorem stripPositiveInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding stripPositiveInclusion := by
  let i : Ioo (1 : ℝ) 2 → Ioo (-2 : ℝ) 2 := fun t =>
    ⟨t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have hi : Topology.IsOpenEmbedding i :=
    isOpen_Ioo.isOpenEmbedding_subtypeVal.of_comp i
      (isOpen_Ioo (a := (1 : ℝ)) (b := 2)).isOpenEmbedding_subtypeVal
  exact Topology.IsOpenEmbedding.id.prodMap hi




theorem isSimplyConnected_of_open_cover
    {M : Type*} [TopologicalSpace M] [SimplyConnectedSpace M]
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hpath : IsPathConnected U) (hinter : IsSimplyConnected (U ∩ V)) :
    IsSimplyConnected U := by
  let : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hpath
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro x p
  rw [← Path.Homotopic.Quotient.eq]
  apply VanKampen.inclusion_injective_at U V x hU hV hcover hinter
  exact Subsingleton.elim _ _



theorem no_twistedStrip_localHomeomorph
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (f : TwistedStrip → M) (hf : IsLocalHomeomorph f)
    (hfib : ∀ x y, f x = f y ↔ y = x ∨ y = stripDeck x) : False := by
  let C : Set M := range (f ∘ stripCoreInclusion)
  have hC : IsCompact C := isCompact_range
    (hf.continuous.comp stripCoreInclusion_continuous)
  let U : Set M := range f
  let V : Set M := Cᶜ
  have hU : IsOpen U := by
    change IsOpen (range f)
    rw [← image_univ]
    exact hf.isOpenMap _ isOpen_univ
  have hV : IsOpen V := hC.isClosed.isOpen_compl
  have hCU : C ⊆ U := by rintro _ ⟨p, rfl⟩; exact mem_range_self _
  have hcover : U ∪ V = univ := by
    ext z
    simp only [mem_union, mem_univ, iff_true]
    by_cases hz : z ∈ C
    · exact Or.inl (hCU hz)
    · exact Or.inr hz
  have hcore (x : TwistedStrip) : f x ∈ C ↔ |x.2.val| ≤ 1 := by
    constructor
    · rintro ⟨y, hy⟩
      rcases (hfib x (stripCoreInclusion y)).mp hy.symm with he | he
      · have ht := congrArg (fun p : TwistedStrip => p.2.val) he
        dsimp [stripCoreInclusion] at ht
        rw [← ht]
        exact abs_le.mpr y.2.property
      · have ht := congrArg (fun p : TwistedStrip => p.2.val) he
        dsimp [stripCoreInclusion, stripDeck] at ht
        rw [← abs_neg, ← ht]
        exact abs_le.mpr y.2.property
    · intro hx
      exact ⟨(x.1, ⟨x.2.val, abs_le.mp hx⟩), rfl⟩
  let g : UnitTwoSphere × Ioo (1 : ℝ) 2 → M := f ∘ stripPositiveInclusion
  have hgLocal : IsLocalHomeomorph g :=
    hf.comp stripPositiveInclusion_isOpenEmbedding.isLocalHomeomorph
  have hginj : Function.Injective g := by
    intro x y he
    rcases (hfib (stripPositiveInclusion x) (stripPositiveInclusion y)).mp he with h | h
    · exact stripPositiveInclusion_isOpenEmbedding.injective h.symm
    · have ht := congrArg (fun p : TwistedStrip => p.2.val) h
      dsimp [stripPositiveInclusion, stripDeck] at ht
      linarith [x.2.property.1, y.2.property.1]
  have hg : Topology.IsOpenEmbedding g := hgLocal.isOpenEmbedding_of_injective hginj
  have hoverlap : U ∩ V = range g := by
    ext z
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      have hx' : 1 < |x.2.val| := lt_of_not_ge (fun h => hx ((hcore x).mpr h))
      rcases lt_or_ge 0 x.2.val with hp | hn
      · exact ⟨(x.1, ⟨x.2.val, by simpa [abs_of_pos hp] using hx', x.2.property.2⟩), rfl⟩
      · refine ⟨(-x.1, ⟨-x.2.val, ?_⟩), ?_⟩
        · constructor
          · simpa [abs_of_nonpos hn] using hx'
          · linarith [x.2.property.1]
        · exact ((hfib x (stripDeck x)).mpr (Or.inr rfl)).symm
    · rintro ⟨x, rfl⟩
      refine ⟨mem_range_self (stripPositiveInclusion x), ?_⟩
      intro hx
      have hb := (hcore (stripPositiveInclusion x)).mp hx
      have hp : 0 < x.2.val := lt_trans zero_lt_one x.2.property.1
      simp only [stripPositiveInclusion, abs_of_pos hp] at hb
      linarith [x.2.property.1]
  let : SimplyConnectedSpace (UnitTwoSphere × Ioo (1 : ℝ) 2) :=
    SurgeryCoordinates.sphere_prod_interval_simplyConnected 1 2 (by norm_num)
  have hinter : IsSimplyConnected (U ∩ V) := by
    rw [hoverlap]
    simpa only [image_univ] using
      (hg.isEmbedding.isSimplyConnected_image (s := univ)).mpr
        (Homeomorph.Set.univ _).toHomotopyEquiv.simplyConnectedSpace
  let : SimplyConnectedSpace TwistedStrip :=
    SurgeryCoordinates.sphere_prod_interval_simplyConnected (-2) 2 (by norm_num)
  have hpath : IsPathConnected U := by
    simpa only [image_univ] using isPathConnected_univ.image hf.continuous
  let : SimplyConnectedSpace U :=
    isSimplyConnected_of_open_cover hU hV hcover hpath hinter
  let : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  let F : TwistedStrip → U := fun x => ⟨f x, mem_range_self x⟩
  have hFlocal : IsLocalHomeomorph F :=
    IsLocalHomeomorph.of_comp (g := (Subtype.val : U → M))
      hf hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      (hf.continuous.subtype_mk _)
  have hFsurj : Function.Surjective F := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hFfib (x y : TwistedStrip) : F x = F y ↔ y = x ∨ y = stripDeck x := by
    rw [Subtype.mk.injEq]
    exact hfib x y
  have hFclosed : IsClosedMap F := by
    have hquot := hFlocal.isOpenMap.isQuotientMap hFlocal.continuous hFsurj
    intro A hA
    apply hquot.isClosed_preimage.mp
    have he : F ⁻¹' (F '' A) = A ∪ stripDeck ⁻¹' A := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        rcases (hFfib x y).mp hyx.symm with h | h
        · exact Or.inl (h ▸ hy)
        · exact Or.inr (show stripDeck x ∈ A from h ▸ hy)
      · rintro (hx | hx)
        · exact ⟨x, hx, rfl⟩
        · exact ⟨stripDeck x, hx, ((hFfib x (stripDeck x)).mpr (Or.inr rfl)).symm⟩
    rw [he]
    exact hA.union (hA.preimage stripDeck_continuous)
  have hFcover : IsCoveringMap F := by
    apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
    apply hFclosed.isCoveringMapOn_of_isLocalHomeomorphOn
      (fun y _ => ?_) hFlocal.isLocalHomeomorphOn
    obtain ⟨x, rfl⟩ := hFsurj y
    have he : F ⁻¹' {F x} = {x, stripDeck x} := by
      ext y
      change F y = F x ↔ y = x ∨ y = stripDeck x
      rw [eq_comm, hFfib]
    rw [he]
    exact (finite_singleton _).insert _
  have hFinj := (Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected hFcover).1
  let x : TwistedStrip := (Classical.choice inferInstance, ⟨0, by norm_num⟩)
  have he := hFinj ((hFfib x (stripDeck x)).mpr (Or.inr rfl))
  exact ne_neg_of_mem_unit_sphere ℝ x.1 (congrArg Prod.fst he)

end PoincareConjecture.CoreTopology
