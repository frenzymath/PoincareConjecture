import PoincareConjecture.Proofs.M38.TubeExclusion

set_option autoImplicit false

open Set Topology

universe u

namespace PoincareConjecture.M38

variable {S : Type u} [TopologicalSpace S]

def cylinderHeight (x : S × Set.Ioo (0 : ℝ) 1) : ℝ := x.2.val

theorem cylinderHeight_continuous :
    Continuous (cylinderHeight (S := S)) :=
  continuous_subtype_val.comp continuous_snd

theorem cylinder_compact_height_bounds {K : Set (S × Set.Ioo (0 : ℝ) 1)}
    (hK : IsCompact K) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      ∀ x ∈ K, a < cylinderHeight x ∧ cylinderHeight x < b := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1 / 4, 3 / 4, by norm_num, by norm_num, by norm_num, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne cylinderHeight_continuous.continuousOn
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne cylinderHeight_continuous.continuousOn
  have hx0 : 0 < cylinderHeight x := x.2.property.1
  have hy1 : cylinderHeight y < 1 := y.2.property.2
  have hxy : cylinderHeight x ≤ cylinderHeight y := hmin hy
  refine ⟨cylinderHeight x / 2, (cylinderHeight y + 1) / 2,
    by linarith, by linarith, by linarith, ?_⟩
  intro z hz
  have hl : cylinderHeight x ≤ cylinderHeight z := hmin hz
  have hu : cylinderHeight z ≤ cylinderHeight y := hmax hz
  constructor <;> linarith

theorem cylinder_slab_compact [CompactSpace S] {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) :
    IsCompact {x : S × Set.Ioo (0 : ℝ) 1 |
      a ≤ cylinderHeight x ∧ cylinderHeight x ≤ b} := by
  let f : S × Set.Icc a b → S × Set.Ioo (0 : ℝ) 1 :=
    fun x => (x.1, ⟨x.2.val, ha.trans_le x.2.property.1, x.2.property.2.trans_lt hb⟩)
  have hf : Continuous f :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hr : Set.range f = {x | a ≤ cylinderHeight x ∧ cylinderHeight x ≤ b} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2.property
    · intro hx
      exact ⟨(x.1, ⟨x.2.val, hx⟩), rfl⟩
  rw [← hr]
  exact isCompact_range hf

theorem cylinder_level_compact [CompactSpace S] {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    IsCompact {x : S × Set.Ioo (0 : ℝ) 1 | cylinderHeight x = a} := by
  convert cylinder_slab_compact (S := S) ha.1 ha.2 using 1
  ext x
  exact ⟨fun h => ⟨h.ge, h.le⟩, fun h => le_antisymm h.2 h.1⟩

theorem cylinder_tails_preconnected [PreconnectedSpace S] {a : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    IsPreconnected {x : S × Set.Ioo (0 : ℝ) 1 | cylinderHeight x < a} ∧
      IsPreconnected {x : S × Set.Ioo (0 : ℝ) 1 | a < cylinderHeight x} := by
  let DL : Set (S × ℝ) := (Set.univ : Set S) ×ˢ Set.Ioo (0 : ℝ) a
  let DR : Set (S × ℝ) := (Set.univ : Set S) ×ˢ Set.Ioo a 1
  let : PreconnectedSpace DL :=
    Subtype.preconnectedSpace
      (isPreconnected_univ.prod
        (isPreconnected_Ioo : IsPreconnected (Set.Ioo (0 : ℝ) a)))
  let : PreconnectedSpace DR :=
    Subtype.preconnectedSpace
      (isPreconnected_univ.prod
        (isPreconnected_Ioo : IsPreconnected (Set.Ioo a 1)))
  let gL : DL → S × Set.Ioo (0 : ℝ) 1 := fun x =>
    (x.1.1, ⟨x.1.2, x.2.2.1, x.2.2.2.trans ha.2⟩)
  let gR : DR → S × Set.Ioo (0 : ℝ) 1 := fun x =>
    (x.1.1, ⟨x.1.2, ha.1.trans x.2.2.1, x.2.2.2⟩)
  have hgL : Continuous gL := by fun_prop
  have hgR : Continuous gR := by fun_prop
  have hL :
      Set.range gL = {x : S × Set.Ioo (0 : ℝ) 1 | cylinderHeight x < a} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property.2.2
    · intro hx
      exact ⟨⟨(x.1, x.2.val), Set.mem_univ _, x.2.property.1, hx⟩, rfl⟩
  have hR :
      Set.range gR = {x : S × Set.Ioo (0 : ℝ) 1 | a < cylinderHeight x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property.2.1
    · intro hx
      exact ⟨⟨(x.1, x.2.val), Set.mem_univ _, hx, x.2.property.2⟩, rfl⟩
  constructor
  · rw [← hL]
    simpa only [Set.image_univ] using isPreconnected_univ.image gL hgL.continuousOn
  · rw [← hR]
    simpa only [Set.image_univ] using isPreconnected_univ.image gR hgR.continuousOn

theorem no_cylinder_homeomorph_compact_compl [CompactSpace S] [ConnectedSpace S]
    [T2Space S] {K : Set (S × Set.Ioo (0 : ℝ) 1)}
    (hK : IsCompact K) (hne : K.Nonempty) :
    IsEmpty ((Kᶜ : Set (S × Set.Ioo (0 : ℝ) 1)) ≃ₜ (S × Set.Ioo (0 : ℝ) 1)) := by
  classical
  refine ⟨fun e => ?_⟩
  let C := S × Set.Ioo (0 : ℝ) 1
  let q : C → ℝ := cylinderHeight
  have hq : Continuous q := cylinderHeight_continuous
  obtain ⟨a, b, ha, hab, hb, hKb⟩ := cylinder_compact_height_bounds hK
  have ha1 : a < 1 := hab.trans hb
  have hb0 : 0 < b := ha.trans hab
  let E : Set C := {x | q x = a} ∪ {x | q x = b}
  have hE : IsCompact E :=
    (cylinder_level_compact ⟨ha, ha1⟩).union (cylinder_level_compact ⟨hb0, hb⟩)
  have hEW : E ⊆ Set.range (Subtype.val : (Kᶜ : Set C) → C) := by
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    intro hxK
    have h := hKb x hxK
    rcases hx with hx | hx <;> change q x = _ at hx <;> change a < q x ∧ q x < b at h <;>
      linarith
  have hEc : IsCompact (e '' ((Subtype.val : (Kᶜ : Set C) → C) ⁻¹' E)) :=
    (IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hE hEW).image e.continuous
  obtain ⟨c, d, hc, hcd, hd, hEb⟩ := cylinder_compact_height_bounds hEc
  let f : C → C := fun x => (e.symm x).val
  have hf : Continuous f := continuous_subtype_val.comp e.symm.continuous
  have hfi : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  let H : Set C := f '' {x | c ≤ q x ∧ q x ≤ d}
  let L : Set C := f '' {x | q x < c}
  let R : Set C := f '' {x | d < q x}
  have hH : IsCompact H := (cylinder_slab_compact hc hd).image hf
  have hEH : E ⊆ H := by
    intro x hx
    obtain ⟨w, hw⟩ := hEW hx
    have hwE : w ∈ (Subtype.val : (Kᶜ : Set C) → C) ⁻¹' E := by
      change (w : C) ∈ E
      rw [hw]
      exact hx
    have hew := hEb (e w) ⟨w, hwE, rfl⟩
    exact ⟨e w, ⟨hew.1.le, hew.2.le⟩,
      (congrArg Subtype.val (e.symm_apply_apply w)).trans hw⟩
  have hHK : ∀ x ∈ H, x ∉ K := by
    rintro x ⟨y, _, rfl⟩
    exact (e.symm y).property
  have hLH : ∀ x ∈ L, x ∉ H := by
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
    have hzy := hfi heq
    subst z
    exact not_lt_of_ge hz.1 hy
  have hRH : ∀ x ∈ R, x ∉ H := by
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
    have hzy := hfi heq
    subst z
    exact not_lt_of_ge hz.2 hy
  have hL : IsPreconnected L :=
    ((cylinder_tails_preconnected (S := S) ⟨hc, hcd.trans hd⟩).1).image f hf.continuousOn
  have hR : IsPreconnected R :=
    ((cylinder_tails_preconnected (S := S) ⟨hc.trans hcd, hd⟩).2).image f hf.continuousOn
  have hLa : ∀ x ∈ L, q x ≠ a := fun x hx heq => hLH x hx (hEH (Or.inl heq))
  have hLb : ∀ x ∈ L, q x ≠ b := fun x hx heq => hLH x hx (hEH (Or.inr heq))
  have hRa : ∀ x ∈ R, q x ≠ a := fun x hx heq => hRH x hx (hEH (Or.inl heq))
  have hRb : ∀ x ∈ R, q x ≠ b := fun x hx heq => hRH x hx (hEH (Or.inr heq))
  have hcover (x : C) (hx : x ∉ K) (hxH : x ∉ H) : x ∈ L ∨ x ∈ R := by
    let y := e ⟨x, hx⟩
    have hy : f y = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    by_cases hcy : q y < c
    · exact Or.inl ⟨y, hcy, hy⟩
    by_cases hyd : d < q y
    · exact Or.inr ⟨y, hyd, hy⟩
    exact (hxH ⟨y, ⟨le_of_not_gt hcy, le_of_not_gt hyd⟩, hy⟩).elim
  obtain ⟨v, w, hv, hvw, hw, hHb⟩ := cylinder_compact_height_bounds hH
  let s : S := Classical.choice inferInstance
  have hmin : 0 < min a v := lt_min ha hv
  have hmax : max b w < 1 := max_lt hb hw
  let low : C := (s, ⟨min a v / 2, by linarith, by linarith [min_le_left a v]⟩)
  let high : C := (s, ⟨(max b w + 1) / 2, by linarith [le_max_left b w],
    by linarith⟩)
  have hlow : q low < a ∧ q low < v := by
    dsimp [low, q, cylinderHeight]
    constructor <;> linarith [min_le_left a v, min_le_right a v]
  have hhigh : b < q high ∧ w < q high := by
    dsimp [high, q, cylinderHeight]
    constructor <;> linarith [le_max_left b w, le_max_right b w]
  have hlowK : low ∉ K := fun h => (not_lt_of_ge (hKb low h).1.le) hlow.1
  have hhighK : high ∉ K := fun h => (not_lt_of_ge (hKb high h).2.le) hhigh.1
  have hlowH : low ∉ H := fun h => (not_lt_of_ge (hHb low h).1.le) hlow.2
  have hhighH : high ∉ H := fun h => (not_lt_of_ge (hHb high h).2.le) hhigh.2
  have hmid (x : C) (hx : x ∉ K) (hax : a ≤ q x) (hxb : q x ≤ b) : x ∈ H := by
    by_contra hxH
    have hlL : low ∈ L → ∀ z ∈ L, q z < a := fun h =>
      fun z hz => hL.gt_of_ne hq.continuousOn hLa ⟨low, h, hlow.1⟩ hz
    have hlR : low ∈ R → ∀ z ∈ R, q z < a := fun h =>
      fun z hz => hR.gt_of_ne hq.continuousOn hRa ⟨low, h, hlow.1⟩ hz
    have hhL : high ∈ L → ∀ z ∈ L, b < q z := fun h =>
      fun z hz => hL.lt_of_ne hq.continuousOn hLb ⟨high, h, hhigh.1⟩ hz
    have hhR : high ∈ R → ∀ z ∈ R, b < q z := fun h =>
      fun z hz => hR.lt_of_ne hq.continuousOn hRb ⟨high, h, hhigh.1⟩ hz
    rcases hcover low hlowK hlowH with hl | hl <;>
      rcases hcover high hhighK hhighH with hh | hh
    · have h := hlL hl high hh
      linarith [hhigh.1]
    · rcases hcover x hx hxH with h | h
      · exact not_lt_of_ge hax (hlL hl x h)
      · exact not_lt_of_ge hxb (hhR hh x h)
    · rcases hcover x hx hxH with h | h
      · exact not_lt_of_ge hxb (hhL hh x h)
      · exact not_lt_of_ge hax (hlR hl x h)
    · have h := hlR hl high hh
      linarith [hhigh.1]
  have hKopen : IsOpen K := by
    have heq : K = {x | a < q x ∧ q x < b} \ H := by
      ext x
      constructor
      · intro hx
        exact ⟨hKb x hx, fun hxH => hHK x hxH hx⟩
      · rintro ⟨hx, hxH⟩
        by_contra hxK
        exact hxH (hmid x hxK hx.1.le hx.2.le)
    rw [heq]
    have hopen : IsOpen ({x : C | a < q x} ∩ {x : C | q x < b}) :=
      (isOpen_lt continuous_const hq).inter (isOpen_lt hq continuous_const)
    exact hopen.sdiff hH.isClosed
  let : ConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo zero_lt_one)
  let : ConnectedSpace C := inferInstance
  have hKuniv : K = Set.univ := (IsClopen.eq_univ ⟨hK.isClosed, hKopen⟩ hne)
  exact hlowK (hKuniv.symm ▸ Set.mem_univ low)

end PoincareConjecture.M38
