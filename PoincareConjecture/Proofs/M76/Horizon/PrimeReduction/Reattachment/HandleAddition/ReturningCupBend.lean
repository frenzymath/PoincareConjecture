import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Cup.Bridge

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryCup

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "I" => Icc (0 : ℝ) 1

def joinedBridgeCoordinates (p : P2) : C3 :=
  ((2 * p.2 + 1, |2 * p.2 + 1|), p.1)

def bridgeBend (t : ℝ) (p : P2) : C3 :=
  ((2 * p.2 + 1, (1-t) * |2 * p.2 + 1| + t), p.1)

theorem bridgeBend_continuous : Continuous (fun z : ℝ × P2 => bridgeBend z.1 z.2) := by
  unfold bridgeBend
  fun_prop

theorem bridgeBend_mapsTo (t : I) : MapsTo (bridgeBend t) (halfSource false) tube := by
  intro p hp
  have hx : -1 ≤ 2*p.2+1 ∧ 2*p.2+1 ≤ 1 := by
    constructor <;> linarith [hp.2.1,hp.2.2]
  have ha : |2*p.2+1| ≤ 1 := abs_le.mpr hx
  have hnon := abs_nonneg (2*p.2+1)
  have ht := t.property
  change ((-1 ≤ 2*p.2+1 ∧ 2*p.2+1 ≤ 1) ∧
    (-1 ≤ (1-(t:ℝ))*|2*p.2+1|+(t:ℝ) ∧
      (1-(t:ℝ))*|2*p.2+1|+(t:ℝ) ≤ 1)) ∧ p.1 ∈ I
  exact ⟨⟨hx,by
    constructor
    · nlinarith [ht.1,ht.2,mul_nonneg (sub_nonneg.mpr ht.2) hnon]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha)]⟩,hp.1⟩

theorem bridgeBend_zero (p : P2) : bridgeBend 0 p = joinedBridgeCoordinates p := by
  simp [bridgeBend,joinedBridgeCoordinates]

theorem bridgeBend_one (p : P2) : bridgeBend 1 p = bridgeCoordinates p := by
  simp [bridgeBend,bridgeCoordinates_apply]

theorem bridgeBend_far_left (t u : ℝ) : bridgeBend t (u,-1) = ((-1,1),u) := by
  norm_num [bridgeBend]

theorem bridgeBend_far_right (t u : ℝ) : bridgeBend t (u,0) = ((1,1),u) := by
  simp [bridgeBend]

theorem bridgeBend_eq_top_of_end (t : ℝ) (p : P2) (hp : p.2 = 0 ∨ p.2 = -1) :
    bridgeBend t p = bridgeCoordinates p := by
  rcases hp with hp | hp
  · have heq : p = (p.1,0) := Prod.ext rfl hp
    rw [heq,bridgeBend_far_right,bridgeCoordinates_apply]
    norm_num
  · have heq : p = (p.1,-1) := Prod.ext rfl hp
    rw [heq,bridgeBend_far_left,bridgeCoordinates_apply]
    norm_num

theorem joinedBridgeCoordinates_image :
    joinedBridgeCoordinates '' halfSource false =
      (fun p : P2 => ((p.2,-p.2),p.1)) '' (I ×ˢ Icc (-1 : ℝ) 0) ∪
      (fun p : P2 => ((p.2,p.2),p.1)) '' (I ×ˢ Icc (0 : ℝ) 1) := by
  apply Subset.antisymm
  · rintro _ ⟨p,hp,rfl⟩
    have hx : -1 ≤ 2*p.2+1 ∧ 2*p.2+1 ≤ 1 := by
      constructor <;> linarith [hp.2.1,hp.2.2]
    by_cases h : 2*p.2+1 ≤ 0
    · exact Or.inl ⟨(p.1,2*p.2+1),⟨hp.1,hx.1,h⟩,by
        simp [joinedBridgeCoordinates,abs_of_nonpos h]⟩
    · exact Or.inr ⟨(p.1,2*p.2+1),⟨hp.1,le_of_not_ge h,hx.2⟩,by
        simp [joinedBridgeCoordinates,abs_of_nonneg (le_of_not_ge h)]⟩
  · rintro z (⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
    · refine ⟨(p.1,(p.2-1)/2),⟨hp.1,?_⟩,?_⟩
      · change -1 ≤ (p.2-1)/2 ∧ (p.2-1)/2 ≤ 0
        constructor <;> linarith [hp.2.1,hp.2.2]
      · have hx : 2*((p.2-1)/2)+1 = p.2 := by ring
        simp [joinedBridgeCoordinates,hx,abs_of_nonpos hp.2.2]
    · refine ⟨(p.1,(p.2-1)/2),⟨hp.1,?_⟩,?_⟩
      · change -1 ≤ (p.2-1)/2 ∧ (p.2-1)/2 ≤ 0
        constructor <;> linarith [hp.2.1,hp.2.2]
      · have hx : 2*((p.2-1)/2)+1 = p.2 := by ring
        simp [joinedBridgeCoordinates,hx,abs_of_nonneg hp.2.1]

theorem joinedBridgeCoordinates_injective : Function.Injective joinedBridgeCoordinates := by
  intro p q hpq
  have ht := congrArg Prod.snd hpq
  have hu := congrArg (fun z : C3 => z.1.1) hpq
  apply Prod.ext ht
  change 2*p.2+1 = 2*q.2+1 at hu
  linarith

theorem joinedBridgeCoordinates_mapsTo : MapsTo joinedBridgeCoordinates (halfSource false) tube := by
  intro p hp
  rw [←bridgeBend_zero]
  exact bridgeBend_mapsTo ⟨0,by norm_num⟩ hp

theorem exists_original_bridge_bend
    {X : Type*} [TopologicalSpace X] {τ : C3 → X}
    (hτ : ContinuousOn τ tube) {R : Set X} (hR : MapsTo τ tube R)
    (hfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) :
    ∃ H : C(I × ↥(halfSource false),X),
      (∀ p : halfSource false,H (⟨0,by norm_num⟩,p) = τ (joinedBridgeCoordinates p)) ∧
      (∀ p : halfSource false,H (⟨1,by norm_num⟩,p) = τ (bridgeCoordinates p)) ∧
      (∀ z,H z ∈ R) ∧
      (∀ z,H z ∈ frontier R ↔ z.2.val.1 = 0 ∨ z.2.val.1 = 1) ∧
      (∀ t : I,∀ u : I,H (t,⟨((u:ℝ),-1),⟨u.property,by norm_num⟩⟩) = τ ((-1,1),(u:ℝ))) ∧
      (∀ t : I,∀ u : I,H (t,⟨((u:ℝ),0),⟨u.property,by norm_num⟩⟩) = τ ((1,1),(u:ℝ))) := by
  let v : C(I × ↥(halfSource false),tube) :=
    ⟨fun z => ⟨bridgeBend z.1 z.2,bridgeBend_mapsTo z.1 z.2.property⟩,by
      apply Continuous.subtype_mk
      exact bridgeBend_continuous.comp (show Continuous
        (fun z : I × ↥(halfSource false) => ((z.1:ℝ),(z.2:P2))) by fun_prop)⟩
  refine ⟨⟨_,hτ.domRestrict.comp v.continuous⟩,?_,?_,?_,?_,?_,?_⟩
  · intro p
    exact congrArg τ (bridgeBend_zero p)
  · intro p
    exact congrArg τ (bridgeBend_one p)
  · intro z
    exact hR (v z).property
  · intro z
    exact hfront _ (v z).property
  · intro t u
    exact congrArg τ (bridgeBend_far_left t u)
  · intro t u
    exact congrArg τ (bridgeBend_far_right t u)

theorem trimmed_disk_bridge_contacts
    {X F : Type*} {c : P2 → F} {B S : Set F} {f : F → X} {τ : C3 → X}
    (hc : MapsTo c source S) (hci : InjOn c source) (hB : B ⊆ S) (hfi : InjOn f S)
    (htrim : B ∩ (c '' halfSource true) = c '' arm 1)
    (hperiod : ∀ p ∈ source,f (c p) = τ ((p.2,p.2),p.1))
    {T : Set X} (hBT : Disjoint (f '' B) T)
    (hA : ∀ z ∈ tube,τ z ∈ f '' S ↔ z.1.2 = z.1.1)
    (hT : ∀ z ∈ tube,τ z ∈ T ↔ z.1.2 = -z.1.1) :
    (∀ p ∈ halfSource false,τ (bridgeCoordinates p) ∈ f '' B ↔ p.2 = 0) ∧
    (∀ p ∈ halfSource false,τ (joinedBridgeCoordinates p) ∈ f '' B ↔ p.2 = 0) := by
  have hfar (u : ℝ) (hu : u ∈ I) : τ ((1,1),u) ∈ f '' B := by
    have hb : c (u,1) ∈ B := (htrim.superset ⟨(u,1),⟨hu,rfl⟩,rfl⟩).1
    exact ⟨c (u,1),hb,hperiod (u,1) ⟨hu,by norm_num⟩⟩
  constructor
  · intro p hp
    constructor
    · intro hb
      have hx := (hA _ (bridgeCoordinates_mapsTo hp)).mp (image_mono hB hb)
      change 1 = 2*p.2+1 at hx
      linarith
    · intro hp0
      simpa only [bridgeCoordinates_apply,hp0,mul_zero,zero_add] using hfar p.1 hp.1
  · intro p hp
    constructor
    · intro hb
      have hx : -1 ≤ 2*p.2+1 ∧ 2*p.2+1 ≤ 1 := by
        constructor <;> linarith [hp.2.1,hp.2.2]
      by_cases hs : 2*p.2+1 ≤ 0
      · have ht : τ (joinedBridgeCoordinates p) ∈ T :=
          (hT _ (joinedBridgeCoordinates_mapsTo hp)).mpr (abs_of_nonpos hs)
        exact (Set.disjoint_left.mp hBT hb ht).elim
      · have hpos : 0 ≤ 2*p.2+1 := le_of_not_ge hs
        have hsource : (p.1,2*p.2+1) ∈ source := ⟨hp.1,hx⟩
        have hvalue : f (c (p.1,2*p.2+1)) = τ (joinedBridgeCoordinates p) := by
          simpa only [joinedBridgeCoordinates,abs_of_nonneg hpos] using hperiod _ hsource
        obtain ⟨b,hbB,hbeq⟩ := hb
        have heq := hfi (hB hbB) (hc hsource) (hbeq.trans hvalue.symm)
        have hcb : c (p.1,2*p.2+1) ∈ B := heq ▸ hbB
        have hcarm := htrim.subset ⟨hcb,⟨(p.1,2*p.2+1),⟨hp.1,hpos,hx.2⟩,rfl⟩⟩
        obtain ⟨q,hq,hqe⟩ := hcarm
        have hqsource : q ∈ source := arm_far_subset_source true hq
        have hpq := congrArg Prod.snd (hci hqsource hsource hqe)
        have hqfar : q.2 = 1 := hq.2
        change q.2 = 2*p.2+1 at hpq
        linarith
    · intro hp0
      simpa only [joinedBridgeCoordinates,hp0,mul_zero,zero_add,abs_one] using hfar p.1 hp.1

theorem retained_core_bridge_contacts
    {X E : Type*} {c : P2 → E} {C S : Set E} {f : E → X} {τ : C3 → X}
    (hc : MapsTo c source S) (hci : InjOn c source) (hC : C ⊆ S) (hfi : InjOn f S)
    (hcontact : C ∩ (c '' halfSource false) = c '' arm (-1))
    (hperiod : ∀ p ∈ source,f (c p) = τ ((p.2,-p.2),p.1))
    (hT : ∀ z ∈ tube,τ z ∈ f '' S ↔ z.1.2 = -z.1.1) :
    (∀ p ∈ halfSource false,τ (bridgeCoordinates p) ∈ f '' C ↔ p.2 = -1) ∧
    (∀ p ∈ halfSource false,τ (joinedBridgeCoordinates p) ∈ f '' C ↔ p.2 = -1) := by
  have hfar (u : ℝ) (hu : u ∈ I) : τ ((-1,1),u) ∈ f '' C := by
    have hb : c (u,-1) ∈ C := (hcontact.superset ⟨(u,-1),⟨hu,rfl⟩,rfl⟩).1
    exact ⟨c (u,-1),hb,by simpa using hperiod (u,-1) ⟨hu,by norm_num⟩⟩
  constructor
  · intro p hp
    constructor
    · intro hb
      have hx := (hT _ (bridgeCoordinates_mapsTo hp)).mp (image_mono hC hb)
      change 1 = -(2*p.2+1) at hx
      linarith
    · intro hp0
      simpa only [bridgeCoordinates_apply,hp0,show 2*(-1:ℝ)+1 = -1 by norm_num] using hfar p.1 hp.1
  · intro p hp
    constructor
    · intro hb
      have hx : -1 ≤ 2*p.2+1 ∧ 2*p.2+1 ≤ 1 := by
        constructor <;> linarith [hp.2.1,hp.2.2]
      have hplane := (hT _ (joinedBridgeCoordinates_mapsTo hp)).mp (image_mono hC hb)
      change |2*p.2+1| = -(2*p.2+1) at hplane
      have hneg : 2*p.2+1 ≤ 0 := by linarith [abs_nonneg (2*p.2+1)]
      have hsource : (p.1,2*p.2+1) ∈ source := ⟨hp.1,hx⟩
      have hvalue : f (c (p.1,2*p.2+1)) = τ (joinedBridgeCoordinates p) := by
        simpa only [joinedBridgeCoordinates,abs_of_nonpos hneg] using hperiod _ hsource
      obtain ⟨b,hbC,hbeq⟩ := hb
      have heq := hfi (hC hbC) (hc hsource) (hbeq.trans hvalue.symm)
      have hcb : c (p.1,2*p.2+1) ∈ C := heq ▸ hbC
      obtain ⟨q,hq,hqe⟩ := hcontact.subset
        ⟨hcb,⟨(p.1,2*p.2+1),⟨hp.1,hx.1,hneg⟩,rfl⟩⟩
      have hqsource : q ∈ source := arm_far_subset_source false hq
      have hpq := congrArg Prod.snd (hci hqsource hsource hqe)
      have hqfar : q.2 = -1 := hq.2
      change q.2 = 2*p.2+1 at hpq
      linarith
    · intro hp0
      simpa only [joinedBridgeCoordinates,hp0,show 2*(-1:ℝ)+1 = -1 by norm_num,
        abs_neg,abs_one] using hfar p.1 hp.1

theorem joined_bridge_image_of_source_strips
    {X E F : Type*} {c₀ : P2 → E} {c₁ : P2 → F}
    {f₀ : E → X} {f₁ : F → X} {τ : C3 → X}
    (hperiod₀ : ∀ p ∈ source,f₀ (c₀ p) = τ ((p.2,-p.2),p.1))
    (hperiod₁ : ∀ p ∈ source,f₁ (c₁ p) = τ ((p.2,p.2),p.1)) :
    τ '' (joinedBridgeCoordinates '' halfSource false) =
      f₀ '' (c₀ '' halfSource false) ∪ f₁ '' (c₁ '' halfSource true) := by
  rw [joinedBridgeCoordinates_image,image_union,←image_comp,←image_comp,
    ←image_comp,←image_comp]
  congr 1
  · exact image_congr (fun p hp => (hperiod₀ p (halfSource_subset_source false hp)).symm)
  · exact image_congr (fun p hp => (hperiod₁ p (halfSource_subset_source true hp)).symm)

theorem exists_physical_cup_bend_of_end_contacts
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {τ : C3 → X} (hτ : ContinuousOn τ tube) (hτi : InjOn τ tube)
    {B R : Set X} (hB : IsCompact B) (hBR : B ⊆ R) (hR : MapsTo τ tube R)
    (hfront : ∀ z ∈ tube,τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (hBtop : ∀ p ∈ halfSource false,τ (bridgeCoordinates p) ∈ B → p.2 = 0 ∨ p.2 = -1)
    (hBraw : ∀ p ∈ halfSource false,τ (joinedBridgeCoordinates p) ∈ B → p.2 = 0 ∨ p.2 = -1) :
    let Y := B ∪ τ '' (bridgeCoordinates '' halfSource false)
    ∃ H : C(I × ↥Y,X),
      (∀ z : Y,H (⟨1,by norm_num⟩,z) = z) ∧
      (∀ z,H z ∈ R) ∧
      (∀ z,H z ∈ frontier R ↔ (z.2:X) ∈ frontier R) ∧
      (∀ z,(z.2:X) ∈ B → H z = z.2) ∧
      (∀ t : I,∀ p : halfSource false,
        H (t,⟨τ (bridgeCoordinates p),Or.inr ⟨_,⟨p,p.property,rfl⟩,rfl⟩⟩) =
          τ (bridgeBend t p)) ∧
      Function.Injective (fun z : Y => H (⟨0,by norm_num⟩,z)) ∧
      Set.range (fun z : Y => H (⟨0,by norm_num⟩,z)) =
        B ∪ τ '' (joinedBridgeCoordinates '' halfSource false) := by
  classical
  let A := halfSource false
  let c : A → X := fun p => τ (bridgeCoordinates p)
  have hA : IsCompact A := isCompact_Icc.prod isCompact_Icc
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hc : Continuous c := by
    apply hτ.comp_continuous
    · exact bridgeCoordinates.continuous.comp continuous_subtype_val
    · exact fun p => bridgeCoordinates_mapsTo p.property
  have hci : Function.Injective c := by
    intro p q hpq
    exact Subtype.ext (bridgeCoordinates_injective
      (hτi (bridgeCoordinates_mapsTo p.property) (bridgeCoordinates_mapsTo q.property) hpq))
  let T := Set.range c
  have hTc : IsCompact T := isCompact_range hc
  let J : A ≃ₜ T := (hc.isClosedEmbedding hci).isEmbedding.toHomeomorph
  have hJ (p : A) : (J p : X) = c p := rfl
  have hJT (z : T) : c (J.symm z) = z :=
    congrArg Subtype.val (J.apply_symm_apply z)
  have hT : T = τ '' (bridgeCoordinates '' A) := by
    ext z
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨_,⟨p,p.property,rfl⟩,rfl⟩
    · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
      exact ⟨⟨p,hp⟩,rfl⟩
  let Y := B ∪ T
  let L : Set (I × Y) := {z | (z.2:X) ∈ B}
  let K : Set (I × Y) := {z | (z.2:X) ∈ T}
  let H : I × Y → X := fun z => if hz : (z.2:X) ∈ T then
    τ (bridgeBend z.1 (J.symm ⟨z.2,hz⟩)) else z.2
  have hHK (z : I × Y) (hz : z ∈ K) :
      H z = τ (bridgeBend z.1 (J.symm ⟨z.2,hz⟩)) := by
    exact dif_pos hz
  have hHL (z : I × Y) (hz : z ∈ L) : H z = z.2 := by
    dsimp only [H]
    split_ifs with ht
    · let p := J.symm ⟨z.2,ht⟩
      have hv := hJT ⟨z.2,ht⟩
      change τ (bridgeCoordinates p) = (z.2:X) at hv
      have hp := hBtop p p.property (hv.symm ▸ hz)
      change τ (bridgeBend z.1 p) = (z.2:X)
      rw [bridgeBend_eq_top_of_end _ _ hp]
      exact hv
    · rfl
  have hcK : ContinuousOn H K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hv : Continuous (fun z : K => τ (bridgeBend z.val.1
        (J.symm ⟨z.val.2,z.property⟩))) := by
      apply hτ.comp_continuous
      · exact bridgeBend_continuous.comp (show Continuous
          (fun z : K => ((z.val.1:ℝ),(J.symm ⟨z.val.2,z.property⟩:P2))) by fun_prop)
      · intro z
        exact bridgeBend_mapsTo z.val.1 (J.symm ⟨z.val.2,z.property⟩).property
    exact hv.congr (fun z => (hHK z z.property).symm)
  have hcL : ContinuousOn H L := by
    have hv : Continuous (fun z : I × Y => (z.2:X)) := by fun_prop
    exact hv.continuousOn.congr (fun z hz => hHL z hz)
  have hLK : L ∪ K = univ := by
    ext z
    simp only [mem_union,mem_univ,iff_true]
    exact z.2.property
  have hH : Continuous H := by
    have hh := hcL.union_of_isClosed hcK
      (hB.isClosed.preimage (by fun_prop)) (hTc.isClosed.preimage (by fun_prop))
    rw [hLK] at hh
    exact continuousOn_univ.mp hh
  have hval (t : I) (p : A) :
      H (t,⟨c p,Or.inr ⟨p,rfl⟩⟩) = τ (bridgeBend t p) := by
    rw [hHK _ (show c p ∈ T from ⟨p,rfl⟩)]
    have hp : (⟨c p,⟨p,rfl⟩⟩ : T) = J p := Subtype.ext rfl
    rw [hp,J.symm_apply_apply]
  have hzeroB (z : Y) (hz : H (⟨0,by norm_num⟩,z) ∈ B) :
      H (⟨0,by norm_num⟩,z) = z := by
    by_cases ht : (z:X) ∈ T
    · let p := J.symm ⟨z,ht⟩
      have hzv := hHK (⟨0,by norm_num⟩,z) ht
      rw [bridgeBend_zero] at hzv
      have hp := hBraw p p.property (hzv ▸ hz)
      rw [hHK _ ht,bridgeBend_eq_top_of_end _ _ hp]
      have hv := hJT ⟨z,ht⟩
      change τ (bridgeCoordinates p) = (z:X) at hv
      exact hv
    · exact hHL _ (z.property.resolve_right ht)
  have hHi : Function.Injective (fun z : Y => H (⟨0,by norm_num⟩,z)) := by
    intro z w hzw
    change H (⟨0,by norm_num⟩,z) = H (⟨0,by norm_num⟩,w) at hzw
    by_cases hz : (z:X) ∈ T
    · by_cases hw : (w:X) ∈ T
      · rw [hHK _ hz,hHK _ hw,bridgeBend_zero,bridgeBend_zero] at hzw
        have hp := joinedBridgeCoordinates_injective
          (hτi (joinedBridgeCoordinates_mapsTo (J.symm ⟨z,hz⟩).property)
            (joinedBridgeCoordinates_mapsTo (J.symm ⟨w,hw⟩).property) hzw)
        exact Subtype.ext (congrArg (fun x : T => (x:X))
          (J.symm.injective (Subtype.ext hp)))
      · have hwB : (w:X) ∈ B := w.property.resolve_right hw
        have hh : H (⟨0,by norm_num⟩,z) ∈ B := by rw [hzw,hHL _ hwB]; exact hwB
        exact Subtype.ext ((hzeroB z hh).symm.trans (hzw.trans (hHL _ hwB)))
    · have hzB : (z:X) ∈ B := z.property.resolve_right hz
      have hh : H (⟨0,by norm_num⟩,w) ∈ B := by rw [←hzw,hHL _ hzB]; exact hzB
      exact Subtype.ext ((hHL _ hzB).symm.trans (hzw.trans (hzeroB w hh)))
  have himage : Set.range (fun z : Y => H (⟨0,by norm_num⟩,z)) =
      B ∪ τ '' (joinedBridgeCoordinates '' A) := by
    apply Subset.antisymm
    · rintro _ ⟨z,rfl⟩
      change H (⟨0,by norm_num⟩,z) ∈ _
      by_cases ht : (z:X) ∈ T
      · rw [hHK _ ht,bridgeBend_zero]
        exact Or.inr ⟨_,⟨_,(J.symm ⟨z,ht⟩).property,rfl⟩,rfl⟩
      · rw [hHL _ (z.property.resolve_right ht)]
        exact Or.inl (z.property.resolve_right ht)
    · rintro z (hz | ⟨_,⟨p,hp,rfl⟩,rfl⟩)
      · exact ⟨⟨z,Or.inl hz⟩,hHL _ hz⟩
      · exact ⟨⟨c ⟨p,hp⟩,Or.inr ⟨⟨p,hp⟩,rfl⟩⟩,
          (hval ⟨0,by norm_num⟩ ⟨p,hp⟩).trans (congrArg τ (bridgeBend_zero p))⟩
  have hout : ∃ G : C(I × Y,X),
      (∀ z : Y,G (⟨1,by norm_num⟩,z) = z) ∧
      (∀ z,G z ∈ R) ∧
      (∀ z,G z ∈ frontier R ↔ (z.2:X) ∈ frontier R) ∧
      (∀ z,(z.2:X) ∈ B → G z = z.2) ∧
      (∀ t : I,∀ p : A,G (t,⟨c p,Or.inr ⟨p,rfl⟩⟩) = τ (bridgeBend t p)) ∧
      Function.Injective (fun z : Y => G (⟨0,by norm_num⟩,z)) ∧
      Set.range (fun z : Y => G (⟨0,by norm_num⟩,z)) = B ∪ τ '' (joinedBridgeCoordinates '' A) := by
    refine ⟨⟨H,hH⟩,?_,?_,?_,hHL,hval,hHi,himage⟩
    · intro z
      change H (⟨1,by norm_num⟩,z) = (z:X)
      by_cases hz : (z:X) ∈ T
      · rw [hHK _ hz,bridgeBend_one]
        exact hJT ⟨z,hz⟩
      · exact hHL _ (z.property.resolve_right hz)
    · intro z
      change H z ∈ R
      by_cases hz : (z.2:X) ∈ T
      · rw [hHK _ hz]
        exact hR (bridgeBend_mapsTo z.1 (J.symm ⟨z.2,hz⟩).property)
      · rw [hHL _ (z.2.property.resolve_right hz)]
        exact hBR (z.2.property.resolve_right hz)
    · intro z
      change H z ∈ frontier R ↔ (z.2:X) ∈ frontier R
      by_cases hz : (z.2:X) ∈ T
      · rw [hHK _ hz,hfront _ (bridgeBend_mapsTo z.1 (J.symm ⟨z.2,hz⟩).property)]
        exact (hfront _ (bridgeCoordinates_mapsTo (J.symm ⟨z.2,hz⟩).property)).symm.trans
          (Iff.of_eq (congrArg (fun x : X => x ∈ frontier R) (hJT ⟨z.2,hz⟩)))
      · rw [hHL _ (z.2.property.resolve_right hz)]
  obtain ⟨G,hG1,hGR,hGfront,hGB,hGval,hGi,hGimage⟩ := hout
  let Y' := B ∪ τ '' (bridgeCoordinates '' halfSource false)
  have hYY : Y' = Y := congrArg (B ∪ ·) hT.symm
  let L : Y' ≃ₜ Y := Homeomorph.setCongr hYY
  let F : C(I × Y',X) := G.comp ⟨fun z => (z.1,L z.2),by fun_prop⟩
  refine ⟨F,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z
    exact hG1 (L z)
  · intro z
    exact hGR (z.1,L z.2)
  · intro z
    exact hGfront (z.1,L z.2)
  · intro z hz
    exact hGB (z.1,L z.2) hz
  · intro t p
    exact hGval t p
  · intro z w hzw
    exact L.injective (hGi hzw)
  · change Set.range ((fun z : Y => G (⟨0,by norm_num⟩,z)) ∘ L) = _
    rw [Set.range_comp,L.surjective.range_eq,Set.image_univ]
    exact hGimage

theorem exists_physical_cup_bend
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {τ : C3 → X} (hτ : ContinuousOn τ tube) (hτi : InjOn τ tube)
    {B R : Set X} (hB : IsCompact B) (hBR : B ⊆ R) (hR : MapsTo τ tube R)
    (hfront : ∀ z ∈ tube,τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (hBtop : ∀ p ∈ halfSource false,τ (bridgeCoordinates p) ∈ B ↔ p.2 = 0)
    (hBraw : ∀ p ∈ halfSource false,τ (joinedBridgeCoordinates p) ∈ B ↔ p.2 = 0) :
    let Y := B ∪ τ '' (bridgeCoordinates '' halfSource false)
    ∃ H : C(I × ↥Y,X),
      (∀ z : Y,H (⟨1,by norm_num⟩,z) = z) ∧
      (∀ z,H z ∈ R) ∧
      (∀ z,H z ∈ frontier R ↔ (z.2:X) ∈ frontier R) ∧
      (∀ z,(z.2:X) ∈ B → H z = z.2) ∧
      (∀ t : I,∀ p : halfSource false,
        H (t,⟨τ (bridgeCoordinates p),Or.inr ⟨_,⟨p,p.property,rfl⟩,rfl⟩⟩) =
          τ (bridgeBend t p)) ∧
      Function.Injective (fun z : Y => H (⟨0,by norm_num⟩,z)) ∧
      Set.range (fun z : Y => H (⟨0,by norm_num⟩,z)) =
        B ∪ τ '' (joinedBridgeCoordinates '' halfSource false) :=
  exists_physical_cup_bend_of_end_contacts hτ hτi hB hBR hR hfront
    (fun p hp hb => Or.inl ((hBtop p hp).mp hb))
    (fun p hp hb => Or.inl ((hBraw p hp).mp hb))

theorem exists_original_returning_cup_branch_homotopy
    {X E F : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace E] [TopologicalSpace F]
    {c₀ : P2 → E} {c₁ : P2 → F} {f₀ : E → X} {f₁ : F → X}
    {A C S₀ : Set E} {B D S₁ : Set F} {τ : C3 → X} {R : Set X}
    (hc₀ : MapsTo c₀ source S₀) (hci₀ : InjOn c₀ source)
    (hc₁ : MapsTo c₁ source S₁) (hci₁ : InjOn c₁ source)
    (hAS : A ⊆ S₀) (hBS : B ⊆ S₁)
    (hCeq : C = A \ ((c₀ '' halfSource false) \ c₀ '' arm (-1)))
    (hhalf : c₀ '' halfSource false ⊆ A)
    (htrim : B ∩ (c₁ '' halfSource true) = c₁ '' arm 1)
    (hcover : (c₁ '' halfSource true) ∪ B = D)
    (hCcompact : IsCompact C) (hBcompact : IsCompact B)
    (hf₀ : ContinuousOn f₀ C) (hf₁ : ContinuousOn f₁ B)
    (hfi₀ : InjOn f₀ S₀) (hfi₁ : InjOn f₁ S₁)
    (hCR : MapsTo f₀ C R) (hBR : MapsTo f₁ B R)
    (hτ : ContinuousOn τ tube) (hτi : InjOn τ tube) (hτR : MapsTo τ tube R)
    (hτfront : ∀ z ∈ tube,τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (hA : ∀ z ∈ tube,τ z ∈ f₁ '' S₁ ↔ z.1.2 = z.1.1)
    (hT : ∀ z ∈ tube,τ z ∈ f₀ '' S₀ ↔ z.1.2 = -z.1.1)
    (hBT : Disjoint (f₁ '' B) (f₀ '' S₀))
    (hperiod₀ : ∀ p ∈ source,f₀ (c₀ p) = τ ((p.2,-p.2),p.1))
    (hperiod₁ : ∀ p ∈ source,f₁ (c₁ p) = τ ((p.2,p.2),p.1)) :
    let Y := (f₁ '' B ∪ f₀ '' C) ∪ τ '' (bridgeCoordinates '' halfSource false)
    ∃ H : C(I × ↥Y,X),
      (∀ z : Y,H (⟨1,by norm_num⟩,z) = z) ∧
      (∀ z,H z ∈ R) ∧
      (∀ z,H z ∈ frontier R ↔ (z.2:X) ∈ frontier R) ∧
      (∀ z,(z.2:X) ∈ f₁ '' B ∪ f₀ '' C → H z = z.2) ∧
      Function.Injective (fun z : Y => H (⟨0,by norm_num⟩,z)) ∧
      Set.range (fun z : Y => H (⟨0,by norm_num⟩,z)) = f₀ '' A ∪ f₁ '' D := by
  have hfar : c₀ '' arm (-1) ⊆ c₀ '' halfSource false := by
    apply image_mono
    intro p hp
    exact ⟨hp.1,by rw [show p.2 = -1 from hp.2]; norm_num⟩
  have hcontact : C ∩ (c₀ '' halfSource false) = c₀ '' arm (-1) := by
    rw [hCeq]
    ext x
    constructor
    · intro hx
      exact Classical.byContradiction (fun hn => hx.1.2 ⟨hx.2,hn⟩)
    · intro hx
      exact ⟨⟨hhalf (hfar hx),fun hh => hh.2 hx⟩,hfar hx⟩
  have hCS : C ⊆ S₀ := by rw [hCeq]; exact sdiff_subset.trans hAS
  have hkept : C ∪ (c₀ '' halfSource false) = A := by
    rw [hCeq]
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hhalf hx
    · intro hx
      by_cases hh : x ∈ c₀ '' halfSource false
      · exact Or.inr hh
      · exact Or.inl ⟨hx,fun hn => hh hn.1⟩
  obtain ⟨hBtop,hBraw⟩ := trimmed_disk_bridge_contacts hc₁ hci₁ hBS hfi₁
    htrim hperiod₁ hBT hA hT
  obtain ⟨hCtop,hCraw⟩ := retained_core_bridge_contacts hc₀ hci₀ hCS hfi₀
    hcontact hperiod₀ hT
  have htop (p : P2) (hp : p ∈ halfSource false)
      (hz : τ (bridgeCoordinates p) ∈ f₁ '' B ∪ f₀ '' C) : p.2 = 0 ∨ p.2 = -1 := by
    rcases hz with hz | hz
    · exact Or.inl ((hBtop p hp).mp hz)
    · exact Or.inr ((hCtop p hp).mp hz)
  have hraw (p : P2) (hp : p ∈ halfSource false)
      (hz : τ (joinedBridgeCoordinates p) ∈ f₁ '' B ∪ f₀ '' C) : p.2 = 0 ∨ p.2 = -1 := by
    rcases hz with hz | hz
    · exact Or.inl ((hBraw p hp).mp hz)
    · exact Or.inr ((hCraw p hp).mp hz)
  obtain ⟨H,hH1,hHR,hHfront,hHfix,_,hHi,hHimage⟩ :=
    exists_physical_cup_bend_of_end_contacts hτ hτi
      ((hBcompact.image_of_continuousOn hf₁).union (hCcompact.image_of_continuousOn hf₀))
      (union_subset hBR.image_subset hCR.image_subset) hτR hτfront htop hraw
  refine ⟨H,hH1,hHR,hHfront,hHfix,hHi,?_⟩
  rw [hHimage,joined_bridge_image_of_source_strips hperiod₀ hperiod₁,
    ←hkept,←hcover,image_union,image_union]
  ext z
  simp only [mem_union]
  tauto

end PoincareConjecture.M76.Dehn.Annuli.BoundaryCup
