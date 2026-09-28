import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RetainedCollarReattachment









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_retained_collar_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K B B₀ : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hK : IsClosed K) (hKR : K ⊆ R) (hfrontK : frontier K = B₀ ∪ B)
    (s : ChartwisePLSphere e B) (F : V3 × ℝ → X)
    (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I)) (hFK : F '' (Sphere ×ˢ I) = K)
    (htop : ∀ z ∈ Sphere, F (z, 1) = s.map z)
    (hbottom : F '' (Sphere ×ˢ {(0 : ℝ)}) = B₀)
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hband : P.map '' (Rim ×ˢ J) ⊆ B)
    {k q : Set V3} (hk : IsFinitePLBallPair P2 k q) (hkS : k ⊆ Sphere)
    (hcontact : (s.map '' k) ∩ (P.map '' (Rim ×ˢ J)) = s.map '' q)
    (b : Bool) (hrim : s.map '' q = P.capRimSet b) :
    ∃ H : (k × unitInterval) ≃ₜ (F '' (k ×ˢ I)),
      (∀ z : k × unitInterval, (H z : X) = F ((z.1 : V3), (z.2 : ℝ))) ∧
      (∀ z : k × unitInterval, (H z : X) ∈ P.cutCarrier ↔ z.2 = 0 ∨ z.2 = 1) ∧
      (∀ (d : Bool) (z : k × unitInterval),
        (H z : X) ∈ F '' (k ×ˢ {if d then (1 : ℝ) else 0}) ↔
          z.2 = if d then 1 else 0) ∧
      P.cutCarrier ∩ (F '' (k ×ˢ I)) =
        (F '' (k ×ˢ {(0 : ℝ)})) ∪ (F '' (k ×ˢ {(1 : ℝ)})) := by
  classical
  have hsub : k ×ˢ I ⊆ Sphere ×ˢ I := prod_mono hkS subset_rfl
  let : CompactSpace (k ×ˢ I : Set (V3 × ℝ)) :=
    isCompact_iff_compactSpace.mp (hk.isCompact.prod isCompact_Icc)
  let G : (k ×ˢ I : Set (V3 × ℝ)) ≃ₜ (F '' (k ×ˢ I)) :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn F (k ×ˢ I) (hFi.mono hsub))
      ((hF.continuousOn.mono hsub).domRestrict.subtype_mk _)
  let H : (k × unitInterval) ≃ₜ (F '' (k ×ˢ I)) :=
    (Homeomorph.Set.prod k I).symm.trans G
  have hval (z : k × unitInterval) : (H z : X) = F ((z.1 : V3), (z.2 : ℝ)) := rfl
  have htopimage : F '' (Sphere ×ˢ {(1 : ℝ)}) = B := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      have ht1 : t = 1 := ht
      subst t
      rw [htop z hz,s.map_eq ⟨z,hz⟩]
      exact (s.parametrization ⟨z,hz⟩).property
    · intro x hx
      let z := s.parametrization.symm ⟨x,hx⟩
      exact ⟨(z,1),⟨z.property,rfl⟩,(htop z z.property).trans
        ((s.map_eq z).trans (congrArg Subtype.val (s.parametrization.apply_symm_apply _)))⟩
  have hfrontF : frontier K = F '' (Sphere ×ˢ ({0,1} : Set ℝ)) := by
    rw [show ({0,1} : Set ℝ) = {0} ∪ {1} by rfl,prod_union,image_union,hbottom,htopimage]
    exact hfrontK
  obtain ⟨_, _, havoid, _, _⟩ := P.retained_collar_reattachment_geometry
    s F hF hFi hFK htop hstripK hband hk hkS hcontact b hrim
  have hboundary (z : k × unitInterval) : (H z : X) ∈ frontier K ↔
      z.2 = 0 ∨ z.2 = 1 := by
    rw [hfrontF,hval]
    constructor
    · rintro ⟨w,hw,heq⟩
      have hwfull : w ∈ Sphere ×ˢ I := by
        refine ⟨hw.1, ?_⟩
        rcases hw.2 with h0 | h1
        · rw [h0]; norm_num
        · rw [show w.2 = 1 from h1]; norm_num
      have heq' := hFi hwfull ⟨hkS z.1.property,z.2.property⟩ heq
      have hzmem : (z.2 : ℝ) ∈ ({0,1} : Set ℝ) := by
        have hweq : w.2 = (z.2 : ℝ) := congrArg Prod.snd heq'
        simpa only [hweq] using hw.2
      rcases hzmem with h0 | h1
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr (Subtype.ext h1)
    · intro hz
      refine ⟨((z.1 : V3),(z.2 : ℝ)),⟨hkS z.1.property,?_⟩,rfl⟩
      rcases hz with hz | hz <;> rw [hz] <;> norm_num
  have hattach (z : k × unitInterval) : (H z : X) ∈ P.cutCarrier ↔
      z.2 = 0 ∨ z.2 = 1 := by
    have hzK : (H z : X) ∈ K := hFK.subset ⟨_,⟨hkS z.1.property,z.2.property⟩,rfl⟩
    have hzavoid : (H z : X) ∉ P.openStrip :=
      fun h => disjoint_left.mp havoid (H z).property h
    rw [← hboundary z,hK.frontier_eq]
    change (((H z : X) ∈ R ∧ (H z : X) ∉ interior K) ∧
      (H z : X) ∉ P.openStrip) ↔ (H z : X) ∈ K ∧ (H z : X) ∉ interior K
    exact ⟨fun h => ⟨hzK,h.1.2⟩, fun h => ⟨⟨hKR hzK,h.2⟩,hzavoid⟩⟩
  have hends (d : Bool) (z : k × unitInterval) :
      (H z : X) ∈ F '' (k ×ˢ {if d then (1 : ℝ) else 0}) ↔
        z.2 = if d then 1 else 0 := by
    rw [hval]
    constructor
    · rintro ⟨w,hw,heq⟩
      have hwfull : w ∈ Sphere ×ˢ I := by
        refine ⟨hkS hw.1, ?_⟩
        rw [show w.2 = (if d then (1 : ℝ) else 0) from hw.2]
        cases d <;> norm_num
      have heq' := hFi hwfull ⟨hkS z.1.property,z.2.property⟩ heq
      apply Subtype.ext
      have hh : (z.2 : ℝ) = (if d then (1 : ℝ) else 0) :=
        (congrArg Prod.snd heq').symm.trans (show w.2 = _ from hw.2)
      cases d <;> simpa using hh
    · intro hz
      refine ⟨((z.1 : V3),(z.2 : ℝ)),⟨z.1.property,?_⟩,rfl⟩
      cases d <;> simpa using congrArg Subtype.val hz
  refine ⟨H,hval,hattach,hends,?_⟩
  apply Subset.antisymm
  · intro x hx
    let z := H.symm ⟨x,hx.2⟩
    have hzval : (H z : X) = x := congrArg Subtype.val (H.apply_symm_apply _)
    rcases (hattach z).mp (hzval.symm ▸ hx.1) with hz | hz
    · exact Or.inl (hzval ▸ (hends false z).mpr hz)
    · exact Or.inr (hzval ▸ (hends true z).mpr hz)
  · rintro x (hx | hx)
    · have hxH : x ∈ F '' (k ×ˢ I) := image_mono
        (prod_mono subset_rfl (by intro t ht; rw [show t=0 from ht]; norm_num)) hx
      let z := H.symm ⟨x,hxH⟩
      have hzval : (H z : X) = x := congrArg Subtype.val (H.apply_symm_apply _)
      exact ⟨hzval ▸ (hattach z).mpr (Or.inl ((hends false z).mp (hzval.symm ▸ hx))),hxH⟩
    · have hxH : x ∈ F '' (k ×ˢ I) := image_mono
        (prod_mono subset_rfl (by intro t ht; rw [show t=1 from ht]; norm_num)) hx
      let z := H.symm ⟨x,hxH⟩
      have hzval : (H z : X) = x := congrArg Subtype.val (H.apply_symm_apply _)
      exact ⟨hzval ▸ (hattach z).mpr (Or.inr ((hends true z).mp (hzval.symm ▸ hx))),hxH⟩

end PoincareConjecture.M76.OriginalDiskProduct
