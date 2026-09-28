import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.RawCrossingRegularity
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedSourceGerms
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OriginalTargetGerms

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem RetainedSourceOpenHomeomorph.transport_branch
    {X : Type*} [TopologicalSpace X] {f g : V2 → X} {K : Set V2} {j : K → V2}
    (H : RetainedSourceOpenHomeomorph f g K j)
    (facts : RetainedSquareMapFacts f g K j)
    (A : Set V2) (hA : IsOpen ((Subtype.val : D2 → V2) ⁻¹' A))
    (he : IsEmbedding (fun x : A ↦ f x)) :
    let B := (fun x : H.source ↦ (H.homeomorph x : V2)) '' (Subtype.val ⁻¹' A)
    B ⊆ D2 ∧ IsOpen ((Subtype.val : D2 → V2) ⁻¹' B) ∧
      IsEmbedding (fun x : B ↦ g x) ∧ g '' B = f '' (H.source ∩ A) := by
  let h : H.source → V2 := fun x ↦ H.homeomorph x
  let U : Set H.source := Subtype.val ⁻¹' A
  have hHD : H.source ⊆ D2 := H.source_subset.trans facts.old_subset
  have hU : IsOpen U := hA.preimage
    (continuous_subtype_val.subtype_mk (fun x ↦ hHD x.property))
  have hh : IsEmbedding h := IsEmbedding.subtypeVal.comp H.homeomorph.isEmbedding
  let E := hh.homeomorphImage U
  have hE (x : U) : (E x : V2) = h x.val := rfl
  have hinc : IsEmbedding (fun x : U ↦ (⟨x.val, x.property⟩ : A)) :=
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _ _
  have he' : IsEmbedding (fun x : U ↦ f x.val) := he.comp hinc
  have hnew : IsEmbedding (fun x : h '' U ↦ g x) := by
    have hem := he'.comp E.symm.isEmbedding
    have heq : (fun x : h '' U ↦ f (E.symm x).val) = (fun x : h '' U ↦ g x) := by
      funext x
      have hk := H.keep (E.symm x).val
      change g (h (E.symm x).val) = _ at hk
      rw [← hE, E.apply_symm_apply] at hk
      exact hk.symm
    exact heq ▸ hem
  refine ⟨?_, ?_, hnew, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact H.target_subset (H.homeomorph x).property
  · let q : H.source → D2 := fun x ↦
      ⟨H.homeomorph x, H.target_subset (H.homeomorph x).property⟩
    have hq : IsOpenMap q :=
      (IsOpenEmbedding.inclusion H.target_subset H.target_open).isOpenMap.comp
        H.homeomorph.isOpenMap
    have heq : (Subtype.val : D2 → V2) ⁻¹' (h '' U) = q '' U := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    change IsOpen ((Subtype.val : D2 → V2) ⁻¹' (h '' U))
    rw [heq]
    exact hq _ hU
  · ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, ⟨x.property, hx⟩, (H.keep x).symm⟩
    · rintro ⟨x, ⟨hxS, hxA⟩, rfl⟩
      exact ⟨H.homeomorph ⟨x, hxS⟩, ⟨⟨x, hxS⟩, hxA, rfl⟩, H.keep ⟨x, hxS⟩⟩

theorem isCompact_square_sdiff_of_relative_open {U : Set V2}
    (hU : IsOpen ((Subtype.val : D2 → V2) ⁻¹' U)) : IsCompact (D2 \ U) := by
  have : CompactSpace D2 := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have heq : (Subtype.val : D2 → V2) '' ((Subtype.val : D2 → V2) ⁻¹' U)ᶜ = D2 \ U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hn⟩
      exact ⟨⟨x, hx⟩, hn, rfl⟩
  rw [← heq]
  exact hU.isClosed_compl.isCompact.image continuous_subtype_val

theorem RetainedSourceOpenHomeomorph.transport_crossing
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f g : V2 → X} {K : Set V2}
    {region : Set X} {j : K → V2}
    (H : RetainedSourceOpenHomeomorph f g K j)
    (facts : RetainedSquareMapFacts f g K j)
    (hf : ContinuousOn f D2) (hg : ContinuousOn g D2)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2))
    (a b : K) (hab : f a = f b) (hne : (a : V2) ≠ b)
    (C : RawCrossingChart e f region a b)
    (W0 : Set X) (hW0 : IsOpen W0) (haW0 : f a ∈ W0) :
    ∃ C' : RawCrossingChart e g region (j a) (j b),
      (C'.chart : X → V3) = C.chart ∧ C'.chart.source ⊆ C.chart.source ∧
        C'.chart.source ⊆ W0 := by
  have hja : j a ∈ D2 := facts.mapsTo a
  have hjb : j b ∈ D2 := facts.mapsTo b
  have hjab : g (j a) = g (j b) := (facts.keep a).trans (hab.trans (facts.keep b).symm)
  have hjne : j a ≠ j b := fun h ↦ hne (congrArg Subtype.val (facts.injective h))
  have haD : (a : V2) ∈ doubleLocusOn f D2 :=
    ⟨facts.old_subset a.property, b, facts.old_subset b.property, hab, hne⟩
  have hbD : (b : V2) ∈ doubleLocusOn f D2 :=
    ⟨facts.old_subset b.property, a, facts.old_subset a.property, hab.symm, hne.symm⟩
  have haS := H.contains a haD
  have hbS := H.contains b hbD
  have hfa : f a ∉ f '' (D2 \ H.source) := by
    rintro ⟨z, ⟨hz, hn⟩, hzval⟩
    have hzK := facts.old_fiber_subset partner hunique hja hjb hjab hjne
      (show z ∈ D2 ∩ f ⁻¹' {g (j a)} from ⟨hz, hzval.trans (facts.keep a).symm⟩)
    have hzD : z ∈ doubleLocusOn f D2 := by
      by_cases hza : z = (a : V2)
      · exact hza ▸ haD
      · exact ⟨hz, a, facts.old_subset a.property, hzval, hza⟩
    exact hn (H.contains ⟨z, hzK⟩ hzD)
  have hga : f a ∉ g '' (D2 \ H.target) := by
    rintro ⟨z, ⟨hz, hn⟩, hzval⟩
    have hzD : z ∈ doubleLocusOn g D2 := by
      by_cases hza : z = j a
      · exact hza ▸ ⟨hja, j b, hjb, hjab, hjne⟩
      · exact ⟨hz, j a, hja, hzval.trans (facts.keep a).symm, hza⟩
    exact hn (H.contains_new_double facts hzD)
  have hclosedF : IsClosed (f '' (D2 \ H.source)) :=
    ((isCompact_square_sdiff_of_relative_open H.source_open).image_of_continuousOn
      (hf.mono sdiff_subset)).isClosed
  have hclosedG : IsClosed (g '' (D2 \ H.target)) :=
    ((isCompact_square_sdiff_of_relative_open H.target_open).image_of_continuousOn
      (hg.mono sdiff_subset)).isClosed
  let W := W0 ∩ (f '' (D2 \ H.source) ∪ g '' (D2 \ H.target))ᶜ
  have hW : IsOpen W := hW0.inter (hclosedF.union hclosedG).isOpen_compl
  have haW : f a ∈ W := ⟨haW0, fun h ↦ h.elim hfa hga⟩
  have hcutF (z : V2) (hz : z ∈ D2) (hzW : f z ∈ W) : z ∈ H.source := by
    by_contra hn
    exact hzW.2 (Or.inl ⟨z, ⟨hz, hn⟩, rfl⟩)
  have hcutG (z : V2) (hz : z ∈ D2) (hzW : g z ∈ W) : z ∈ H.target := by
    by_contra hn
    exact hzW.2 (Or.inr ⟨z, ⟨hz, hn⟩, rfl⟩)
  let A := C.left ∩ f ⁻¹' W
  let B := C.right ∩ f ⁻¹' W
  let L := (fun z : H.source ↦ (H.homeomorph z : V2)) '' (Subtype.val ⁻¹' A)
  let U := (fun z : H.source ↦ (H.homeomorph z : V2)) '' (Subtype.val ⁻¹' B)
  have hfD : Continuous (fun z : D2 ↦ f z) := continuousOn_iff_continuous_domRestrict.mp hf
  have hA : IsOpen ((Subtype.val : D2 → V2) ⁻¹' A) :=
    C.left_open.inter (hW.preimage hfD)
  have hB : IsOpen ((Subtype.val : D2 → V2) ⁻¹' B) :=
    C.right_open.inter (hW.preimage hfD)
  obtain ⟨hLD, hLo, hLe, hLim⟩ := H.transport_branch facts A hA
    (C.left_embedding.comp (IsEmbedding.inclusion inter_subset_left))
  obtain ⟨hUD, hUo, hUe, hUim⟩ := H.transport_branch facts B hB
    (C.right_embedding.comp (IsEmbedding.inclusion inter_subset_left))
  have hmem (z : K) (hzS : (z : V2) ∈ H.source) (hzW : f z ∈ W)
      {B0 : Set V2} (hzB : (z : V2) ∈ B0) :
      j z ∈ (fun z : H.source ↦ (H.homeomorph z : V2)) ''
        (Subtype.val ⁻¹' (B0 ∩ f ⁻¹' W)) :=
    ⟨⟨z, hzS⟩, ⟨hzB, hzW⟩, H.value ⟨z, hzS⟩⟩
  have himage (B0 : Set V2) (hB0 : B0 ⊆ D2) (z : X) (hz : z ∈ W) :
      z ∈ f '' (H.source ∩ (B0 ∩ f ⁻¹' W)) ↔ z ∈ f '' B0 := by
    constructor
    · rintro ⟨u, ⟨_, hu, _⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, ⟨hcutF u (hB0 hu) hz, hu, hz⟩, rfl⟩
  let T := C.chart.restrOpen W hW
  refine ⟨⟨T, L, U, hLD, hUD, hLo, hUo, ?_, ?_, ?_, hLe, hUe,
    ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ h ↦ h.1, fun _ h ↦ h.2.1⟩
  · apply disjoint_left.mpr
    rintro z ⟨u, hu, huval⟩ ⟨v, hv, hvval⟩
    have huv : u = v := H.homeomorph.injective (Subtype.ext (huval.trans hvval.symm))
    exact disjoint_left.mp C.disjoint hu.1 (huv.symm ▸ hv.1)
  · rcases C.labels with ⟨haL, hbU⟩ | ⟨haU, hbL⟩
    · exact Or.inl ⟨hmem a haS haW haL, hmem b hbS (hab ▸ haW) hbU⟩
    · exact Or.inr ⟨hmem a haS haW haU, hmem b hbS (hab ▸ haW) hbL⟩
  · exact (facts.keep a).symm ▸ ⟨C.point, haW⟩
  · ext z
    constructor
    · rintro ⟨hzD, hzT, hzW⟩
      let u : H.source := H.homeomorph.symm ⟨z, hcutG z hzD hzW⟩
      have huval : (H.homeomorph u : V2) = z := congrArg Subtype.val
        (H.homeomorph.apply_symm_apply ⟨z, hcutG z hzD hzW⟩)
      have huf : f u = g z := (H.keep u).symm.trans (congrArg g huval)
      have huT : f u ∈ C.chart.source := huf.symm ▸ hzT
      have huW : f u ∈ W := huf.symm ▸ hzW
      rcases C.whole_preimage.subset
          ⟨facts.old_subset (H.source_subset u.property), huT⟩ with huL | huU
      · exact Or.inl ⟨u, ⟨huL, huW⟩, huval⟩
      · exact Or.inr ⟨u, ⟨huU, huW⟩, huval⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · have huT := (C.whole_preimage.symm.subset (Or.inl hu.1)).2
        have hgt : g (H.homeomorph u) ∈ T.source :=
          (H.keep u).symm ▸ (show f u ∈ T.source from ⟨huT, hu.2⟩)
        exact ⟨H.target_subset (H.homeomorph u).property, hgt⟩
      · have huT := (C.whole_preimage.symm.subset (Or.inr hu.1)).2
        have hgt : g (H.homeomorph u) ∈ T.source :=
          (H.keep u).symm ▸ (show f u ∈ T.source from ⟨huT, hu.2⟩)
        exact ⟨H.target_subset (H.homeomorph u).property, hgt⟩
  · intro k
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (C.compatible k)).mono
      ((e k).symm.trans T).open_source (fun _ hz ↦ ⟨hz.1, hz.2.1⟩)
  · intro z hz
    rw [hLim, himage C.left C.left_subset z hz.2]
    exact C.left_image z hz.1
  · intro z hz
    rw [hUim, himage C.right C.right_subset z hz.2]
    exact C.right_image z hz.1
  · rcases C.region with hi | ⟨hr, hf'⟩
    · exact Or.inl (fun _ hz ↦ hi hz.1)
    · exact Or.inr ⟨fun z hz ↦ hr z hz.1, fun z hz ↦ hf' z hz.1⟩

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem OriginalNormalizedResolutionPairData.exists_raw_crossing_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    {f : V2 → X} {Z region : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
    {c : Bool → P2 → V2} {τ : C3 → X}
    {D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)}
    (P : OriginalNormalizedResolutionPairData e D)
    (hf : ContinuousOn f D2) (hτc : ContinuousOn τ tube)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2))
    (hold : ∀ x ∈ D2, ∀ y ∈ D2, x ≠ y → f x = f y →
      Nonempty (RawCrossingChart e f region x y)) :
    (∀ x ∈ D2, ∀ y ∈ D2, x ≠ y → P.gU x = P.gU y →
      ∃ C : RawCrossingChart e P.gU region x y,
        P.gU '' D2 ∩ C.chart.source = f '' D2 ∩ C.chart.source) ∧
    (∀ x ∈ D2, ∀ y ∈ D2, x ≠ y → P.gV x = P.gV y →
      ∃ C : RawCrossingChart e P.gV region x y,
        P.gV '' D2 ∩ C.chart.source = f '' D2 ∩ C.chart.source) := by
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  obtain ⟨⟨HU⟩, ⟨HV⟩⟩ := P.nonempty_retained_source_germs
    hcPL hci hcS hdisj hτ hfull h0 h1 hfZ
  obtain ⟨hWU, hWV⟩ := P.exists_double_target_germs hf hτc hci hcS hdisj hτ hfull
    h0 h1 hfZ partner hunique
  have transport (g : V2 → X) (K : Set V2) (j : K → V2)
      (facts : RetainedSquareMapFacts f g K j)
      (H : RetainedSourceOpenHomeomorph f g K j) (hg : ContinuousOn g D2)
      (hW : ∀ x ∈ D2, ∀ y ∈ D2, g x = g y → x ≠ y →
        ∃ W : Set X, IsOpen W ∧ g x ∈ W ∧ g '' D2 ∩ W = f '' D2 ∩ W) :
      ∀ x ∈ D2, ∀ y ∈ D2, x ≠ y → g x = g y →
        ∃ C : RawCrossingChart e g region x y,
          g '' D2 ∩ C.chart.source = f '' D2 ∩ C.chart.source := by
    intro x hx y hy hne hxy
    have hrel : (x, y) ∈
        {v : V2 × V2 | v.1 ∈ D2 ∧ v.2 ∈ D2 ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} :=
      ⟨hx, hy, hxy, hne⟩
    rw [facts.double_relation] at hrel
    obtain ⟨⟨a, b⟩, ⟨hab, hneab⟩, hjab⟩ := hrel
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hjab
    obtain ⟨C⟩ := hold a (facts.old_subset a.property) b
      (facts.old_subset b.property) hneab hab
    obtain ⟨W, hWo, haW, hWimage⟩ := hW _ hx _ hy hxy hne
    obtain ⟨C', _, _, hCW⟩ := H.transport_crossing facts hf hg partner hunique
      a b hab hneab C W hWo ((facts.keep a) ▸ haW)
    refine ⟨C', ?_⟩
    calc
      g '' D2 ∩ C'.chart.source = (g '' D2 ∩ W) ∩ C'.chart.source := by
        rw [inter_assoc, inter_eq_right.mpr hCW]
      _ = (f '' D2 ∩ W) ∩ C'.chart.source := by rw [hWimage]
      _ = f '' D2 ∩ C'.chart.source := by rw [inter_assoc, inter_eq_right.mpr hCW]
  exact ⟨transport P.gU _ P.retainedUpperCopy factsU HU P.plU.continuousOn hWU,
    transport P.gV _ P.retainedAlternateCopy factsV HV P.plV.continuousOn hWV⟩

theorem RetainedSourceOpenHomeomorph.exists_raw_crossings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f g : V2 → X} {K : Set V2}
    {region : Set X} {j : K → V2}
    (H : RetainedSourceOpenHomeomorph f g K j)
    (facts : RetainedSquareMapFacts f g K j)
    (hf : ContinuousOn f D2) (hg : ContinuousOn g D2)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2))
    (hold : ∀ x ∈ D2, ∀ y ∈ D2, x ≠ y → f x = f y →
      Nonempty (RawCrossingChart e f region x y)) :
    ∀ x ∈ D2, ∀ y ∈ D2, x ≠ y → g x = g y →
      Nonempty (RawCrossingChart e g region x y) := by
  intro x hx y hy hne hxy
  have hrel : (x, y) ∈
      {v : V2 × V2 | v.1 ∈ D2 ∧ v.2 ∈ D2 ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} :=
    ⟨hx, hy, hxy, hne⟩
  rw [facts.double_relation] at hrel
  obtain ⟨⟨a, b⟩, ⟨hab, hneab⟩, hjab⟩ := hrel
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hjab
  obtain ⟨C⟩ := hold a (facts.old_subset a.property) b
    (facts.old_subset b.property) hneab hab
  obtain ⟨C', _⟩ := H.transport_crossing facts hf hg partner hunique
    a b hab hneab C univ isOpen_univ (mem_univ _)
  exact ⟨C'⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
