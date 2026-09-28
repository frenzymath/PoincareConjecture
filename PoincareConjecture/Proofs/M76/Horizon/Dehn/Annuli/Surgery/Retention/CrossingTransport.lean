import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.RawChart
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.TargetNeighborhood

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem RawSourceCrossing.transport_retained
    {E Y X ι : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {g : Y → X}
    {S U : Set E} {T V : Set Y} {R : Set X}
    (hS : IsCompact S) (hT : IsCompact T) (hUS : U ⊆ S) (hVT : V ⊆ T)
    (hU : IsOpen ((Subtype.val : S → E) ⁻¹' U))
    (hV : IsOpen ((Subtype.val : T → Y) ⁻¹' V))
    (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (H : U ≃ₜ V) (hkeep : ∀ x : U, g (H x) = f x)
    (p : doubleLocusOn f S → doubleLocusOn f S)
    (hunique : ∀ (x : doubleLocusOn f S) (y : E), y ∈ S →
      f x = f y → (x : E) ≠ y → y = (p x : E))
    (hcontains : doubleLocusOn g T ⊆ V)
    (a b : U) (hab : f a = f b) (hne : (a : E) ≠ b)
    (C : RawSourceCrossing e f S R a b)
    (W0 : Set X) (hW0 : IsOpen W0) (haW0 : f a ∈ W0) :
    ∃ C' : RawSourceCrossing e g T R (H a) (H b),
      (C'.chart : X → V3) = C.chart ∧ C'.chart.source ⊆ C.chart.source ∧
      C'.chart.source ⊆ W0 ∧ g '' T ∩ C'.chart.source = f '' S ∩ C'.chart.source := by
  have hfold : ∀ x ∈ S, f x = f a → x ∈ U := by
    intro x hx hxa
    exact source_double_fiber_subset p hunique (hUS a.property) (hUS b.property)
      hab hne a.property b.property ⟨hx, hxa⟩
  have hga : g (H a) = g (H b) := (hkeep a).trans (hab.trans (hkeep b).symm)
  have hgab : (H a : Y) ≠ H b := by
    intro h
    exact hne (congrArg Subtype.val (H.injective (Subtype.ext h)))
  have hfnew : ∀ x ∈ T, g x = f a → x ∈ V := by
    intro x hx hxa
    by_cases heq : x = (H a : Y)
    · exact heq ▸ (H a).property
    · apply hcontains
      exact ⟨hx, H a, hVT (H a).property, hxa.trans (hkeep a).symm, heq⟩
  obtain ⟨W, hW, haW, hWW0, hcutF, hcutG, himages⟩ :=
    exists_retained_target_neighborhood hS hT hUS hVT hU hV hf hg H hkeep
      hfold hfnew W0 hW0 haW0
  have hbW : f b ∈ W := hab ▸ haW
  let A := C.left ∩ f ⁻¹' W
  let B := C.right ∩ f ⁻¹' W
  let L := (fun z : U ↦ (H z : Y)) '' (Subtype.val ⁻¹' A)
  let N := (fun z : U ↦ (H z : Y)) '' (Subtype.val ⁻¹' B)
  have hfS : Continuous (fun z : S ↦ f z) := continuousOn_iff_continuous_domRestrict.mp hf
  have hA : IsOpen ((Subtype.val : S → E) ⁻¹' A) := C.left_open.inter (hW.preimage hfS)
  have hB : IsOpen ((Subtype.val : S → E) ⁻¹' B) := C.right_open.inter (hW.preimage hfS)
  obtain ⟨hLS, hLo, hLe, hLim⟩ := retained_source_transport_branch hUS hVT hV H hkeep hA
    (C.left_embedding.comp (IsEmbedding.inclusion inter_subset_left))
  obtain ⟨hNS, hNo, hNe, hNim⟩ := retained_source_transport_branch hUS hVT hV H hkeep hB
    (C.right_embedding.comp (IsEmbedding.inclusion inter_subset_left))
  have himage (B0 : Set E) (hB0 : B0 ⊆ S) (z : X) (hz : z ∈ W) :
      z ∈ f '' (U ∩ (B0 ∩ f ⁻¹' W)) ↔ z ∈ f '' B0 := by
    constructor
    · rintro ⟨u, ⟨_, hu, _⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, ⟨hcutF u (hB0 hu) hz, hu, hz⟩, rfl⟩
  let chart := C.chart.restrOpen W hW
  refine ⟨⟨chart, L, N, hLS, hNS, hLo, hNo, ?_, ?_, ?_, hLe, hNe,
    ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ h ↦ h.1, fun _ h ↦ hWW0 h.2, ?_⟩
  · apply disjoint_left.mpr
    rintro z ⟨u, hu, huval⟩ ⟨v, hv, hvval⟩
    have huv : u = v := H.injective (Subtype.ext (huval.trans hvval.symm))
    exact disjoint_left.mp C.disjoint hu.1 (huv.symm ▸ hv.1)
  · rcases C.labels with ⟨haL, hbN⟩ | ⟨haN, hbL⟩
    · exact Or.inl ⟨⟨a, ⟨haL, haW⟩, rfl⟩, ⟨b, ⟨hbN, hbW⟩, rfl⟩⟩
    · exact Or.inr ⟨⟨a, ⟨haN, haW⟩, rfl⟩, ⟨b, ⟨hbL, hbW⟩, rfl⟩⟩
  · exact (hkeep a).symm ▸ (show f a ∈ chart.source from ⟨C.point, haW⟩)
  · ext z
    constructor
    · rintro ⟨hzT, hzC, hzW⟩
      let u : U := H.symm ⟨z, hcutG z hzT hzW⟩
      have huval : (H u : Y) = z := congrArg Subtype.val
        (H.apply_symm_apply ⟨z, hcutG z hzT hzW⟩)
      have huf : f u = g z := (hkeep u).symm.trans (congrArg g huval)
      have huC : f u ∈ C.chart.source := huf.symm ▸ hzC
      have huW : f u ∈ W := huf.symm ▸ hzW
      rcases C.whole_preimage.subset ⟨hUS u.property, huC⟩ with huL | huN
      · exact Or.inl ⟨u, ⟨huL, huW⟩, huval⟩
      · exact Or.inr ⟨u, ⟨huN, huW⟩, huval⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · have huC := (C.whole_preimage.symm.subset (Or.inl hu.1)).2
        have hgt : g (H u) ∈ chart.source := (hkeep u).symm ▸
          (show f u ∈ chart.source from ⟨huC, hu.2⟩)
        exact ⟨hVT (H u).property, hgt⟩
      · have huC := (C.whole_preimage.symm.subset (Or.inr hu.1)).2
        have hgt : g (H u) ∈ chart.source := (hkeep u).symm ▸
          (show f u ∈ chart.source from ⟨huC, hu.2⟩)
        exact ⟨hVT (H u).property, hgt⟩
  · intro k
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (C.compatible k)).mono
      ((e k).symm.trans chart).open_source (fun _ hz ↦ ⟨hz.1, hz.2.1⟩)
  · intro z hz
    rw [hLim, himage C.left C.left_subset z hz.2]
    exact C.left_image z hz.1
  · intro z hz
    rw [hNim, himage C.right C.right_subset z hz.2]
    exact C.right_image z hz.1
  · rcases C.region with hi | ⟨hr, hf'⟩
    · exact Or.inl (fun _ hz ↦ hi hz.1)
    · exact Or.inr ⟨fun z hz ↦ hr z hz.1, fun z hz ↦ hf' z hz.1⟩
  · ext z
    constructor
    · rintro ⟨hz, hzc, hzw⟩
      exact ⟨(himages.subset ⟨hz, hzw⟩).1, hzc, hzw⟩
    · rintro ⟨hz, hzc, hzw⟩
      exact ⟨(himages.symm.subset ⟨hz, hzw⟩).1, hzc, hzw⟩

end PoincareConjecture.M76.Dehn.Annuli
