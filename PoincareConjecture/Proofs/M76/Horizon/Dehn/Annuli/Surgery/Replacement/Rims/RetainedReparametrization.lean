import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.NestedRetention



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem doubleLocusOn_source_homeomorph_iff
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {S : Set E} {T : Set Y} (H : S ≃ₜ T) {f : E → X} {g : Y → X}
    (hvalue : ∀ x : S, f x = g (H x)) (x : S) :
    (x : E) ∈ doubleLocusOn f S ↔ (H x : Y) ∈ doubleLocusOn g T := by
  constructor
  · rintro ⟨_, y, hy, hxy, hne⟩
    refine ⟨(H x).property, H ⟨y, hy⟩, (H ⟨y, hy⟩).property, ?_, ?_⟩
    · rw [← hvalue, ← hvalue]
      exact hxy
    · intro heq
      exact hne (congrArg Subtype.val (H.injective (Subtype.ext heq)))
  · rintro ⟨_, y, hy, hxy, hne⟩
    refine ⟨x.property, H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property, ?_, ?_⟩
    · rw [hvalue, hvalue, H.apply_symm_apply]
      exact hxy
    · intro heq
      have hh := congrArg (fun z : S ↦ (H z : Y)) (Subtype.ext heq)
      exact hne (by simpa only [H.apply_symm_apply] using hh)

def doubleLocusOnSourceHomeomorph
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {S : Set E} {T : Set Y} (H : S ≃ₜ T) {f : E → X} {g : Y → X}
    (hvalue : ∀ x : S, f x = g (H x)) :
    doubleLocusOn f S ≃ₜ doubleLocusOn g T where
  toFun x := ⟨H ⟨x, x.property.1⟩,
    (doubleLocusOn_source_homeomorph_iff H hvalue _).mp x.property⟩
  invFun y := ⟨H.symm ⟨y, y.property.1⟩,
    (doubleLocusOn_source_homeomorph_iff H hvalue _).mpr
      (by simpa only [H.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext (congrArg (fun z : S ↦ (z : E))
    (H.symm_apply_apply ⟨x, x.property.1⟩))
  right_inv y := Subtype.ext (congrArg (fun z : T ↦ (z : Y))
    (H.apply_symm_apply ⟨y, y.property.1⟩))
  continuous_toFun := (continuous_subtype_val.comp
    (H.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp
    (H.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _

theorem double_component_count_source_homeomorph
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {S : Set E} {T : Set Y} (H : S ≃ₜ T) {f : E → X} {g : Y → X}
    (hvalue : ∀ x : S, f x = g (H x)) :
    Nat.card (ConnectedComponents (doubleLocusOn f S)) =
      Nat.card (ConnectedComponents (doubleLocusOn g T)) := by
  let D := doubleLocusOnSourceHomeomorph H hvalue
  let C := D.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y ↦ by
    have hfiber : D ⁻¹' {y} = {D.symm y} := by
      ext x
      exact D.toEquiv.eq_symm_apply.symm
    rw [hfiber]
    exact isConnected_singleton
  exact Nat.card_congr C.toEquiv

theorem exists_reparametrized_retained_source
    {E Y Z X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {K S U : Set E} {T V : Set Y} {R : Set Z}
    {f : E → X} {g : Y → X} {G : Z → X}
    (H : R ≃ₜ T) (hH : H.IsFinitePL) (hG : ∀ x : R, G x = g (H x))
    (j : K → Y) (hji : Function.Injective j) (hjc : Continuous j)
    (hjPL : ∃ J : E → Y, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = j x)
    (hjmaps : ∀ x, j x ∈ T) (hjkeep : ∀ x, g (j x) = f x)
    (hjrel : {v : Y × Y | v.1 ∈ T ∧ v.2 ∈ T ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
      (fun v : K × K ↦ (j v.1, j v.2)) '' {v | f v.1 = f v.2 ∧ (v.1 : E) ≠ v.2})
    (H₀ : U ≃ₜ V) (hVT : V ⊆ T)
    (hU : IsOpen ((Subtype.val : S → E) ⁻¹' U))
    (hV : IsOpen ((Subtype.val : T → Y) ⁻¹' V))
    (hHj : ∀ x : U, ∃ hx : (x : E) ∈ K, (H₀ x : Y) = j ⟨x, hx⟩)
    (hnew : doubleLocusOn g T ⊆ V) :
    ∃ (c : K → Z) (W : Set Z) (H₁ : U ≃ₜ W),
      (∀ x, c x = (H.symm ⟨j x, hjmaps x⟩ : Z)) ∧
      Function.Injective c ∧ Continuous c ∧
      (∃ J : E → Z, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = c x) ∧
      (∀ x, c x ∈ R) ∧ (∀ x, G (c x) = f x) ∧
      {v : Z × Z | v.1 ∈ R ∧ v.2 ∈ R ∧ G v.1 = G v.2 ∧ v.1 ≠ v.2} =
        (fun v : K × K ↦ (c v.1, c v.2)) '' {v | f v.1 = f v.2 ∧ (v.1 : E) ≠ v.2} ∧
      doubleLocusOn G R = c '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y} ∧
      W ⊆ R ∧ IsOpen ((Subtype.val : R → Z) ⁻¹' W) ∧
      IsOpen ((Subtype.val : S → E) ⁻¹' U) ∧
      (∀ x : U, ∃ hx : (x : E) ∈ K, (H₁ x : Z) = c ⟨x, hx⟩) ∧
      (∀ x : U, G (H₁ x) = f x) ∧ doubleLocusOn G R ⊆ W := by
  let c : K → Z := fun x ↦ H.symm ⟨j x, hjmaps x⟩
  have hcR (x : K) : c x ∈ R := (H.symm ⟨j x, hjmaps x⟩).property
  have hcH (x : K) : (H ⟨c x, hcR x⟩ : Y) = j x :=
    congrArg Subtype.val (H.apply_symm_apply ⟨j x, hjmaps x⟩)
  have hci : Function.Injective c := by
    intro x y hxy
    apply hji
    exact (hcH x).symm.trans ((congrArg (fun z : R ↦ (H z : Y))
      (Subtype.ext hxy)).trans (hcH y))
  have hcc : Continuous c := continuous_subtype_val.comp
    (H.symm.continuous.comp (hjc.subtype_mk hjmaps))
  have hckeep (x : K) : G (c x) = f x := by
    rw [hG ⟨c x, hcR x⟩, hcH, hjkeep]
  obtain ⟨J, hJ, hJv⟩ := hjPL
  obtain ⟨P, hP, hPv⟩ := hH.symm
  have hcPL : ∃ J' : E → Z, FinitePiecewiseAffineOn J' K ∧ ∀ x : K, J' x = c x := by
    refine ⟨P ∘ J, hP.comp hJ (fun x hx ↦ ?_), ?_⟩
    · rw [hJv ⟨x, hx⟩]
      exact hjmaps _
    · intro x
      change P (J x) = _
      rw [hJv]
      exact (hPv ⟨j x, hjmaps x⟩).symm
  have hrel : {v : Z × Z | v.1 ∈ R ∧ v.2 ∈ R ∧ G v.1 = G v.2 ∧ v.1 ≠ v.2} =
      (fun v : K × K ↦ (c v.1, c v.2)) '' {v | f v.1 = f v.2 ∧ (v.1 : E) ≠ v.2} := by
    ext v
    constructor
    · rintro ⟨hv, hw, hval, hne⟩
      have hold : ((H ⟨v.1, hv⟩ : Y), (H ⟨v.2, hw⟩ : Y)) ∈
          {w : Y × Y | w.1 ∈ T ∧ w.2 ∈ T ∧ g w.1 = g w.2 ∧ w.1 ≠ w.2} := by
        refine ⟨(H _).property, (H _).property, ?_, ?_⟩
        · simpa only [← hG] using hval
        · intro hh
          exact hne (congrArg Subtype.val (H.injective (Subtype.ext hh)))
      obtain ⟨w, hw', heq⟩ := hjrel.subset hold
      refine ⟨w, hw', Prod.ext ?_ ?_⟩
      · exact (congrArg (fun y : T ↦ (H.symm y : Z))
          (Subtype.ext (congrArg Prod.fst heq))).trans
            (congrArg Subtype.val (H.symm_apply_apply ⟨v.1, hv⟩))
      · exact (congrArg (fun y : T ↦ (H.symm y : Z))
          (Subtype.ext (congrArg Prod.snd heq))).trans
            (congrArg Subtype.val (H.symm_apply_apply ⟨v.2, hw⟩))
    · rintro ⟨v, ⟨hv, hne⟩, rfl⟩
      refine ⟨hcR _, hcR _, ?_, ?_⟩
      · rw [hckeep, hckeep]
        exact hv
      · intro hh
        exact hne (congrArg Subtype.val (hci hh))
  have hdouble : doubleLocusOn G R =
      c '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y} := by
    ext z
    constructor
    · rintro ⟨hz, w, hw, hval, hne⟩
      obtain ⟨v, ⟨hv, hne'⟩, heq⟩ := hrel.subset
        (show (z, w) ∈ {v : Z × Z |
          v.1 ∈ R ∧ v.2 ∈ R ∧ G v.1 = G v.2 ∧ v.1 ≠ v.2} from ⟨hz, hw, hval, hne⟩)
      exact ⟨v.1, ⟨v.2, hv, hne'⟩, congrArg Prod.fst heq⟩
    · rintro ⟨x, ⟨y, hval, hne⟩, rfl⟩
      have hh := hrel.symm.subset ⟨(x, y), ⟨hval, hne⟩, rfl⟩
      exact ⟨hh.1, c y, hh.2⟩
  let k : V → Z := fun y ↦ H.symm ⟨y, hVT y.property⟩
  have hk : IsEmbedding k := IsEmbedding.subtypeVal.comp
    (H.symm.isEmbedding.comp (IsEmbedding.inclusion hVT))
  let W := range k
  let H₁ : U ≃ₜ W := H₀.trans hk.toHomeomorph
  have hWR : W ⊆ R := by
    rintro x ⟨y, rfl⟩
    exact (H.symm ⟨y, hVT y.property⟩).property
  have hW : (Subtype.val : R → Z) ⁻¹' W = H ⁻¹' ((Subtype.val : T → Y) ⁻¹' V) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have hh : H.symm ⟨y, hVT y.property⟩ = x := Subtype.ext hy
      have heq := congrArg H hh
      rw [H.apply_symm_apply] at heq
      exact (congrArg (fun z : T ↦ (z : Y) ∈ V) heq).mp y.property
    · intro hx
      refine ⟨⟨H x, hx⟩, ?_⟩
      exact congrArg Subtype.val (H.symm_apply_apply x)
  have hH₁ (x : U) : ∃ hx : (x : E) ∈ K, (H₁ x : Z) = c ⟨x, hx⟩ := by
    obtain ⟨hx, hh⟩ := hHj x
    refine ⟨hx, ?_⟩
    exact congrArg (fun y : T ↦ (H.symm y : Z)) (Subtype.ext hh)
  refine ⟨c, W, H₁, fun _ ↦ rfl, hci, hcc, hcPL, hcR, hckeep, hrel, hdouble,
    hWR, ?_, hU, hH₁, ?_, ?_⟩
  · rw [hW]
    exact hV.preimage H.continuous
  · intro x
    obtain ⟨hx, hh⟩ := hH₁ x
    rw [hh, hckeep]
  · intro x hx
    have hh := hnew ((doubleLocusOn_source_homeomorph_iff H hG ⟨x, hx.1⟩).mp hx)
    exact hW.symm.subset hh

end PoincareConjecture.M76.Dehn.Annuli
