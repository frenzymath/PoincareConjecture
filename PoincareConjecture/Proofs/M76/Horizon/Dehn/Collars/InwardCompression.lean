import PoincareConjecture.Proofs.M76.Horizon.Dehn.Collars.StripResidual
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps











set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

local notation "I" => Icc (0 : ℝ) 1



theorem exists_inward_collar_compression
    (K : SimplicialComplex ℝ F) (L : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    (c : E × ℝ → F) (hc : FinitePiecewiseAffineOn c (L.space ×ˢ I))
    (hinj : InjOn c (L.space ×ˢ I)) (hinside : MapsTo c (L.space ×ˢ I) K.space)
    (hopen : IsOpen ((Subtype.val : K.space → F) ⁻¹'
      (c '' (L.space ×ˢ Ico (0 : ℝ) 1)))) :
    ∃ (D : Set F) (H : K.space ≃ₜ D), H.IsFinitePL ∧ D ⊆ K.space ∧
      (∀ z (hz : z ∈ L.space ×ˢ I),
        (H ⟨c z, hinside hz⟩ : F) = c (z.1, (z.2 + 1) / 2)) ∧
      (∀ x : K.space, (x : F) ∉ c '' (L.space ×ˢ Ico (0 : ℝ) 1) → (H x : F) = x) ∧
      ∀ z ∈ L.space ×ˢ I, c z ∈ D ↔ (1 / 2 : ℝ) ≤ z.2 := by
  obtain ⟨J, hJ, hJs, hcover, hroof⟩ :=
    exists_finite_collar_strip_residual K L hK hL c hc hinj hinside hopen
  let a : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      ((1 / 2 : ℝ) • ((ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap +
        ContinuousAffineMap.const ℝ (E × ℝ) 1))
  have haval (z : E × ℝ) : a z = (z.1, (z.2 + 1) / 2) := by
    apply Prod.ext
    · rfl
    change (1 / 2 : ℝ) * (z.2 + 1) = (z.2 + 1) / 2
    ring
  have hamap : MapsTo a (L.space ×ˢ I) (L.space ×ˢ I) := by
    intro z hz
    rw [haval]
    exact ⟨hz.1, by dsimp; constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hainj : Function.Injective a := by
    intro z w heq
    rw [haval, haval] at heq
    apply Prod.ext
    · have h := congrArg Prod.fst heq
      exact h
    have h := congrArg Prod.snd heq
    dsimp at h
    linarith
  have hcopy := hc
  obtain ⟨T, hT, hTs, _⟩ := hcopy
  have ha : FinitePiecewiseAffineOn a (L.space ×ˢ I) :=
    hTs ▸ (T.affineOnFaces_affine a).finitePiecewiseAffineOn hT
  have hk : FinitePiecewiseAffineOn (c ∘ a) (L.space ×ˢ I) := hc.comp ha hamap
  have hki : InjOn (c ∘ a) (L.space ×ˢ I) :=
    fun _ hx _ hy hxy ↦ hainj (hinj (hamap hx) (hamap hy) hxy)
  obtain ⟨C, hC, hCval⟩ := hc.exists_homeomorph_image hinj
  obtain ⟨B, hB, hBval⟩ := hk.exists_homeomorph_image hki
  let G := C.symm.trans B
  have hG : G.IsFinitePL := hC.symm.trans hB
  have hGval (z : L.space ×ˢ I) : (G (C z) : F) = c (a z) := by
    change (B (C.symm (C z)) : F) = _
    rw [C.symm_apply_apply]
    exact hBval z
  have hGoverlap (x : c '' (L.space ×ˢ I)) :
      (x : F) ∈ J.space ↔ (G x : F) ∈ J.space := by
    obtain ⟨z, rfl⟩ := C.surjective x
    rw [hCval, hGval, hroof _ z.property, hroof _ (hamap z.property), haval]
    change z.val.2 = 1 ↔ (z.val.2 + 1) / 2 = 1
    constructor <;> intro h <;> linarith
  have hagree (x : F) (hxC : x ∈ c '' (L.space ×ˢ I)) (hxJ : x ∈ J.space) :
      (G ⟨x, hxC⟩ : F) = (Homeomorph.refl J.space ⟨x, hxJ⟩ : F) := by
    change (G ⟨x, hxC⟩ : F) = x
    obtain ⟨z, hz⟩ := C.surjective ⟨x, hxC⟩
    have hzval : c z = x := (hCval z).symm.trans (congrArg Subtype.val hz)
    have hz1 : (z : E × ℝ).2 = 1 := (hroof _ z.property).mp (hzval.symm ▸ hxJ)
    rw [← hz, hGval, haval, hz1]
    have hzpair : ((z : E × ℝ).1, 1) = (z : E × ℝ) := by
      apply Prod.ext
      · rfl
      · exact hz1.symm
    norm_num
    exact (congrArg c hzpair).trans hzval
  have hid : (Homeomorph.refl J.space).IsFinitePL :=
    ⟨id, (J.affineOnFaces_affine (ContinuousAffineMap.id ℝ F)).finitePiecewiseAffineOn hJ,
      fun _ ↦ rfl⟩
  obtain ⟨U, hU, hUC, hUJ⟩ :=
    Homeomorph.exists_union_finitePL G (Homeomorph.refl J.space) hG hid hGoverlap hagree
  let D := (c ∘ a) '' (L.space ×ˢ I) ∪ J.space
  let H : K.space ≃ₜ D := (Homeomorph.setCongr hcover.symm).trans U
  have hH : H.IsFinitePL := hU.setCongr hcover rfl
  have hD : D ⊆ K.space := by
    apply union_subset
    · rintro _ ⟨z, hz, rfl⟩
      exact hinside (hamap hz)
    · rw [hJs]
      exact sdiff_subset
  refine ⟨D, H, hH, hD, ?_, ?_, ?_⟩
  · intro z hz
    have heq : (⟨c z, mem_image_of_mem c hz⟩ : c '' (L.space ×ˢ I)) = C ⟨z, hz⟩ :=
      Subtype.ext (hCval ⟨z, hz⟩).symm
    exact (hUC ⟨c z, mem_image_of_mem c hz⟩).trans (by rw [heq, hGval, haval])
  · intro x hx
    have hxJ : (x : F) ∈ J.space := hJs.symm ▸ ⟨x.property, hx⟩
    exact hUJ ⟨x, hxJ⟩
  · intro z hz
    constructor
    · intro hzD
      rcases hzD with ⟨w, hw, heq⟩ | hzJ
      · have he := hinj (hamap hw) hz heq
        rw [haval] at he
        have ht := congrArg Prod.snd he
        dsimp at ht
        linarith [hw.2.1]
      · rw [(hroof _ hz).mp hzJ]
        norm_num
    · intro hzhalf
      let w : E × ℝ := (z.1, 2 * z.2 - 1)
      have hw : w ∈ L.space ×ˢ I := ⟨hz.1, by
        dsimp [w]; constructor <;> linarith [hz.2.2]⟩
      apply Or.inl
      refine ⟨w, hw, ?_⟩
      change c (a w) = c z
      congr 1
      rw [haval]
      apply Prod.ext
      · rfl
      dsimp [w]
      ring

end PoincareConjecture.M76.Dehn
