import PoincareConjecture.Proofs.M76.Mathlib.OrdinaryCollarLevelComplement
import PoincareConjecture.Proofs.M76.Mathlib.OrdinaryCollarCutMembership
import PoincareConjecture.Proofs.M76.Mathlib.CappedSlabLevelCoverage
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.exists_ordinary_capped_cut_level
    {S B T d b k R s₀ s₁ : Set E} {upper g : E → ℝ}
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ) {β : ℝ}
    (hslab : T ∪ R = S ∩ {x | A x ∈ Icc 0 β}) (hsS : s₀ ⊆ S)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hcap : d ∩ T = b) (hdR : Disjoint d R)
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ b) (hs₁ : IsClosed s₁)
    (hcover : T ⊆ s₀ ∪ s₁) (hinter : s₀ ∩ s₁ ⊆ b)
    (hbzero : b ⊆ {x | A x = 0})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ b → (C p : E) ∈ s₀)
    (H : E ≃ₜ E) (hfix : ∀ x ∈ R, H x = x)
    (hraise : ∀ x ∈ s₀, A x ≤ A (H x))
    (hneg : ∀ x ∈ s₀, A x < 0 → H x = x)
    (hB : B = b ∪ k) (hbk : Disjoint b k)
    (hgb : ∀ x ∈ b, g x = 1) (hgk : ∀ x ∈ k, g x = 0)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKk : K.space = k)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    {t c : ℝ} (hc : c ∈ Ioc (0 : ℝ) β) (hct : c < t)
    (hroof : ∀ x ∈ b, c < upper x) (hHb : ∀ x ∈ b, A (H x) = t)
    {L : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)} ≃ₜ
      ((H '' T) ∩ {x | A x = c} : Set E)} (hL : L.IsFinitePL)
    (hLres : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      (L x : E) ∈ R ↔ upper x = c)
    (hLp : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H (C p) ∧
        (upper x = c ↔ (p : E × ℝ).2 = upper x)) :
    ∃ (f : E → E) (X Y : Set E),
      FinitePiecewiseAffineOn f {x | x ∈ B ∧ c ≤ upper x} ∧
      InjOn f {x | x ∈ B ∧ c ≤ upper x} ∧
      b ⊆ {x | x ∈ B ∧ c ≤ upper x} ∧
      s₀ ∩ {x | A x = c} = (f '' b) ∪ X ∧ Disjoint (f '' b) X ∧
      (H '' (s₀ ∪ d)) ∩ {x | A x = c} = ((H '' d) ∩ {x | A x = c}) ∪ Y ∧
      Disjoint ((H '' d) ∩ {x | A x = c}) Y ∧
      ∃ F : X ≃ₜ Y, F.IsFinitePL ∧
        ∀ x : ((R ∩ s₀) ∩ {x | A x = c} : Set E),
          ∃ y : X, (y : E) = x ∧ (F y : E) = x := by
  obtain ⟨f₀, f₁, hf₀, _, hinj, hf₀val, hf₁val, hsource, hsep, hcapSep,
      F, hF, hFR, hFw⟩ := hC.exists_ordinary_collar_level_complement A hheight
    hcap hdR hresidual H hfix hB hbk hgb hgk K hK hKk J hJ hJR
    hc.1 hct hroof hHb hL hLres hLp
  let w : Set E := {x | x ∈ k ∧ c ≤ upper x}
  let Rc : Set E := R ∩ {x | A x = c}
  let X₀ : Set E := (f₀ '' w) ∪ Rc
  let Y₀ : Set E := ((H '' T) ∪ R) ∩ {x | A x = c}
  let X := X₀ ∩ s₀
  let Y := Y₀ ∩ (H '' s₀)
  have hwb : Disjoint w b := hbk.symm.mono_left (fun _ hx => hx.1)
  have h₀ (x : E) (hx : x ∈ w) :
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = x ∧ f₀ x = (C p : E) :=
    ⟨⟨(x, c), hB.symm.subset (Or.inr hx.1), hc.1.le, hx.2⟩, rfl,
      hf₀val x (hB.symm.subset (Or.inr hx.1)) hx.2⟩
  have h₁ (x : E) (hx : x ∈ w) :
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = x ∧ f₁ x = H (C p) := by
    let z : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)} :=
      ⟨x, hB.symm.subset (Or.inr hx.1),
        by simpa only [hgk x hx.1, mul_zero] using hc.1.le, hx.2⟩
    obtain ⟨p, hp, hv, _⟩ := hLp z
    exact ⟨p, hp, (hf₁val x hx.1 hx.2).trans hv⟩
  have hmem := C.collar_complement_map_mem_cut_iff hheight hbottom
    hs₀.isCompact.isClosed hs₁ hcover hinter hbzero H (fun x hx => hfix x hx.1)
    hwb f₀ f₁ h₀ h₁ F hFR hFw
  have hcopy := hs₀
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K₀, hK₀, hK₀s, _⟩, _⟩, _⟩ := hcopy
  obtain ⟨G, hG, hGval⟩ := hF.exists_cut_image_restriction H hmem K₀ hK₀ hK₀s
  have hselectedImage : f₀ '' b ⊆ s₀ := by
    rintro y ⟨x, hx, rfl⟩
    rw [hf₀val x (hB.symm.subset (Or.inl hx)) (hroof x hx).le]
    exact hselected _ hx
  have hsrc : s₀ ∩ {x | A x = c} = (f₀ '' b) ∪ X := by
    have hwhole : ((T ∪ R) ∩ {x | A x = c}) ∩ s₀ = s₀ ∩ {x | A x = c} := by
      rw [← cut_slab_level_eq hsS hslab ⟨hc.1.le, hc.2⟩]
      ext x
      simp only [mem_inter_iff, mem_union]
      tauto
    rw [← hwhole, hsource, union_inter_distrib_right,
      inter_eq_left.mpr hselectedImage]
  have hY : Y = ((H '' (T ∩ s₀)) ∪ (R ∩ s₀)) ∩ {x | A x = c} := by
    ext y
    constructor
    · rintro ⟨⟨hyT | hyR, hyc⟩, hys⟩
      · exact ⟨Or.inl ((image_inter H.injective).symm.subset ⟨hyT, hys⟩), hyc⟩
      · have hys₀ : y ∈ s₀ := by
          rw [← hfix y hyR, H.injective.mem_set_image] at hys
          exact hys
        exact ⟨Or.inr ⟨hyR, hys₀⟩, hyc⟩
    · rintro ⟨hy | hy, hyc⟩
      · have hboth := (image_inter H.injective).subset hy
        exact ⟨⟨Or.inl hboth.1, hyc⟩, hboth.2⟩
      · exact ⟨⟨Or.inr hy.1, hyc⟩, ⟨y, hy.2, hfix y hy.1⟩⟩
  have htgt : (H '' (s₀ ∪ d)) ∩ {x | A x = c} =
      ((H '' d) ∩ {x | A x = c}) ∪ Y := by
    rw [image_capped_slab_level_eq hsS hslab H hraise hneg hfix hc, hY,
      image_union]
    simp only [union_inter_distrib_right, union_assoc]
  refine ⟨f₀, X, Y, hf₀, hinj,
    fun x hx => ⟨hB.symm.subset (Or.inl hx), (hroof x hx).le⟩, hsrc,
    hsep.mono_right inter_subset_left, htgt, hcapSep.mono_right inter_subset_left,
    G, hG, ?_⟩
  intro x
  let y : X := ⟨x, Or.inr ⟨x.property.1.1, x.property.2⟩, x.property.1.2⟩
  exact ⟨y, rfl, (hGval y).trans (hFR ⟨x, x.property.1.1, x.property.2⟩)⟩

end Homeomorph
