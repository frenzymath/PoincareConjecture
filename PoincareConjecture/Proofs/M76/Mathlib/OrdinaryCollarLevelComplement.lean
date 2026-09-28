import PoincareConjecture.Proofs.M76.Mathlib.CollarLevelResidualGluing
import PoincareConjecture.Proofs.M76.Mathlib.OriginalCollarLevelCharts
import PoincareConjecture.Proofs.M76.Mathlib.PointedWholeLevelComparison











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePL.exists_ordinary_collar_level_complement
    {B T d b k R : Set E} {upper g : E → ℝ}
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hcap : d ∩ T = b) (hdR : Disjoint d R)
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (H : E ≃ₜ E) (hfix : ∀ x ∈ R, H x = x)
    (hB : B = b ∪ k) (hbk : Disjoint b k)
    (hgb : ∀ x ∈ b, g x = 1) (hgk : ∀ x ∈ k, g x = 0)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKk : K.space = k)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    {t c : ℝ} (hc : 0 < c) (hct : c < t)
    (hroof : ∀ x ∈ b, c < upper x) (hHb : ∀ x ∈ b, A (H x) = t)
    {L : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)} ≃ₜ
      ((H '' T) ∩ {x | A x = c} : Set E)} (hL : L.IsFinitePL)
    (hLres : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      (L x : E) ∈ R ↔ upper x = c)
    (hLp : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H (C p) ∧
        (upper x = c ↔ (p : E × ℝ).2 = upper x)) :
    ∃ (f₀ f₁ : E → E),
      FinitePiecewiseAffineOn f₀ {x | x ∈ B ∧ c ≤ upper x} ∧
      FinitePiecewiseAffineOn f₁ {x | x ∈ k ∧ c ≤ upper x} ∧
      InjOn f₀ {x | x ∈ B ∧ c ≤ upper x} ∧
      (∀ (x : E) (hxB : x ∈ B) (hxu : c ≤ upper x),
        f₀ x = C ⟨(x, c), hxB, hc.le, hxu⟩) ∧
      (∀ (x : E) (hxk : x ∈ k) (hxu : c ≤ upper x),
        f₁ x = L ⟨x, hB.symm.subset (Or.inr hxk),
          by simpa only [hgk x hxk, mul_zero] using hc.le, hxu⟩) ∧
      ((T ∪ R) ∩ {x | A x = c}) =
        (f₀ '' b) ∪ ((f₀ '' {x | x ∈ k ∧ c ≤ upper x}) ∪ (R ∩ {x | A x = c})) ∧
      Disjoint (f₀ '' b)
        ((f₀ '' {x | x ∈ k ∧ c ≤ upper x}) ∪ (R ∩ {x | A x = c})) ∧
      Disjoint ((H '' d) ∩ {x | A x = c})
        (((H '' T) ∪ R) ∩ {x | A x = c}) ∧
      ∃ F : ((f₀ '' {x | x ∈ k ∧ c ≤ upper x}) ∪
          (R ∩ {x | A x = c}) : Set E) ≃ₜ
          (((H '' T) ∪ R) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
        (∀ x : (R ∩ {x | A x = c} : Set E),
          (F ⟨x, Or.inr x.property⟩ : E) = x) ∧
        ∀ x : {x | x ∈ k ∧ c ≤ upper x},
          (F ⟨f₀ x, Or.inl ⟨x, x.property, rfl⟩⟩ : E) = f₁ x := by
  let S₀ : Set E := {x | x ∈ B ∧ c ≤ upper x}
  let S₁ : Set E := {x | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)}
  let w : Set E := {x | x ∈ k ∧ c ≤ upper x}
  let Rc : Set E := R ∩ {x | A x = c}
  have hb₀ : b ⊆ S₀ := fun x hx => ⟨hB.symm.subset (Or.inl hx), (hroof x hx).le⟩
  have hw₀ : w ⊆ S₀ := fun _ hx => ⟨hB.symm.subset (Or.inr hx.1), hx.2⟩
  have hS₀ : S₀ = b ∪ w := by
    ext x
    constructor
    · intro hx
      rcases hB.subset hx.1 with hxb | hxk
      · exact Or.inl hxb
      · exact Or.inr ⟨hxk, hx.2⟩
    · exact fun hx => hx.elim (fun hx => hb₀ hx) (fun hx => hw₀ hx)
  have hS₁ : S₁ = w := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, hx.2.2⟩
      rcases hB.subset hx.1 with hxb | hxk
      · have htc : t ≤ c := by simpa only [hgb x hxb, mul_one] using hx.2.1
        exact (hct.not_ge htc).elim
      · exact hxk
    · intro hx
      refine ⟨hB.symm.subset (Or.inr hx.1), ?_, hx.2⟩
      simpa only [hgk x hx.1, mul_zero] using hc.le
  obtain ⟨L₀, hL₀, hL₀val⟩ := hC.exists_original_collar_level_chart A hheight hc.le
  obtain ⟨f₀, hf₀, hf₀val⟩ := hL₀
  obtain ⟨f₁, hf₁, hf₁val⟩ := hL
  have hbij₀ := L₀.bijOn_ambient_representative hf₀val
  have hbij₁ := L.bijOn_ambient_representative hf₁val
  have hf₁w : FinitePiecewiseAffineOn f₁ w := hS₁ ▸ hf₁
  have hcopy := hf₀
  obtain ⟨N, hN, hNS, _⟩ := hcopy
  obtain ⟨W, hW, hWs⟩ := N.exists_finite_triangulation_inter K hN hK
  have hWw : W.space = w := by
    rw [hWs, hNS, hKk]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨hw₀ hx, hx.1⟩⟩
  have hf₀w : FinitePiecewiseAffineOn f₀ w := by
    rw [← hWw]
    exact hf₀.restrict W hW (hWw.subset.trans hw₀)
  obtain ⟨e₀, he₀, he₀val⟩ := hf₀w.exists_homeomorph_image (hbij₀.injOn.mono hw₀)
  obtain ⟨e₁, he₁, he₁val⟩ :=
    hf₁w.exists_homeomorph_image (hS₁ ▸ hbij₁.injOn)
  have hcontact₀ (x : S₀) : f₀ x ∈ Rc ↔ upper x = c := by
    have hmem : f₀ x ∈ R ↔ c = upper x := by rw [← hf₀val, hL₀val, hresidual]
    exact ⟨fun hx => (hmem.mp hx.1).symm,
      fun hx => ⟨hmem.mpr hx.symm, by rw [← hf₀val]; exact (L₀ x).property.2⟩⟩
  have hcontact₁ (x : w) : f₁ x ∈ Rc ↔ upper x = c := by
    let z : S₁ := ⟨x, hS₁.symm.subset x.property⟩
    have hmem : f₁ x ∈ R ↔ upper x = c := by rw [← hf₁val z]; exact hLres z
    exact ⟨fun hx => hmem.mp hx.1,
      fun hx => ⟨hmem.mpr hx, by rw [← hf₁val z]; exact (L z).property.2⟩⟩
  have hequal (x : w) (hx : upper x = c) : f₀ x = f₁ x := by
    let z : S₁ := ⟨x, hS₁.symm.subset x.property⟩
    obtain ⟨p, hpbase, hpval, hphi⟩ := hLp z
    have hptop := hphi.mp hx
    have hpR : (C p : E) ∈ R :=
      (hresidual p).mpr (hptop.trans (congrArg upper hpbase).symm)
    have hCp : (C p : E) = f₀ x := by
      rw [← hf₀val ⟨x, hw₀ x.property⟩, hL₀val]
      exact congrArg (fun p => (C p : E))
        (Subtype.ext (Prod.ext hpbase (hptop.trans hx)))
    exact hCp.symm.trans ((hfix _ hpR).symm.trans (hpval.symm.trans (hf₁val z)))
  obtain ⟨Jc, hJc, hJcs⟩ := J.exists_finite_affineLevel_complex hJ A c
  have hJcR : Jc.space = Rc := by rw [hJcs, hJR]
  obtain ⟨G, hG, hGR, hGw, _, _⟩ :=
    he₀.exists_union_homeomorph_fixing_residual (q := {x | upper x = c}) he₁
      (fun x => by rw [he₀val]; exact hcontact₀ ⟨x, hw₀ x.property⟩)
      (fun x => by rw [he₁val]; exact hcontact₁ x)
      (fun x hx => by rw [he₀val, he₁val]; exact hequal x hx) Jc hJc hJcR
  have hsource : (T ∪ R) ∩ {x | A x = c} = (f₀ '' b) ∪ ((f₀ '' w) ∪ Rc) := by
    rw [union_inter_distrib_right, ← hbij₀.image_eq]
    change (f₀ '' S₀) ∪ Rc = (f₀ '' b) ∪ ((f₀ '' w) ∪ Rc)
    rw [hS₀, image_union, union_assoc]
  have htarget : (f₁ '' w) ∪ Rc = ((H '' T) ∪ R) ∩ {x | A x = c} := by
    rw [← hS₁, hbij₁.image_eq]
    exact (union_inter_distrib_right _ _ _).symm
  have hsep : Disjoint (f₀ '' b) ((f₀ '' w) ∪ Rc) := by
    apply disjoint_union_right.mpr
    constructor
    · exact disjoint_image_image fun x hx y hy hxy =>
        disjoint_left.mp hbk hx ((hbij₀.injOn (hb₀ hx) (hw₀ hy) hxy).symm ▸ hy.1)
    · apply disjoint_left.mpr
      rintro y ⟨x, hx, rfl⟩ hyR
      exact (hroof x hx).ne' ((hcontact₀ ⟨x, hb₀ hx⟩).mp hyR)
  have hcapSep : Disjoint ((H '' d) ∩ {x | A x = c})
      (((H '' T) ∪ R) ∩ {x | A x = c}) := by
    apply disjoint_left.mpr
    rintro y ⟨⟨x, hxd, rfl⟩, hxA⟩ ⟨hxTR, _⟩
    rcases hxTR with hxT | hxR
    · have hxTb : x ∈ T := H.injective.mem_set_image.mp hxT
      exact hct.ne (hxA.symm.trans (hHb x (hcap.subset ⟨hxd, hxTb⟩)))
    · have hxr : x ∈ R := by
        have heq : H x = x := H.injective (hfix _ hxR)
        exact heq ▸ hxR
      exact disjoint_left.mp hdR hxd hxr
  let F := G.trans (Homeomorph.setCongr htarget)
  refine ⟨f₀, f₁, hf₀, hf₁w, hbij₀.injOn, ?_, ?_, hsource, hsep, hcapSep,
    F, hG.setCongr rfl htarget, fun x => hGR x, ?_⟩
  · intro x hxB hxu
    exact (hf₀val ⟨x, hxB, hxu⟩).symm.trans (hL₀val _)
  · intro x hxk hxu
    exact (hf₁val ⟨x, hB.symm.subset (Or.inr hxk),
      by simpa only [hgk x hxk, mul_zero] using hc.le, hxu⟩).symm
  · intro x
    change (G ⟨f₀ x, Or.inl ⟨x, x.property, rfl⟩⟩ : E) = f₁ x
    simpa only [he₀val, he₁val] using hGw x

end Homeomorph
