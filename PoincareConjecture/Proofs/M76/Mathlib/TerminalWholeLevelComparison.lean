import PoincareConjecture.Proofs.M76.Mathlib.CollarLevelResidualGluing
import PoincareConjecture.Proofs.M76.Mathlib.OriginalCollarLevelCharts










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePL.exists_terminal_whole_level_comparison_with_chart
    {B T d b R : Set E} {upper g r : E → ℝ}
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2) (hcap : d ∩ T = b)
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (H : E ≃ₜ E) (hfix : ∀ x ∈ R, H x = x)
    {t m c : ℝ} (ht : 0 < t) (hc : 0 ≤ c) (hmc : t * m ≤ c)
    (hbound : ∀ x ∈ d, r x ≤ m) (hmax : ∀ x ∈ d, r x = m → x ∈ b)
    (hgB : ∀ x ∈ B, g x ≤ m) (hHheight : ∀ x ∈ d, A (H x) = t * r x)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    {L : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)} ≃ₜ
      ((H '' T) ∩ {x | A x = c} : Set E)} (hL : L.IsFinitePL)
    (hLres : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      (L x : E) ∈ R ↔ upper x = c)
    (hLp : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H (C p) ∧
        (upper x = c ↔ (p : E × ℝ).2 = upper x)) :
    ∃ F : ((T ∪ R) ∩ {x | A x = c} : Set E) ≃ₜ
        (((H '' (d ∪ T)) ∪ R) ∩ {x | A x = c} : Set E),
      F.IsFinitePL ∧
      (∀ x : (R ∩ {x | A x = c} : Set E),
        (F ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x) ∧
      ∀ (x : E) (hxB : x ∈ B) (hxu : c ≤ upper x),
        ∃ y : ((T ∪ R) ∩ {x | A x = c} : Set E),
          (y : E) = C ⟨(x, c), hxB, hc, hxu⟩ ∧
          (F y : E) = L ⟨x, hxB,
            (mul_le_mul_of_nonneg_left (hgB x hxB) ht.le).trans hmc, hxu⟩ := by
  let S₀ : Set E := {x | x ∈ B ∧ c ≤ upper x}
  let S₁ : Set E := {x | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)}
  let Rc : Set E := R ∩ {x | A x = c}
  have hS : S₁ = S₀ := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx =>
      ⟨hx.1, (mul_le_mul_of_nonneg_left (hgB x hx.1) ht.le).trans hmc, hx.2⟩⟩
  obtain ⟨L₀, hL₀, hL₀val⟩ := hC.exists_original_collar_level_chart A hheight hc
  let L₁ := (Homeomorph.setCongr hS.symm).trans (L.trans (Homeomorph.setCongr rfl))
  have hL₁ : L₁.IsFinitePL := hL.setCongr hS rfl
  have hcontact₀ (x : S₀) : (L₀ x : E) ∈ Rc ↔ upper x = c := by
    have hmem : (L₀ x : E) ∈ R ↔ c = upper x := by rw [hL₀val, hresidual]
    exact ⟨fun hx => (hmem.mp hx.1).symm,
      fun hx => ⟨hmem.mpr hx.symm, (L₀ x).property.2⟩⟩
  have hcontact₁ (x : S₀) : (L₁ x : E) ∈ Rc ↔ upper x = c := by
    have hmem : (L₁ x : E) ∈ R ↔ upper x = c := hLres ⟨x, hS.symm.subset x.property⟩
    exact ⟨fun hx => hmem.mp hx.1, fun hx => ⟨hmem.mpr hx, (L₁ x).property.2⟩⟩
  have hequal (x : S₀) (hx : upper x = c) : (L₀ x : E) = L₁ x := by
    obtain ⟨p, hpbase, hpval, hphi⟩ := hLp ⟨x, hS.symm.subset x.property⟩
    have hptop := hphi.mp hx
    have hpR : (C p : E) ∈ R :=
      (hresidual p).mpr (hptop.trans (congrArg upper hpbase).symm)
    have hCp : (C p : E) = L₀ x := by
      rw [hL₀val]
      exact congrArg (fun p => (C p : E))
        (Subtype.ext (Prod.ext hpbase (hptop.trans hx)))
    exact hCp.symm.trans ((hfix _ hpR).symm.trans hpval.symm)
  obtain ⟨Jc, hJc, hJcs⟩ := J.exists_finite_affineLevel_complex hJ A c
  have hJcR : Jc.space = Rc := by rw [hJcs, hJR]
  obtain ⟨G, hG, hGR, hGchart, _, _⟩ :=
    hL₀.exists_union_homeomorph_fixing_residual (q := {x | upper x = c}) hL₁
      hcontact₀ hcontact₁ hequal Jc hJc hJcR
  have hcapLevel : (H '' d) ∩ {x | A x = c} ⊆ (H '' T) ∩ {x | A x = c} := by
    rintro y ⟨⟨x, hx, rfl⟩, hlevel⟩
    have hmul : t * r x = c := (hHheight x hx).symm.trans hlevel
    have hrx : r x = m := le_antisymm (hbound x hx)
      (le_of_mul_le_mul_left (hmc.trans_eq hmul.symm) ht)
    exact ⟨mem_image_of_mem H (hcap.symm.subset (hmax x hx hrx)).2, hlevel⟩
  have hsource : (T ∩ {x | A x = c}) ∪ Rc = (T ∪ R) ∩ {x | A x = c} :=
    (union_inter_distrib_right T R _).symm
  have htarget : ((H '' T) ∩ {x | A x = c}) ∪ Rc =
      ((H '' (d ∪ T)) ∪ R) ∩ {x | A x = c} := by
    rw [image_union, union_inter_distrib_right, union_inter_distrib_right,
      union_eq_right.mpr hcapLevel]
  let F := (Homeomorph.setCongr hsource.symm).trans
    (G.trans (Homeomorph.setCongr htarget))
  refine ⟨F, hG.setCongr hsource htarget, fun x => hGR x, ?_⟩
  intro x hxB hxu
  let z : S₀ := ⟨x, hxB, hxu⟩
  let y : ((T ∪ R) ∩ {x | A x = c} : Set E) :=
    ⟨L₀ z, Or.inl (L₀ z).property.1, (L₀ z).property.2⟩
  exact ⟨y, hL₀val z, hGchart z⟩





theorem IsFinitePL.exists_terminal_whole_level_comparison
    {B T d b R : Set E} {upper g r : E → ℝ}
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2) (hcap : d ∩ T = b)
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (H : E ≃ₜ E) (hfix : ∀ x ∈ R, H x = x)
    {t m c : ℝ} (ht : 0 < t) (hc : 0 ≤ c) (hmc : t * m ≤ c)
    (hbound : ∀ x ∈ d, r x ≤ m) (hmax : ∀ x ∈ d, r x = m → x ∈ b)
    (hgB : ∀ x ∈ B, g x ≤ m) (hHheight : ∀ x ∈ d, A (H x) = t * r x)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    {L : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)} ≃ₜ
      ((H '' T) ∩ {x | A x = c} : Set E)} (hL : L.IsFinitePL)
    (hLres : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      (L x : E) ∈ R ↔ upper x = c)
    (hLp : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H (C p) ∧
        (upper x = c ↔ (p : E × ℝ).2 = upper x)) :
    ∃ F : ((T ∪ R) ∩ {x | A x = c} : Set E) ≃ₜ
        (((H '' (d ∪ T)) ∪ R) ∩ {x | A x = c} : Set E),
      F.IsFinitePL ∧ ∀ x : (R ∩ {x | A x = c} : Set E),
        (F ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x := by
  obtain ⟨F, hF, hFR, _⟩ := hC.exists_terminal_whole_level_comparison_with_chart
    A hheight hcap hresidual H hfix ht hc hmc hbound hmax hgB hHheight J hJ hJR hL hLres hLp
  exact ⟨F, hF, hFR⟩

end Homeomorph
