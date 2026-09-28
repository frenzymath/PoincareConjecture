import PoincareConjecture.Proofs.M76.Mathlib.CollarCutMembership











set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]






theorem collar_level_map_mem_selected_cut_iff
    {B T d b k R s₀ s₁ Y : Set E} {upper g A : E → ℝ} {q : E}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ T = b)
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁) (hcover : T ⊆ s₀ ∪ s₁)
    (hinter : s₀ ∩ s₁ ⊆ b) (hbzero : b ⊆ {x | A x = 0})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ b → (C p : E) ∈ s₀)
    (H : E ≃ₜ E) (hfix : ∀ x ∈ R, H x = x)
    (hB : B = b ∪ k) (htouch : b ∩ k ⊆ {q}) (hqzero : upper q = 0)
    (hgk : ∀ x ∈ k, g x = 0) {t c : ℝ} (hc : 0 < c) (f : E → E)
    (hfp : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ f x = H (C p))
    (F : ((T ∪ R) ∩ {x | A x = c} : Set E) ≃ₜ Y)
    (hFR : ∀ x : (R ∩ {x | A x = c} : Set E),
      (F ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x)
    (hFselected : ∀ (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)})
        (_hb : (p : E × ℝ).1 ∈ b) (hz : (p : E × ℝ).2 = c),
      (F ⟨C p, ⟨Or.inl (C p).property, (hheight p).trans hz⟩⟩ : E) ∈ H '' (s₀ ∪ d))
    (hFother : ∀ (x : E) (hxk : x ∈ k) (hxu : c ≤ upper x),
      ∃ z : ((T ∪ R) ∩ {x | A x = c} : Set E),
        (z : E) = C ⟨(x, c), hB.symm.subset (Or.inr hxk), hc.le, hxu⟩ ∧
        (F z : E) = f x) :
    ∀ y : ((T ∪ R) ∩ {x | A x = c} : Set E),
      (y : E) ∈ s₀ ↔ (F y : E) ∈ H '' (s₀ ∪ d) := by
  intro y
  rcases y.property.1 with hyT | hyR
  · let p := C.symm ⟨y, hyT⟩
    have hCp : (C p : E) = y := congrArg Subtype.val (C.apply_symm_apply _)
    have hpc : (p : E × ℝ).2 = c :=
      (hheight p).symm.trans ((congrArg A hCp).trans y.property.2)
    rcases hB.subset p.property.1 with hpb | hpk
    · let z : ((T ∪ R) ∩ {x | A x = c} : Set E) :=
        ⟨C p, ⟨Or.inl (C p).property, (hheight p).trans hpc⟩⟩
      have hzy : z = y := Subtype.ext hCp
      rw [← hzy]
      exact iff_of_true (hselected p hpb) (hFselected p hpb hpc)
    · have hroof : c ≤ upper (p : E × ℝ).1 := hpc ▸ p.property.2.2
      have hnotb : (p : E × ℝ).1 ∉ b := by
        intro hb
        have heq : (p : E × ℝ).1 = q := htouch ⟨hb, hpk⟩
        have hbad : c ≤ 0 := by simpa only [heq, hqzero] using hroof
        exact (not_le_of_gt hc) hbad
      have hsrc : (p : E × ℝ).1 ∈
          {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)} := by
        refine ⟨p.property.1, ?_, hroof⟩
        rw [hgk _ hpk, mul_zero]
        exact hc.le
      obtain ⟨p', hpbase, hpval⟩ := hfp ⟨(p : E × ℝ).1, hsrc⟩
      have hnotb' : (p' : E × ℝ).1 ∉ b := by rwa [hpbase]
      have hnotd : (C p' : E) ∉ d := by
        intro hd
        have hCb : (C p' : E) ∈ b := hcap.subset ⟨hd, (C p').property⟩
        have hp0 : (p' : E × ℝ).2 = 0 := (hheight p').symm.trans (hbzero hCb)
        exact hnotb' ((hbottom p' hp0) ▸ hCb)
      have hnew : f (p : E × ℝ).1 ∈ H '' (s₀ ∪ d) ↔ (p : E × ℝ).1 ∈ s₀ := by
        rw [hpval, H.injective.mem_set_image, mem_union, or_iff_left hnotd]
        exact (C.collar_fiber_mem_cut_iff hheight hbottom hs₀ hs₁ hcover
          hinter hbzero p' hnotb').1.trans (by rw [hpbase])
      obtain ⟨z, hz, hFz⟩ := hFother (p : E × ℝ).1 hpk hroof
      have hzy : z = y := by
        apply Subtype.ext
        refine hz.trans ((congrArg (fun p => (C p : E)) ?_).trans hCp)
        exact Subtype.ext (Prod.ext rfl hpc.symm)
      rw [hzy] at hFz
      rw [hFz]
      have hold := (C.collar_fiber_mem_cut_iff hheight hbottom hs₀ hs₁ hcover
        hinter hbzero p hnotb).1
      rw [hCp] at hold
      exact hold.trans hnew.symm
  · have hFy : (F y : E) = y := hFR ⟨y, hyR, y.property.2⟩
    have hnotd : (y : E) ∉ d :=
      fun hy => hc.ne' (y.property.2.symm.trans (hdplane hy))
    rw [hFy, ← hfix y hyR, H.injective.mem_set_image, mem_union, or_iff_left hnotd,
      hfix y hyR]

end Homeomorph
