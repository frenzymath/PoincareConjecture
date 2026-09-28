import PoincareConjecture.Proofs.M76.Mathlib.TerminalWholeLevelComparison
import PoincareConjecture.Proofs.M76.Mathlib.CollarLevelCutMembership
import PoincareConjecture.Proofs.M76.Mathlib.CappedCollarLevelRestriction
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePL.exists_terminal_capped_cut_level
    {B T d b k R s₀ s₁ : Set E} {upper g r : E → ℝ} {q : E}
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ T = b)
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ b) (hs₁ : IsClosed s₁)
    (hcover : T ⊆ s₀ ∪ s₁) (hinter : s₀ ∩ s₁ ⊆ b)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ b → (C p : E) ∈ s₀)
    (H : E ≃ₜ E) (hfix : ∀ x ∈ R, H x = x)
    (hB : B = b ∪ k) (htouch : b ∩ k ⊆ {q}) (hqzero : upper q = 0)
    (hgk : ∀ x ∈ k, g x = 0)
    {t m c : ℝ} (ht : 0 < t) (hc : 0 < c) (hmc : t * m ≤ c)
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
    ∃ G : (((T ∩ s₀) ∪ (R ∩ s₀)) ∩ {x | A x = c} : Set E) ≃ₜ
        (((H '' (d ∪ (T ∩ s₀))) ∪ (R ∩ s₀)) ∩ {x | A x = c} : Set E),
      G.IsFinitePL ∧ ∀ x : ((R ∩ s₀) ∩ {x | A x = c} : Set E),
        (G ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x := by
  obtain ⟨F, hF, hFR, hFchart⟩ := hC.exists_terminal_whole_level_comparison_with_chart
    A hheight hcap hresidual H hfix ht hc.le hmc hbound hmax hgB hHheight J hJ hJR hL hLres hLp
  obtain ⟨f, _, hfval⟩ := hL
  have hfp (x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)}) :
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ f x = H (C p) := by
    obtain ⟨p, hbase, hval, _⟩ := hLp x
    exact ⟨p, hbase, (hfval x).symm.trans hval⟩
  have hFselected (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)})
      (hpb : (p : E × ℝ).1 ∈ b) (hpz : (p : E × ℝ).2 = c) :
      (F ⟨C p, ⟨Or.inl (C p).property, (hheight p).trans hpz⟩⟩ : E) ∈ H '' (s₀ ∪ d) := by
    have hroof : c ≤ upper (p : E × ℝ).1 := hpz ▸ p.property.2.2
    obtain ⟨y, hy, hFy⟩ := hFchart (p : E × ℝ).1 p.property.1 hroof
    have hyEq : y = ⟨C p, ⟨Or.inl (C p).property, (hheight p).trans hpz⟩⟩ := by
      apply Subtype.ext
      exact hy.trans (congrArg (fun p => (C p : E)) (Subtype.ext (Prod.ext rfl hpz.symm)))
    rw [hyEq] at hFy
    let x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)} :=
      ⟨(p : E × ℝ).1, p.property.1,
        (mul_le_mul_of_nonneg_left (hgB _ p.property.1) ht.le).trans hmc, hroof⟩
    obtain ⟨p', hbase, hval, _⟩ := hLp x
    rw [hFy, hval]
    exact mem_image_of_mem H (Or.inl (hselected p' (hbase.symm ▸ hpb)))
  have hFother (x : E) (hxk : x ∈ k) (hxu : c ≤ upper x) :
      ∃ z : ((T ∪ R) ∩ {x | A x = c} : Set E),
        (z : E) = C ⟨(x, c), hB.symm.subset (Or.inr hxk), hc.le, hxu⟩ ∧
        (F z : E) = f x := by
    obtain ⟨z, hz, hFz⟩ := hFchart x (hB.symm.subset (Or.inr hxk)) hxu
    exact ⟨z, hz, hFz.trans (hfval _)⟩
  have hmem := C.collar_level_map_mem_selected_cut_iff hheight hbottom hdplane hcap
    hs₀.isCompact.isClosed hs₁ hcover hinter
    (fun _ hx => hdplane (hcap.symm.subset hx).1) hselected H hfix
    hB htouch hqzero hgk hc f hfp F hFR hFselected hFother
  have hcopy := hs₀
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨N, hN, hNs, _⟩, _⟩, _⟩ := hcopy
  exact hF.exists_capped_collar_cut_restriction H hfix hdplane hc.ne' hmem hFR N hN hNs

end Homeomorph
