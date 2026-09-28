import PoincareConjecture.Proofs.M76.Mathlib.PointedWholeLevelComparison
import PoincareConjecture.Proofs.M76.Mathlib.CollarLevelCutMembership
import PoincareConjecture.Proofs.M76.Mathlib.CappedCollarLevelRestriction
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePL.exists_pointed_capped_cut_level
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
    (hgr : EqOn g r b) (hgk : ∀ x ∈ k, g x = 0)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKk : K.space = k)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    {t a : ℝ} (ht : 0 < t) (hc : 0 < t * a)
    (hhigh : ∀ x ∈ b, a ≤ r x → t * a < upper x)
    (hwidth : IsFinitePLBallPair ℝ (b ∩ {x | t * a ≤ upper x})
      (b ∩ {x | upper x = t * a}))
    {L : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)} ≃ₜ
      ((H '' T) ∩ {x | A x = t * a} : Set E)} (hL : L.IsFinitePL)
    (hLres : ∀ x : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)},
      (L x : E) ∈ R ↔ upper x = t * a)
    (hLp : ∀ x : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H (C p) ∧
        (t * g x = t * a ↔ (p : E × ℝ).2 = 0) ∧
        (upper x = t * a ↔ (p : E × ℝ).2 = upper x))
    {f : E → E} (hfval : ∀ x, (L x : E) = f x)
    (hball : IsFinitePLBallPair ℝ
      (((H '' d) ∩ {x | A x = t * a}) ∪
        f '' ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}))
      (f '' (b ∩ {x | upper x = t * a})))
    (harcR : (((H '' d) ∩ {x | A x = t * a}) ∪
        f '' ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x})) ∩ R =
      f '' (b ∩ {x | upper x = t * a})) :
    ∃ G : (((T ∩ s₀) ∪ (R ∩ s₀)) ∩ {x | A x = t * a} : Set E) ≃ₜ
        (((H '' (d ∪ (T ∩ s₀))) ∪ (R ∩ s₀)) ∩ {x | A x = t * a} : Set E),
      G.IsFinitePL ∧ ∀ x : ((R ∩ s₀) ∩ {x | A x = t * a} : Set E),
        (G ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x := by
  obtain ⟨F, hF, hFR, hFselected, hFother⟩ :=
    hC.exists_pointed_whole_level_comparison_with_selected A hheight hbottom hdplane hcap
      hresidual H hfix hB htouch hqzero hgr hgk K hK hKk J hJ hJR ht hc
      hhigh hwidth hL hLres hLp hfval hball harcR
  have hfp (x : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)}) :
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ f x = H (C p) := by
    obtain ⟨p, hbase, hval, _, _⟩ := hLp x
    exact ⟨p, hbase, (hfval x).symm.trans hval⟩
  have hjS : (b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x} ⊆
      {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)} := by
    intro x hx
    refine ⟨hB.symm.subset (Or.inl hx.1.1), ?_, hx.2⟩
    rw [hgr hx.1.1]
    exact mul_le_mul_of_nonneg_left hx.1.2 ht.le
  have harcSide : ((H '' d) ∩ {x | A x = t * a}) ∪
      f '' ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}) ⊆ H '' (s₀ ∪ d) := by
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact image_mono subset_union_right hy.1
    · obtain ⟨p, hbase, hval⟩ := hfp ⟨x, hjS hx⟩
      refine ⟨C p, Or.inl (hselected p (hbase.symm ▸ hx.1.1)), hval.symm⟩
  have hmem := C.collar_level_map_mem_selected_cut_iff hheight hbottom hdplane hcap
    hs₀.isCompact.isClosed hs₁ hcover hinter
    (fun _ hx => hdplane (hcap.symm.subset hx).1) hselected H hfix
    hB htouch hqzero hgk hc f hfp F hFR
    (fun p hpb hpz => harcSide (hFselected p hpb hpz)) hFother
  have hcopy := hs₀
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨N, hN, hNs, _⟩, _⟩, _⟩ := hcopy
  exact hF.exists_capped_collar_cut_restriction H hfix hdplane hc.ne' hmem hFR N hN hNs

end Homeomorph
