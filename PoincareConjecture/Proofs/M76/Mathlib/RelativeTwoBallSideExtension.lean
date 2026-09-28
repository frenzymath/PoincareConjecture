import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension











set_option autoImplicit false

open Set Geometry

namespace Set

variable {V W X : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]





theorem IsFinitePLBallPair.exists_extension_fix_outer_piece
    {s b d q : Set X} (hs : IsFinitePLBallPair V s (b ∪ d))
    (hb : IsFinitePLBallPair W b q) (hinter : b ∩ d = q)
    (e : d ≃ₜ d) (he : e.IsFinitePL)
    (hfix : ∀ x : d, (x : X) ∈ q → e x = x) :
    ∃ H : s ≃ₜ s, H.IsFinitePL ∧
      (∀ x : b, H ⟨x, hs.1 (Or.inl x.property)⟩ = ⟨x, hs.1 (Or.inl x.property)⟩) ∧
      (∀ x : d, H ⟨x, hs.1 (Or.inr x.property)⟩ =
        ⟨e x, hs.1 (Or.inr (e x).property)⟩) ∧
      ∀ x : s, (x : X) ∈ d ↔ (H x : X) ∈ d := by
  have hbcopy := hb
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKb, _⟩, _⟩, _⟩ := hbcopy
  have hid : (Homeomorph.refl b).IsFinitePL :=
    ⟨id, ⟨K, hK, hKb, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ X)⟩, fun _ => rfl⟩
  have hagree (x : X) (hxb : x ∈ b) (hxd : x ∈ d) :
      ((Homeomorph.refl b) ⟨x, hxb⟩ : X) = e ⟨x, hxd⟩ :=
    (congrArg Subtype.val (hfix ⟨x, hxd⟩ (hinter ▸ And.intro hxb hxd))).symm
  obtain ⟨B, hB, hBb, hBd⟩ := Homeomorph.exists_union_finitePL
    (Homeomorph.refl b) e hid he (fun _ => Iff.rfl) hagree
  obtain ⟨H, hH, hHB, _⟩ := hs.exists_extension hs B hB
  have hHd (x : d) : H ⟨x, hs.1 (Or.inr x.property)⟩ =
      ⟨e x, hs.1 (Or.inr (e x).property)⟩ := by
    apply Subtype.ext
    exact (congrArg (fun y : s => (y : X)) (hHB ⟨x, Or.inr x.property⟩)).trans (hBd x)
  refine ⟨H, hH, ?_, hHd,
    H.mem_subset_iff_of_extension e (fun _ hx => hs.1 (Or.inr hx))
      (fun _ hx => hs.1 (Or.inr hx)) hHd⟩
  intro x
  apply Subtype.ext
  exact (congrArg (fun y : s => (y : X)) (hHB ⟨x, Or.inl x.property⟩)).trans (hBb x)






theorem IsFinitePLBallPair.exists_two_side_extension_fix_outer
    {s₀ s₁ b₀ b₁ d q : Set X}
    (hs₀ : IsFinitePLBallPair V s₀ (b₀ ∪ d))
    (hs₁ : IsFinitePLBallPair V s₁ (b₁ ∪ d))
    (hb₀ : IsFinitePLBallPair W b₀ q) (hb₁ : IsFinitePLBallPair W b₁ q)
    (hinter : s₀ ∩ s₁ = d) (hbd₀ : b₀ ∩ d = q) (hbd₁ : b₁ ∩ d = q)
    (e : d ≃ₜ d) (he : e.IsFinitePL)
    (hfix : ∀ x : d, (x : X) ∈ q → e x = x) :
    ∃ H : (s₀ ∪ s₁ : Set X) ≃ₜ (s₀ ∪ s₁ : Set X), H.IsFinitePL ∧
      (∀ x : d, H ⟨x, Or.inl (hs₀.1 (Or.inr x.property))⟩ =
        ⟨e x, Or.inl (hs₀.1 (Or.inr (e x).property))⟩) ∧
      (∀ x : (s₀ ∪ s₁ : Set X), (x : X) ∈ b₀ ∪ b₁ → H x = x) ∧
      ∀ x : (s₀ ∪ s₁ : Set X), (x : X) ∈ d ↔ (H x : X) ∈ d := by
  obtain ⟨f₀, hf₀, hf₀b, hf₀d, hf₀D⟩ :=
    hs₀.exists_extension_fix_outer_piece hb₀ hbd₀ e he hfix
  obtain ⟨f₁, hf₁, hf₁b, hf₁d, _⟩ :=
    hs₁.exists_extension_fix_outer_piece hb₁ hbd₁ e he hfix
  have hcontact (x : s₀) : (x : X) ∈ s₁ ↔ (f₀ x : X) ∈ s₁ := by
    have hx : (x : X) ∈ s₁ ↔ (x : X) ∈ d := by
      rw [← hinter]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (f₀ x : X) ∈ d ↔ (f₀ x : X) ∈ s₁ := by
      rw [← hinter]
      simp only [mem_inter_iff, (f₀ x).property, true_and]
    exact hx.trans ((hf₀D x).trans hy)
  have hagree (x : X) (hx₀ : x ∈ s₀) (hx₁ : x ∈ s₁) :
      (f₀ ⟨x, hx₀⟩ : X) = f₁ ⟨x, hx₁⟩ := by
    have hxd : x ∈ d := hinter ▸ And.intro hx₀ hx₁
    exact (congrArg (fun y : s₀ => (y : X)) (hf₀d ⟨x, hxd⟩)).trans
      (congrArg (fun y : s₁ => (y : X)) (hf₁d ⟨x, hxd⟩)).symm
  obtain ⟨H, hH, hH₀, hH₁⟩ :=
    Homeomorph.exists_union_finitePL f₀ f₁ hf₀ hf₁ hcontact hagree
  have hkeep (x : d) : H ⟨x, Or.inl (hs₀.1 (Or.inr x.property))⟩ =
      ⟨e x, Or.inl (hs₀.1 (Or.inr (e x).property))⟩ := by
    apply Subtype.ext
    exact (hH₀ ⟨x, hs₀.1 (Or.inr x.property)⟩).trans
      (congrArg (fun y : s₀ => (y : X)) (hf₀d x))
  refine ⟨H, hH, hkeep, ?_,
    H.mem_subset_iff_of_extension e (fun _ hx => Or.inl (hs₀.1 (Or.inr hx)))
      (fun _ hx => Or.inl (hs₀.1 (Or.inr hx))) hkeep⟩
  intro x hx
  apply Subtype.ext
  rcases hx with hx | hx
  · exact (hH₀ ⟨x, hs₀.1 (Or.inl hx)⟩).trans
      (congrArg (fun y : s₀ => (y : X)) (hf₀b ⟨x, hx⟩))
  · exact (hH₁ ⟨x, hs₁.1 (Or.inl hx)⟩).trans
      (congrArg (fun y : s₁ => (y : X)) (hf₁b ⟨x, hx⟩))

end Set
