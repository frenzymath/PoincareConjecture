import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPrismPreimages









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem prescribed_prism_interval_eq
    {E : Type*} [TopologicalSpace E] {A D Z : Set E}
    (b : Icc (0 : ℝ) 1 ≃ₜ A) (hZD : Z ⊆ D)
    {α β γ δ : ℝ} (hαβ : α ≤ β) (hγδ : γ ≤ δ)
    (hsub : Icc α β ⊆ Icc (0 : ℝ) 1) (hcanonSub : Icc γ δ ⊆ Icc (0 : ℝ) 1)
    (H : ↥(signedTubeDiamond ×ˢ Icc α β) ≃ₜ D)
    (haxis : ∀ x : ↥(signedTubeDiamond ×ˢ Icc α β),
      (x : P2 × ℝ).1 = (0, 0) ↔ (H x : E) ∈ Z)
    (hkeep : ∀ t : Icc α β,
      (H ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _), t.property⟩ : E) = b ⟨t, hsub t.property⟩)
    (canonical : Icc γ δ ≃ₜ Z)
    (hcanon : ∀ t : Icc γ δ, (canonical t : E) = b ⟨t, hcanonSub t.property⟩) :
    α = γ ∧ β = δ := by
  have hforward (t : Icc α β) : (t : ℝ) ∈ Icc γ δ := by
    let x : ↥(signedTubeDiamond ×ˢ Icc α β) := ⟨((0, 0), t),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _), t.property⟩
    have hz : (H x : E) ∈ Z := (haxis x).mp rfl
    let u : Icc γ δ := canonical.symm ⟨H x, hz⟩
    have hcu : (canonical u : E) = H x := congrArg Subtype.val (canonical.apply_symm_apply _)
    have he : (b ⟨t, hsub t.property⟩ : E) = b ⟨u, hcanonSub u.property⟩ :=
      (hkeep t).symm.trans (hcu.symm.trans (hcanon u))
    have htu : (t : ℝ) = u := congrArg Subtype.val (b.injective (Subtype.ext he))
    exact htu.symm ▸ u.property
  have hbackward (u : Icc γ δ) : (u : ℝ) ∈ Icc α β := by
    let x : ↥(signedTubeDiamond ×ˢ Icc α β) := H.symm ⟨canonical u, hZD (canonical u).property⟩
    have hx : (H x : E) = canonical u := congrArg Subtype.val (H.apply_symm_apply _)
    have hfirst : (x : P2 × ℝ).1 = (0, 0) := (haxis x).mpr (hx.symm ▸ (canonical u).property)
    let t : Icc α β := ⟨(x : P2 × ℝ).2, x.property.2⟩
    have hxeq : x = ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _), t.property⟩ := Subtype.ext (Prod.ext hfirst rfl)
    have he : (b ⟨t, hsub t.property⟩ : E) = b ⟨u, hcanonSub u.property⟩ :=
      (hkeep t).symm.trans ((congrArg (fun p => (H p : E)) hxeq).symm.trans
        (hx.trans (hcanon u)))
    have htu : (t : ℝ) = u := congrArg Subtype.val (b.injective (Subtype.ext he))
    exact htu ▸ t.property
  exact ⟨le_antisymm (hbackward ⟨γ, le_rfl, hγδ⟩).1 (hforward ⟨α, le_rfl, hαβ⟩).1,
    le_antisymm (hforward ⟨β, hαβ, le_rfl⟩).2 (hbackward ⟨δ, hγδ, le_rfl⟩).2⟩

theorem prescribed_prism_end_time
    {E : Type*} [TopologicalSpace E] {A D J : Set E}
    (b : Icc (0 : ℝ) 1 ≃ₜ A) {α β : ℝ} (hαβ : α ≤ β)
    (hsub : Icc α β ⊆ Icc (0 : ℝ) 1)
    (H : ↥(signedTubeDiamond ×ˢ Icc α β) ≃ₜ D)
    (G : signedTubeDiamond ≃ₜ J) (j : Bool) (τ : Icc (0 : ℝ) 1)
    (hkeep : ∀ x : signedTubeDiamond,
      (H ⟨(x, if j then β else α), x.property, by cases j <;> simp [hαβ]⟩ : E) = G x)
    (hcenter : (G ⟨(0, 0), signedTubeRadius_subset_diamond 0 false
      (left_mem_segment ℝ _ _)⟩ : E) = b τ)
    (haxis : ∀ t : Icc α β,
      (H ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _), t.property⟩ : E) = b ⟨t, hsub t.property⟩) :
    (if j then β else α) = (τ : ℝ) := by
  let t : Icc α β := ⟨if j then β else α, by cases j <;> simp [hαβ]⟩
  have he := (haxis t).symm.trans ((hkeep ⟨(0, 0),
    signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩).trans hcenter)
  exact congrArg Subtype.val (b.injective (Subtype.ext he))

end PoincareConjecture.M76.Dehn
