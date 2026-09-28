import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedQuarterPrismBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondRadiusMaps

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_signed_diamond_quarter_restriction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s Q : Set E} (G : signedTubeDiamond ≃ₜ s) (hG : G.IsFinitePL)
    (eps delta : Bool) (hQ : Q ⊆ s)
    (hmem : ∀ x : signedTubeDiamond,
      (x : P2) ∈ signedTubeQuarter eps delta ↔ (G x : E) ∈ Q) :
    ∃ e : signedTubeQuarter eps delta ≃ₜ Q, e.IsFinitePL ∧
      ∀ x, (e x : E) =
        G ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ := by
  have hsrc : signedTubeQuarter eps delta ⊆ signedTubeDiamond :=
    fun _ hx => mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, hx⟩⟩
  let e := G.restrictSubsets hsrc hQ hmem
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    signedTube_quarter_ball eps delta
  exact ⟨e, hG.restrictSubsets hsrc hQ hmem K hK hKs, fun _ => rfl⟩

noncomputable def signedTubeQuarterEndProjection (eps delta : Bool) (t : ℝ) :
    ↥(signedTubeQuarter eps delta ×ˢ {t}) ≃ₜ signedTubeQuarter eps delta :=
  (Homeomorph.Set.prod _ _).trans (Homeomorph.prodUnique _ _)

theorem signedTubeQuarterEndProjection_isFinitePL (eps delta : Bool) (t : ℝ) :
    (signedTubeQuarterEndProjection eps delta t).IsFinitePL := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    (signedTube_quarter_ball eps delta).prod_singleton t
  exact ⟨Prod.fst, ⟨K, hK, hKs,
    K.affineOnFaces_affine (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap⟩,
      fun _ => rfl⟩

theorem exists_signed_sector_radial_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (eps delta : Bool) (α β : ℝ) {F0 F1 Z : Set E}
    (f0 : ↥(signedTubeRadius 0 delta ×ˢ Icc α β) ≃ₜ F0)
    (f1 : ↥(signedTubeRadius 1 eps ×ˢ Icc α β) ≃ₜ F1)
    (hf0 : f0.IsFinitePL) (hf1 : f1.IsFinitePL)
    (hinter : F0 ∩ F1 = Z) (z : Icc α β → E)
    (haxis : ∀ x : ↥(signedTubeRadius 0 delta ×ˢ Icc α β),
      (x : P2 × ℝ).1 = (0, 0) ↔ (f0 x : E) ∈ Z)
    (hz0 : ∀ t : Icc α β,
      (f0 ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) = z t)
    (hz1 : ∀ t : Icc α β,
      (f1 ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) = z t) :
    ∃ f : ↥(signedTubeRadialRim eps delta ×ˢ Icc α β) ≃ₜ ↥(F0 ∪ F1),
      f.IsFinitePL ∧
      (∀ x : ↥(signedTubeRadius 0 delta ×ˢ Icc α β),
        (f ⟨x, Or.inl x.property.1, x.property.2⟩ : E) = f0 x) ∧
      ∀ x : ↥(signedTubeRadius 1 eps ×ˢ Icc α β),
        (f ⟨x, Or.inr x.property.1, x.property.2⟩ : E) = f1 x := by
  have hoverlap (x : ↥(signedTubeRadius 0 delta ×ˢ Icc α β)) :
      (x : P2 × ℝ) ∈ signedTubeRadius 1 eps ×ˢ Icc α β ↔ (f0 x : E) ∈ F1 := by
    have hs : (x : P2 × ℝ).1 ∈ signedTubeRadius 1 eps ↔
        (x : P2 × ℝ).1 = (0, 0) := by
      rw [← mem_singleton_iff, ← signedTube_cross_radius_inter eps delta]
      simp only [mem_inter_iff, x.property.1, true_and]
    have ht : (f0 x : E) ∈ F1 ↔ (f0 x : E) ∈ Z := by
      rw [← hinter]
      simp only [mem_inter_iff, (f0 x).property, true_and]
    simpa only [mem_prod, x.property.2, and_true] using hs.trans ((haxis x).trans ht.symm)
  have hagree (x : P2 × ℝ) (hx0 : x ∈ signedTubeRadius 0 delta ×ˢ Icc α β)
      (hx1 : x ∈ signedTubeRadius 1 eps ×ˢ Icc α β) :
      (f0 ⟨x, hx0⟩ : E) = f1 ⟨x, hx1⟩ := by
    have hx : x.1 = (0, 0) :=
      (signedTube_cross_radius_inter eps delta).subset ⟨hx0.1, hx1.1⟩
    have heq : x = ((0, 0), x.2) := Prod.ext hx rfl
    have he0 : (⟨x, hx0⟩ : ↥(signedTubeRadius 0 delta ×ˢ Icc α β)) =
        ⟨((0, 0), x.2), left_mem_segment ℝ _ _, hx0.2⟩ := Subtype.ext heq
    have he1 : (⟨x, hx1⟩ : ↥(signedTubeRadius 1 eps ×ˢ Icc α β)) =
        ⟨((0, 0), x.2), left_mem_segment ℝ _ _, hx0.2⟩ := Subtype.ext heq
    rw [he0, he1]
    exact (hz0 ⟨x.2, hx0.2⟩).trans (hz1 ⟨x.2, hx0.2⟩).symm
  obtain ⟨f, hf, hkeep0, hkeep1⟩ :=
    Homeomorph.exists_union_finitePL f0 f1 hf0 hf1 hoverlap hagree
  have hsource : (signedTubeRadius 0 delta ×ˢ Icc α β) ∪
      (signedTubeRadius 1 eps ×ˢ Icc α β) = signedTubeRadialRim eps delta ×ˢ Icc α β := by
    ext x
    simp only [signedTubeRadialRim, mem_union, mem_prod]
    tauto
  let f' := (Homeomorph.setCongr hsource.symm).trans f
  exact ⟨f', hf.setCongr hsource rfl, hkeep0, hkeep1⟩

end PoincareConjecture.M76.Dehn
