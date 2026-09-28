import PoincareConjecture.Proofs.M76.Mathlib.CollarLevelResidualGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages











set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]






theorem FinitePiecewiseAffineOn.exists_level_replacement_fixing_residual
    {f₀ f₁ : V → E} {S₀ S₁ u j w q : Set V} {a R : Set E}
    (hf₀ : FinitePiecewiseAffineOn f₀ S₀) (hf₁ : FinitePiecewiseAffineOn f₁ S₁)
    (hinj₀ : InjOn f₀ S₀) (hinj₁ : InjOn f₁ S₁)
    (hS₀ : S₀ = u ∪ w) (hS₁ : S₁ = j ∪ w)
    (huw : Disjoint u w) (hjw : Disjoint j w) (haw : Disjoint a (f₁ '' w))
    (hu : IsFinitePLBallPair ℝ u q)
    (ha : IsFinitePLBallPair ℝ (a ∪ f₁ '' j) (f₁ '' q))
    (hcontact₀ : (f₀ '' u) ∩ R = f₀ '' q)
    (hcontact₁ : (a ∪ f₁ '' j) ∩ R = f₁ '' q)
    (hq : EqOn f₀ f₁ q)
    (hwcontact : ∀ x ∈ w, f₀ x ∈ R ↔ f₁ x ∈ R)
    (hwfixed : ∀ x ∈ w, f₀ x ∈ R → f₀ x = f₁ x)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite) (hKw : K.space = w)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R) :
    ∃ F : ((f₀ '' S₀) ∪ R : Set E) ≃ₜ ((a ∪ f₁ '' S₁) ∪ R : Set E),
      F.IsFinitePL ∧
      (∀ x : R, (F ⟨x, Or.inr x.property⟩ : E) = x) ∧
      (∀ x : w, (F ⟨f₀ x, Or.inl
        ⟨x, hS₀.symm.subset (Or.inr x.property), rfl⟩⟩ : E) = f₁ x) ∧
      ∀ x : ((f₀ '' S₀) ∪ R : Set E),
        (x : E) ∈ f₀ '' u ↔ (F x : E) ∈ a ∪ f₁ '' j := by
  have hu₀ : u ⊆ S₀ := subset_union_left.trans hS₀.symm.subset
  have hw₀ : w ⊆ S₀ := subset_union_right.trans hS₀.symm.subset
  have hj₁ : j ⊆ S₁ := subset_union_left.trans hS₁.symm.subset
  have hw₁ : w ⊆ S₁ := subset_union_right.trans hS₁.symm.subset
  have hfw₀ : FinitePiecewiseAffineOn f₀ w := by
    rw [← hKw]
    exact hf₀.restrict K hK (hKw.subset.trans hw₀)
  have hfw₁ : FinitePiecewiseAffineOn f₁ w := by
    rw [← hKw]
    exact hf₁.restrict K hK (hKw.subset.trans hw₁)
  obtain ⟨e₀, he₀, he₀val⟩ := hfw₀.exists_homeomorph_image (hinj₀.mono hw₀)
  obtain ⟨e₁, he₁, he₁val⟩ := hfw₁.exists_homeomorph_image (hinj₁.mono hw₁)
  have hc₀ (x : w) : (e₀ x : E) ∈ R ↔ f₀ x ∈ R := by rw [he₀val]
  have hc₁ (x : w) : (e₁ x : E) ∈ R ↔ f₀ x ∈ R := by
    rw [he₁val]
    exact (hwcontact x x.property).symm
  have heq (x : w) (hx : f₀ x ∈ R) : (e₀ x : E) = e₁ x :=
    (he₀val x).trans ((hwfixed x x.property hx).trans (he₁val x).symm)
  obtain ⟨D, hD, hDR, hDw, _, _⟩ :=
    he₀.exists_union_homeomorph_fixing_residual (q := {x | f₀ x ∈ R})
      he₁ hc₀ hc₁ heq J hJ hJR
  have hDwval (x : w) :
      (D ⟨f₀ x, Or.inl ⟨x, x.property, rfl⟩⟩ : E) = f₁ x := by
    simpa only [he₀val, he₁val] using hDw x
  have hdisj₀ : Disjoint (f₀ '' u) (f₀ '' w) :=
    disjoint_image_image fun x hx y hy hxy =>
      disjoint_left.mp huw hx ((hinj₀ (hu₀ hx) (hw₀ hy) hxy).symm ▸ hy)
  have hdisj₁ : Disjoint (f₁ '' j) (f₁ '' w) :=
    disjoint_image_image fun x hx y hy hxy =>
      disjoint_left.mp hjw hx ((hinj₁ (hj₁ hx) (hw₁ hy) hxy).symm ▸ hy)
  have hdisjA : Disjoint (a ∪ f₁ '' j) (f₁ '' w) := disjoint_union_left.mpr ⟨haw, hdisj₁⟩
  have himage : f₀ '' q = f₁ '' q := image_congr hq
  have hA₀ : IsFinitePLBallPair ℝ (f₀ '' u) (f₀ '' q) :=
    hu.image_of_subset hf₀ hu₀ hinj₀
  have hA₁ : IsFinitePLBallPair ℝ (a ∪ f₁ '' j) (f₀ '' q) := himage.symm ▸ ha
  have hinter₀ : (f₀ '' u) ∩ ((f₀ '' w) ∪ R) = f₀ '' q := by
    rw [inter_union_distrib_left, hdisj₀.inter_eq, empty_union, hcontact₀]
  have hinter₁ : (a ∪ f₁ '' j) ∩ ((f₁ '' w) ∪ R) = f₀ '' q := by
    rw [inter_union_distrib_left, hdisjA.inter_eq, empty_union, hcontact₁, himage]
  have hqR : f₀ '' q ⊆ R := hcontact₀.symm.subset.trans inter_subset_right
  have hq₀ : f₀ '' q ⊆ (f₀ '' w) ∪ R := hqR.trans subset_union_right
  have hq₁ : f₀ '' q ⊆ (f₁ '' w) ∪ R := hqR.trans subset_union_right
  have hmem (x : ((f₀ '' w) ∪ R : Set E)) :
      (x : E) ∈ f₀ '' q ↔ (D x : E) ∈ f₀ '' q :=
    D.mem_subset_iff_of_extension (Homeomorph.refl (f₀ '' q)) hq₀ hq₁
      (fun y => Subtype.ext (hDR ⟨y, hqR y.property⟩)) x
  obtain ⟨G, hG, hkeep, hGu, _⟩ :=
    hA₀.exists_union_homeomorph_of_boundary_piece hA₁ hinter₀ hinter₁ D hD hmem
  have hsource : (f₀ '' u) ∪ ((f₀ '' w) ∪ R) = (f₀ '' S₀) ∪ R := by
    rw [hS₀, image_union, union_assoc]
  have htarget : (a ∪ f₁ '' j) ∪ ((f₁ '' w) ∪ R) = (a ∪ f₁ '' S₁) ∪ R := by
    simp only [hS₁, image_union, union_assoc]
  let F := (Homeomorph.setCongr hsource.symm).trans
    (G.trans (Homeomorph.setCongr htarget))
  refine ⟨F, hG.setCongr hsource htarget, ?_, ?_, ?_⟩
  · intro x
    exact (congrArg Subtype.val (hkeep ⟨x, Or.inr x.property⟩)).trans (hDR x)
  · intro x
    exact (congrArg Subtype.val (hkeep ⟨f₀ x, Or.inl ⟨x, x.property, rfl⟩⟩)).trans
      (hDwval x)
  · intro x
    exact hGu ⟨x, hsource.symm ▸ x.property⟩

end Geometry
