import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]






theorem IsFinitePL.exists_union_homeomorph_fixing_residual
    {S q : Set V} {T₀ T₁ R : Set E} {L₀ : S ≃ₜ T₀} (hL₀ : L₀.IsFinitePL)
    {L₁ : S ≃ₜ T₁} (hL₁ : L₁.IsFinitePL)
    (hcontact₀ : ∀ x : S, (L₀ x : E) ∈ R ↔ (x : V) ∈ q)
    (hcontact₁ : ∀ x : S, (L₁ x : E) ∈ R ↔ (x : V) ∈ q)
    (hcontact : ∀ x : S, (x : V) ∈ q → (L₀ x : E) = L₁ x)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R) :
    ∃ F : (T₀ ∪ R : Set E) ≃ₜ (T₁ ∪ R : Set E), F.IsFinitePL ∧
      (∀ x : R, (F ⟨x, Or.inr x.property⟩ : E) = x) ∧
      (∀ x : S, (F ⟨L₀ x, Or.inl (L₀ x).property⟩ : E) = L₁ x) ∧
      (∀ x : (T₀ ∪ R : Set E), (x : E) ∈ T₀ ↔ (F x : E) ∈ T₁) ∧
      ∀ x : (T₀ ∪ R : Set E), (x : E) ∈ R ↔ (F x : E) ∈ R := by
  let e := L₀.symm.trans L₁
  have he : e.IsFinitePL := hL₀.symm.trans hL₁
  have hR : (Homeomorph.refl R).IsFinitePL :=
    ⟨id, ⟨J, hJ, hJR, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩,
      fun _ => rfl⟩
  have hoverlap (x : T₀) : (x : E) ∈ R ↔ (e x : E) ∈ R := by
    have h₀ : (x : E) ∈ R ↔ (L₀.symm x : V) ∈ q := by
      simpa only [L₀.apply_symm_apply] using hcontact₀ (L₀.symm x)
    exact h₀.trans (hcontact₁ (L₀.symm x)).symm
  have hagree (x : E) (hx : x ∈ T₀) (hxR : x ∈ R) :
      (e ⟨x, hx⟩ : E) = (Homeomorph.refl R ⟨x, hxR⟩ : E) := by
    have h₀ : (L₀ (L₀.symm ⟨x, hx⟩) : E) = x :=
      congrArg Subtype.val (L₀.apply_symm_apply _)
    have hq : (L₀.symm ⟨x, hx⟩ : V) ∈ q :=
      (hcontact₀ _).mp (h₀.symm ▸ hxR)
    exact (hcontact _ hq).symm.trans h₀
  obtain ⟨F, hF, hF₀, hFR⟩ :=
    Homeomorph.exists_union_finitePL e (Homeomorph.refl R) he hR hoverlap hagree
  have hkeep (x : R) : F ⟨x, Or.inr x.property⟩ = ⟨x, Or.inr x.property⟩ :=
    Subtype.ext (hFR x)
  refine ⟨F, hF, hFR, ?_, ?_, ?_⟩
  · intro x
    simpa only [e, Homeomorph.trans_apply, L₀.symm_apply_apply] using hF₀ (L₀ x)
  · exact F.mem_subset_iff_of_extension e subset_union_left subset_union_left
      (fun x => Subtype.ext (hF₀ x))
  · exact F.mem_subset_iff_of_extension (Homeomorph.refl R)
      subset_union_right subset_union_right hkeep

end Homeomorph
