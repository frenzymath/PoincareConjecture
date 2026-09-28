import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli






theorem exists_original_signed_tube_branch_inverses
    {V E X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (C : Set X) (K : SimplicialComplex ℝ E)
    (F : X → E) (H : C ≃ₜ K.space) (g : E → C)
    (hH : ∀ x : C, (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hsep : ∀ x ∈ C, ∀ y : X, F x = F y → x = y)
    (P T : Fin 2 → SimplicialComplex ℝ V)
    (M : Fin 2 → SimplicialComplex ℝ E)
    (f : Fin 2 → V → X)
    (hinj : ∀ i, InjOn (f i) (P i).space)
    (hclip : ∀ i, (T i).space = (P i).space ∩ (f i) ⁻¹' C)
    (hPL : ∀ i, FinitePiecewiseAffineOn (F ∘ f i) (T i).space)
    (himage : ∀ i, (F ∘ f i) '' (T i).space = (M i).space)
    (hMK : ∀ i, M i ≤ K) :
    ∃ u : ∀ i : Fin 2, (M i).space ≃ₜ (T i).space,
      (∀ i, (u i).IsFinitePL ∧ (u i).symm.IsFinitePL) ∧
      (∀ i (z : (M i).space), f i (u i z) = (g z : X)) ∧
      (∀ i (z : (M i).space), F (f i (u i z)) = z) ∧
      (∀ i (x : (T i).space), ((u i).symm x : E) = F (f i x)) ∧
      ∀ i (z : (M i).space) (x : V),
        x ∈ (P i).space → f i x = (g z : X) → x = (u i z : V) := by
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    rw [← hH (g z)]
    have he : g z = H.symm ⟨z, hz⟩ := Subtype.ext (hg ⟨z, hz⟩)
    rw [he, H.apply_symm_apply]
  have hfi (i : Fin 2) : InjOn (F ∘ f i) (T i).space := by
    intro x hx y hy hxy
    have hx' := (hclip i).subset hx
    have hy' := (hclip i).subset hy
    exact hinj i hx'.1 hy'.1 (hsep (f i x) hx'.2 (f i y) hxy)
  have hex (i : Fin 2) : ∃ q : (T i).space ≃ₜ (M i).space,
      q.IsFinitePL ∧ ∀ x : (T i).space, (q x : E) = F (f i x) := by
    obtain ⟨q, hq, hval⟩ := (hPL i).exists_homeomorph_image (hfi i)
    let q' := q.trans (Homeomorph.setCongr (himage i))
    refine ⟨q', ?_, hval⟩
    obtain ⟨a, ha, haval⟩ := hq
    exact ⟨a, ha, haval⟩
  choose q hq hval using hex
  let u (i : Fin 2) : (M i).space ≃ₜ (T i).space := (q i).symm
  have hvalue (i : Fin 2) (z : (M i).space) : F (f i (u i z)) = z := by
    rw [← hval i, Homeomorph.apply_symm_apply]
  have horiginal (i : Fin 2) (z : (M i).space) : f i (u i z) = (g z : X) := by
    apply (hsep (g z) (g z).property (f i (u i z)) ?_).symm
    exact (hFg z (SimplicialComplex.space_subset_of_le (hMK i) z.property)).trans
      (hvalue i z).symm
  refine ⟨u, fun i => ⟨(hq i).symm, hq i⟩, horiginal, hvalue, hval, ?_⟩
  intro i z x hx hfx
  exact hinj i hx ((hclip i).subset (u i z).property).1
    (hfx.trans (horiginal i z).symm)

end PoincareConjecture.M76.Dehn.Annuli

