import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalHalfBlocks

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem isFinitePLBallPair_closedStar_chart_halfspaces
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices) {f : E → (Fin 3 → ℝ)}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hinj : InjOn f (K.closedStar p).space)
    (hzero : f p 0 = 0)
    (hint : f p ∈ interior (f '' (K.closedStar p).space)) :
    IsFinitePLBallPair (Fin 3 → ℝ)
      ((K.closedStar p).space ∩ {x | 0 ≤ f x 0})
      (((K.link p).space ∩ {x | 0 ≤ f x 0}) ∪
        ((K.closedStar p).space ∩ {x | f x 0 = 0})) ∧
    IsFinitePLBallPair (Fin 3 → ℝ)
      ((K.closedStar p).space ∩ {x | f x 0 ≤ 0})
      (((K.link p).space ∩ {x | f x 0 ≤ 0}) ∪
        ((K.closedStar p).space ∩ {x | f x 0 = 0})) := by
  classical
  let a : (Fin 3 → ℝ) ≃ᴬ[ℝ] (Fin 3 → ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (Fin 3 → ℝ) (-f p)
  let g : E → (Fin 3 → ℝ) := fun x => a (f x)
  have hg : (K.closedStar p).AffineOnFaces g := hf.postcomp a.toContinuousAffineMap
  have hginj : InjOn g (K.closedStar p).space := fun _ hx _ hy h =>
    hinj hx hy (a.injective h)
  have hgp : g p = 0 := by
    change -f p + f p = 0
    exact neg_add_cancel _
  have hgheight (x : E) : g x 0 = f x 0 := by
    change -(f p 0) + f x 0 = f x 0
    rw [hzero, neg_zero, zero_add]
  have hgint : (0 : Fin 3 → ℝ) ∈ interior (g '' (K.closedStar p).space) := by
    change (0 : Fin 3 → ℝ) ∈ interior ((a ∘ f) '' (K.closedStar p).space)
    rw [image_comp]
    change (0 : Fin 3 → ℝ) ∈ interior (a.toHomeomorph '' (f '' (K.closedStar p).space))
    rw [← a.toHomeomorph.image_interior]
    exact ⟨f p, hint, hgp⟩
  have hpstar : p ∈ (K.closedStar p).vertices := by
    change {p} ∈ K.faces ∧ insert p {p} ∈ K.faces
    exact ⟨hp, by
      rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
      exact hp⟩
  have hstar : (K.closedStar p).closedStar p = K.closedStar p := by
    ext s
    change ((s ∈ K.faces ∧ insert p s ∈ K.faces) ∧
      insert p s ∈ K.faces ∧ insert p (insert p s) ∈ K.faces) ↔
      s ∈ K.faces ∧ insert p s ∈ K.faces
    simp only [Finset.insert_idem, and_self, and_assoc]
  have hlink : (K.closedStar p).link p = K.link p := by
    ext s
    change ((s ∈ K.faces ∧ insert p s ∈ K.faces) ∧ p ∉ s ∧
      insert p s ∈ K.faces ∧ insert p (insert p s) ∈ K.faces) ↔
      s ∈ K.faces ∧ p ∉ s ∧ insert p s ∈ K.faces
    simp only [Finset.insert_idem]
    tauto
  have hlinksub : (K.link p).space ⊆ (K.closedStar p).space :=
    space_subset_of_le (K.link_le_closedStar p)
  let L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  have hpos := hg.isFinitePLBallPair_conical_halfspaces
    (finite_closedStar_faces hK p) hginj hpstar hstar hgp hgint
    (ContinuousLinearEquiv.refl ℝ _) (fun _ : Unit => L)
    (by exact ⟨fun _ => 1, fun _ => by norm_num [L]⟩)
  have hneg := hg.isFinitePLBallPair_conical_halfspaces
    (finite_closedStar_faces hK p) hginj hpstar hstar hgp hgint
    (ContinuousLinearEquiv.refl ℝ _) (fun _ : Unit => -L)
    (by exact ⟨fun _ => -1, fun _ => by norm_num [L]⟩)
  simp only [hlink, LinearMap.neg_apply, neg_nonneg, neg_eq_zero, L,
    LinearMap.proj_apply, hgheight, forall_const, exists_const] at hpos hneg
  have hrim (side : E → Prop) (hz : ∀ x, f x 0 = 0 → side x) :
      {x | x ∈ (K.closedStar p).space ∧ side x ∧
        (x ∈ (K.link p).space ∨ f x 0 = 0)} =
      ((K.link p).space ∩ {x | side x}) ∪
        ((K.closedStar p).space ∩ {x | f x 0 = 0}) := by
    ext x
    constructor
    · rintro ⟨hx, hs, hl | he⟩
      · exact Or.inl ⟨hl, hs⟩
      · exact Or.inr ⟨hx, he⟩
    · rintro (⟨hl, hs⟩ | ⟨hx, he⟩)
      · exact ⟨hlinksub hl, hs, Or.inl hl⟩
      · exact ⟨hx, hz x he, Or.inr he⟩
  rw [hrim (fun x => 0 ≤ f x 0) (fun x hx => by rw [hx])] at hpos
  rw [hrim (fun x => f x 0 ≤ 0) (fun x hx => by rw [hx])] at hneg
  exact ⟨hpos, hneg⟩

end Geometry.SimplicialComplex
