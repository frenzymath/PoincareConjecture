import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGraphs










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePL.exists_pointed_upperBoundary_complex
    {B T : Set E} {upper : E → ℝ} (hupperPL : FinitePiecewiseAffineOn upper B)
    (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    {q : E} (hq : q ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x) :
    ∃ (f : E → E) (Q : SimplicialComplex ℝ E), FinitePiecewiseAffineOn f B ∧
      InjOn f B ∧
      (∀ x (hx : x ∈ B),
        f x = (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩ : E)) ∧
      Q.faces.Finite ∧ Q.space = f '' B ∧ Q.space ⊆ T ∧
      (∀ x ∈ B, A (f x) = upper x) ∧ Q.space ∩ {x | A x = 0} = {q} := by
  obtain ⟨g, hg, hgval⟩ := hC
  let f : E → E := fun x => g (x, upper x)
  have hfval (x : E) (hx : x ∈ B) :
      f x = (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩ : E) :=
    (hgval ⟨(x, upper x), hx, hupper x hx, le_rfl⟩).symm
  have hf : FinitePiecewiseAffineOn f B :=
    hg.comp hupperPL.graph (fun x hx => ⟨hx, hupper x hx, le_rfl⟩)
  have hfinj : InjOn f B := by
    intro x hx y hy hxy
    rw [hfval x hx, hfval y hy] at hxy
    exact congrArg Prod.fst (congrArg Subtype.val (C.injective (Subtype.ext hxy)))
  have hfheight (x : E) (hx : x ∈ B) : A (f x) = upper x := by
    rw [hfval x hx]
    exact hheight _
  have hfq : f q = q := (hfval q hq).trans (hbottom _ hqzero)
  obtain ⟨J, hJ, hJs, hfaces⟩ := hf
  have hinjJ : InjOn f J.space := hJs.symm ▸ hfinj
  let Q := hfaces.embeddedImage hinjJ
  have hQspace : Q.space = f '' B := by
    rw [hfaces.embeddedImage_space hinjJ, hJs]
  refine ⟨f, Q, ⟨J, hJ, hJs, hfaces⟩, hfinj, hfval,
    hfaces.embeddedImage_finite hinjJ hJ, hQspace, ?_, hfheight, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hQspace ▸ hy
    rw [hfval x hx]
    exact (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩).property
  · ext y
    constructor
    · rintro ⟨hy, hyzero⟩
      obtain ⟨x, hx, rfl⟩ := hQspace ▸ hy
      have hux : upper x = 0 := (hfheight x hx).symm.trans hyzero
      have hxq : x = q := by
        by_contra hxq
        exact (hpos x hx hxq).ne' hux
      exact mem_singleton_iff.mpr (hxq ▸ hfq)
    · intro hy
      have hyq : y = q := mem_singleton_iff.mp hy
      subst y
      refine ⟨hQspace.symm ▸ (show q ∈ f '' B from ⟨q, hq, hfq⟩), ?_⟩
      exact hfq ▸ (hfheight q hq).trans hqzero

end Homeomorph
