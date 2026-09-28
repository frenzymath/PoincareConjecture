import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGluing










set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem FinitePiecewiseAffineOn.iUnion {ι : Type*} [Finite ι]
    {f : E → F} {s : ι → Set E} (hs : ∀ i, FinitePiecewiseAffineOn f (s i)) :
    FinitePiecewiseAffineOn f (⋃ i, s i) := by
  choose J hJ hspace hfaces using hs
  obtain ⟨K, hK, hKspace, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion J hJ
  have hfK := finitePiecewiseAffineOn_of_finite_cover K hK J hJ hfaces
    (fun _ hx => hKspace ▸ hx)
  simpa only [hKspace, hspace] using hfK




theorem finitePiecewiseAffineOn_union {f : E → F} {s u : Set E}
    (hs : FinitePiecewiseAffineOn f s) (hu : FinitePiecewiseAffineOn f u) :
    FinitePiecewiseAffineOn f (s ∪ u) := by
  let S : Bool → Set E := fun b => if b then s else u
  have hS (b : Bool) : FinitePiecewiseAffineOn f (S b) := by cases b <;> assumption
  have hcover : (⋃ b, S b) = s ∪ u := by
    ext x
    simp only [mem_iUnion, Bool.exists_bool, S, Bool.false_eq_true, if_false, if_true,
      mem_union]
    exact or_comm
  rw [← hcover]
  exact FinitePiecewiseAffineOn.iUnion hS

end Geometry

namespace Homeomorph





theorem exists_union_finitePL {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s u : Set E} {t v : Set F} (e : s ≃ₜ t) (d : u ≃ₜ v)
    (he : e.IsFinitePL) (hd : d.IsFinitePL)
    (hoverlap : ∀ x : s, (x : E) ∈ u ↔ (e x : F) ∈ v)
    (hagree : ∀ (x : E) (hxs : x ∈ s) (hxu : x ∈ u),
      (e ⟨x, hxs⟩ : F) = (d ⟨x, hxu⟩ : F)) :
    ∃ H : (s ∪ u : Set E) ≃ₜ (t ∪ v : Set F), H.IsFinitePL ∧
      (∀ x : s, (H ⟨x, Or.inl x.property⟩ : F) = e x) ∧
      (∀ x : u, (H ⟨x, Or.inr x.property⟩ : F) = d x) := by
  have hecopy := he
  have hdcopy := hd
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hecopy
  obtain ⟨_, ⟨J, hJ, hJu, _⟩, _⟩ := hdcopy
  obtain ⟨L, hL, hspace⟩ := K.exists_finite_triangulation_union J hK hJ
  rw [hKs, hJu] at hspace
  exact exists_union_of_isFinitePL e d he hd L hL hspace hoverlap hagree

end Homeomorph
