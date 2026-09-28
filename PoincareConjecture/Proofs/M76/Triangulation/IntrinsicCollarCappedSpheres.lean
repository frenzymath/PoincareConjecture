import PoincareConjecture.Proofs.M76.Triangulation.IntrinsicCappedSpheres
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCutSide

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Geometry

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [Finite ι] [Nonempty ι]

theorem AlexanderCollarSlab.exists_intrinsic_capped_spheres
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β) (hdim : Module.finrank ℝ E = 3)
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hpair : Pairwise (fun i j =>
      (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    (hsection : S ∩ {x | A x = 0} = ⋃ i, (P i).boundary ℝ)
    {C : Set F} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hne : (interior C).Nonempty) (hdimC : Module.finrank ℝ F = 3)
    (e : S ≃ₜ frontier C) (he : e.IsFinitePL) :
    ∃ (j : ι) (d s₀ s₁ : Set E) (N : SimplicialComplex ℝ E),
      IsFinitePLBallPair (ℝ × ℝ) d ((P j).boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s₀ ((P j).boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s₁ ((P j).boundary ℝ) ∧
      d ⊆ {x | A x = 0} ∧ d ∩ S = (P j).boundary ℝ ∧
      s₀ ∪ s₁ = S ∧ s₀ ∩ s₁ = (P j).boundary ℝ ∧
      s₀ ∩ d = (P j).boundary ℝ ∧ s₁ ∩ d = (P j).boundary ℝ ∧
      N.faces.Finite ∧ S ∩ {x | A x = 0} = (P j).boundary ℝ ∪ N.space ∧
      d ∩ N.space ⊆ {q} ∧
      N.space = ⋃ i : {i : ι // i ≠ j}, (P i.val).boundary ℝ ∧
      ∃ (e₀ : (s₀ ∪ d : Set E) ≃ₜ frontier (halfBall 1))
        (e₁ : (s₁ ∪ d : Set E) ≃ₜ frontier (halfBall 1)),
        e₀.IsFinitePL ∧ e₁.IsFinitePL := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨ec⟩ := (P i).nonempty_boundary_homeomorph_circle (hP i).2 (hP i).1
  obtain ⟨x, hxP, hxq⟩ :=
    (isConnected_sdiff_singleton_of_homeomorph_circle ((P i).boundary ℝ) ec q).nonempty
  have hx : x ∈ S ∩ {x | A x = 0} :=
    hsection.symm.subset (mem_iUnion.mpr ⟨i, hxP⟩)
  have hxne : x ≠ q := fun h => hxq (mem_singleton_iff.mpr h)
  obtain ⟨v, hv⟩ := M.exists_unit_height_direction hx hxne
  have hA : A.linear ≠ 0 := by
    intro hz
    rw [hz, LinearMap.zero_apply] at hv
    exact zero_ne_one hv
  let p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)} :=
    ⟨(x, M.upper x), hx, (M.upper_bounds x hx).1, le_rfl⟩
  have hpS : (M.chart p : E) ∈ S :=
    (M.cover.subset (Or.inl (M.chart p).property)).1
  have hpos : 0 < A (M.chart p) := by
    rw [M.height]
    exact M.upper_pos x hx hxne
  exact Polygon.exists_intrinsic_capped_spheres hdim A hA n P hP q hpair S hsection
    ⟨M.chart p, hpS, hpos.ne'⟩ hC hcv hne hdimC e he

end Geometry
