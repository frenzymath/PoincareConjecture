import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine
import Mathlib.Data.Set.UnionLift










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem exists_finitePL_affineLevel_pasting (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) (c : ℝ)
    {ι : Type*} [Finite ι] (T : ι → Finset E)
    (hT : ∀ i, AffineIndependent ℝ ((↑) : T i → E))
    (hcover : (⋃ i, convexHull ℝ (T i : Set E) ∩ {x | A x = c}) =
      K.space ∩ {x | A x = c})
    (a : ι → E →ᴬ[ℝ] F)
    (hagree : ∀ i j x, x ∈ convexHull ℝ (T i : Set E) ∩ {x | A x = c} →
      x ∈ convexHull ℝ (T j : Set E) ∩ {x | A x = c} → a i x = a j x) :
    ∃ f : E → F, FinitePiecewiseAffineOn f (K.space ∩ {x | A x = c}) ∧
      ∀ i, EqOn f (a i) (convexHull ℝ (T i : Set E) ∩ {x | A x = c}) := by
  classical
  let B : ι → Set E := fun i => convexHull ℝ (T i : Set E) ∩ {x | A x = c}
  let g := Set.iUnionLift B (fun i x => a i x) hagree (⋃ i, B i) Subset.rfl
  let f : E → F := fun x => if hx : x ∈ ⋃ i, B i then g ⟨x, hx⟩ else 0
  have hfval (i : ι) (x : E) (hx : x ∈ B i) : f x = a i x := by
    have hxB : x ∈ ⋃ i, B i := mem_iUnion.mpr ⟨i, hx⟩
    dsimp only [f]
    rw [dif_pos hxB]
    exact Set.iUnionLift_of_mem ⟨x, hxB⟩ hx
  obtain ⟨J, hJ, hJspace⟩ := K.exists_finite_affineLevel_complex hK A c
  let N := hJ.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ J.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hJ.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  have hcov (x : E) (hx : x ∈ J.space) : ∃ i, x ∈ convexHull ℝ (T i : Set E) := by
    have hxB : x ∈ ⋃ i, B i := hcover.symm ▸ (hJspace ▸ hx)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxB
    exact ⟨i, hi.1⟩
  obtain ⟨R, hR, hRJ, _, href⟩ :=
    J.exists_subdivision_refines_finite_cover hJ hN T hT hcov
  have hRspace := hRJ.space_eq.trans hJspace
  refine ⟨f, ⟨R, hR, hRspace, ?_⟩, fun i x hx => hfval i x hx⟩
  intro s hs
  obtain ⟨i, hi⟩ := href s hs
  refine ⟨a i, fun x hx => ?_⟩
  have hxlevel : x ∈ K.space ∩ {x | A x = c} :=
    hRspace ▸ R.convexHull_subset_space hs hx
  exact hfval i x ⟨hi hx, hxlevel.2⟩

end Geometry.SimplicialComplex
