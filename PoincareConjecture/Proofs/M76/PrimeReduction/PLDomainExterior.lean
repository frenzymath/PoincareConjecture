import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isImage_interior_of_affine_nonneg (B : OpenPartialHomeomorph X E)
    {R : Set X} (ell : E →ᴬ[ℝ] ℝ) (v : E) (hv : ell.contLinear v = 1)
    (hhalf : ∀ x ∈ B.source, x ∈ R ↔ 0 ≤ ell (B x)) :
    B.IsImage (interior R) {z | 0 < ell z} := by
  have hlin : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have he : ell.toAffineMap.linear v = 1 := hv
    rw [h] at he
    exact zero_ne_one he
  have hopen : IsOpenMap (ell : E → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
    (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hlin))
  have hint : interior {z : E | 0 ≤ ell z} = {z : E | 0 < ell z} := by
    change interior ((ell : E → ℝ) ⁻¹' Ici 0) = (ell : E → ℝ) ⁻¹' Ioi 0
    rw [← hopen.preimage_interior_eq_interior_preimage ell.continuous, interior_Ici]
  have himage : B.IsImage R {z | 0 ≤ ell z} := fun {x} hx => (hhalf x hx).symm
  simpa only [hint] using himage.interior

end OpenPartialHomeomorph

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}

theorem PLDomain.frontier_closed_exterior (he : PLDomain e R) :
    frontier (interior R)ᶜ = frontier R := by
  rw [frontier_compl, frontier, he.closure_interior, interior_interior]
  exact he.closed.frontier_eq.symm

theorem PLDomain.closed_exterior (he : PLDomain e R) :
    PLDomain e (interior R)ᶜ := by
  refine ⟨he.cover, he.compatible, isOpen_interior.isClosed_compl, ?_⟩
  intro x hx
  obtain ⟨ell, v, B, hv, hxB, hzero, hPL, hhalf⟩ :=
    he.halfspace x (he.frontier_closed_exterior ▸ hx)
  have hi := B.isImage_interior_of_affine_nonneg ell v hv hhalf
  refine ⟨-ell, -v, B, ?_, hxB, ?_, hPL, ?_⟩
  · change -(ell.contLinear (-v)) = 1
    rw [map_neg, neg_neg, hv]
  · change -ell (B x) = 0
    rw [hzero, neg_zero]
  · intro y hy
    change y ∉ interior R ↔ 0 ≤ -ell (B y)
    rw [← hi.apply_mem_iff hy]
    change ¬0 < ell (B y) ↔ 0 ≤ -ell (B y)
    exact not_lt.trans neg_nonneg.symm

end PoincareConjecture.M76
