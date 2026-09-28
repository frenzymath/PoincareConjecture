import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]




theorem PLDomain.exists_local_region_chart
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (x : R) :
    ∃ B : OpenPartialHomeomorph X V3,
      (x : X) ∈ B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ell (B x) = 0 ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) := by
  by_cases hxf : (x : X) ∈ frontier R
  · obtain ⟨ell, v, B, hv, hxB, hzero, hcompat, hhalf⟩ := he.halfspace x hxf
    exact ⟨B, hxB, hcompat, Or.inr ⟨ell, v, hv, hzero, hhalf⟩⟩
  · have hxi : (x : X) ∈ interior R := by
      by_contra hnot
      exact hxf (he.closed.frontier_eq.symm.subset ⟨x.property, hnot⟩)
    obtain ⟨i, hi⟩ := he.cover x
    let B := (e i).restrOpen (interior R) isOpen_interior
    refine ⟨B, ⟨hi, hxi⟩, ?_, Or.inl (fun _ hy => interior_subset hy.2)⟩
    intro j
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (he.compatible j i)).mono
      ((e j).symm.trans B).open_source (fun _ hy => ⟨hy.1, hy.2.1⟩)

end PoincareConjecture.M76
