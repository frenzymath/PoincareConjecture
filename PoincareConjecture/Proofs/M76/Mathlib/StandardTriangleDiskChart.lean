import PoincareConjecture.Proofs.M76.Mathlib.TriangularCapDisks

set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

theorem exists_base_disk_chart : ∃ e : base ≃ₜ disk, e.IsFinitePL ∧
    (∀ x : base, (e x : (ℝ × ℝ) × ℝ) = ((x : ℝ × ℝ), 0)) ∧
    ∀ x : base, (x : ℝ × ℝ) ∈ frontier base ↔ (e x : (ℝ × ℝ) × ℝ) ∈ rim := by
  unfold disk
  have hf : FinitePiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) base :=
    finitePiecewiseAffineOn_roof.postcomp (ContinuousAffineMap.const ℝ ℝ 0)
  obtain ⟨e, he, hval⟩ := hf.graph.exists_homeomorph_image
    (fun _ _ _ _ h => congrArg Prod.fst h)
  refine ⟨e, he, hval, fun x => ?_⟩
  rw [hval, mem_rim, frontier_base]
  simp

theorem exists_triangle_disk_chart :
    ∃ e : convexHull ℝ (range TriangleDiskModel.rightTriangle) ≃ₜ disk,
      e.IsFinitePL ∧ ∀ x : convexHull ℝ (range TriangleDiskModel.rightTriangle), (x : ℝ × ℝ) ∈
        frontier (convexHull ℝ (range TriangleDiskModel.rightTriangle)) ↔
        (e x : (ℝ × ℝ) × ℝ) ∈ rim := by
  obtain ⟨e, he, _, hb⟩ := exists_base_disk_chart
  let G := (Homeomorph.setCongr base_eq_triangle.symm).trans
    (e.trans (Homeomorph.setCongr (rfl : disk = disk)))
  refine ⟨G, he.setCongr base_eq_triangle rfl, fun x => ?_⟩
  change (x : ℝ × ℝ) ∈ frontier (convexHull ℝ (range TriangleDiskModel.rightTriangle)) ↔
    (e ⟨x, base_eq_triangle.symm ▸ x.property⟩ : (ℝ × ℝ) × ℝ) ∈ rim
  rw [← congrArg frontier base_eq_triangle]
  exact hb ⟨x, base_eq_triangle.symm ▸ x.property⟩

end TriangularRoofModel
