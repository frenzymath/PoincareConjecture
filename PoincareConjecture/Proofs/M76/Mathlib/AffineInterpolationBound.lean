import PoincareConjecture.Proofs.M76.Mathlib.AffineOnFaces
import Mathlib.Tactic.Module










set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}





theorem AffineOnFaces.norm_sub_le_of_vertex_bound (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ convexHull ℝ (s : Set E))
    (z : F) {B : ℝ} (hB : ∀ v ∈ s, ‖f v - z‖ ≤ B) : ‖f x - z‖ ≤ B := by
  obtain ⟨a, ha⟩ := hf s hs
  obtain ⟨w, hw, hsum, hval⟩ := Finset.mem_convexHull'.mp hx
  have hmap := Finset.map_affineCombination (s := s) id w hsum a.toAffineMap
  simp only [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
    id_eq, Function.comp_apply] at hmap
  rw [hval] at hmap
  change a x = ∑ v ∈ s, w v • a v at hmap
  have hfx : f x = ∑ v ∈ s, w v • f v := by
    rw [ha hx, hmap]
    apply Finset.sum_congr rfl
    intro v hv
    rw [ha (subset_convexHull ℝ _ hv)]
  have he : f x - z = ∑ v ∈ s, w v • (f v - z) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul, hfx]
  rw [he]
  calc
    ‖∑ v ∈ s, w v • (f v - z)‖ ≤ ∑ v ∈ s, ‖w v • (f v - z)‖ := norm_sum_le _ _
    _ = ∑ v ∈ s, w v * ‖f v - z‖ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw v hv)]
    _ ≤ ∑ v ∈ s, w v * B :=
      Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (hB v hv) (hw v hv)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

end Geometry.SimplicialComplex
