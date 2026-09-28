import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import Mathlib.Analysis.Normed.Module.Ball.Pointwise











set_option autoImplicit false

open Set Metric Geometry
open scoped Pointwise

namespace Geometry.SimplicialComplex




theorem exists_finite_coordinate_closedBall
    {ι : Type*} [Fintype ι] (z : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ J : SimplicialComplex ℝ (ι → ℝ),
      J.faces.Finite ∧ J.space = closedBall z r := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := ι)
  let A : (ι → ℝ) →ᴬ[ℝ] (ι → ℝ) :=
    ContinuousAffineMap.const ℝ (ι → ℝ) z + r • ContinuousAffineMap.id ℝ (ι → ℝ)
  obtain ⟨J, hJ, hJs, _⟩ := (K.affineOnFaces_affine A).exists_finite_triangulation_image hK
  refine ⟨J, hJ, hJs.trans ?_⟩
  rw [hKs]
  have himage : A '' closedBall (0 : ι → ℝ) 1 =
      (fun y => z + y) '' ((fun y : ι → ℝ => r • y) '' closedBall 0 1) := by
    rw [image_image]
    rfl
  rw [himage]
  change z +ᵥ r • closedBall (0 : ι → ℝ) 1 = closedBall z r
  exact affinity_unitClosedBall hr z





theorem exists_nested_finite_coordinate_cubes
    {ι : Type*} [Fintype ι] {O : Set (ι → ℝ)} (hO : IsOpen O)
    {z : ι → ℝ} (hz : z ∈ O) :
    ∃ (r : ℝ) (J : SimplicialComplex ℝ (ι → ℝ)),
      0 < r ∧ J.faces.Finite ∧ J.space = closedBall z (3 * r) ∧
      J.space ⊆ O ∧ closure (ball z r) ⊆ ball z (2 * r) ∧
      closure (ball z (2 * r)) ⊆ interior J.space := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO z hz
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have h3r : 0 ≤ 3 * r := by positivity
  obtain ⟨J, hJ, hJs⟩ := exists_finite_coordinate_closedBall z h3r
  have hclosure (s : ℝ) : closure (ball z s) ⊆ closedBall z s :=
    closure_minimal ball_subset_closedBall isClosed_closedBall
  refine ⟨r, J, hr, hJ, hJs, ?_, ?_, ?_⟩
  · rw [hJs]
    intro y hy
    apply hball
    exact (mem_closedBall.mp hy).trans_lt (by dsimp [r]; linarith)
  · intro y hy
    exact (mem_closedBall.mp (hclosure r hy)).trans_lt (by linarith)
  · rw [hJs]
    intro y hy
    apply ball_subset_interior_closedBall
    exact (mem_closedBall.mp (hclosure (2 * r) hy)).trans_lt (by linarith)

end Geometry.SimplicialComplex
