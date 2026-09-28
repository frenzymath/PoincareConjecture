import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3}

theorem exists_original_chart_ball (i : ι) (x : X) (hx : x ∈ (e i).source)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ D : Set X, IsCompact D ∧ x ∈ D ∧ D ⊆ U ∧
      Nonempty (ChartwisePLBall e D (frontier D)) := by
  let c := (e i).restrOpen U hU
  have hxc : x ∈ c.source := ⟨hx, hxU⟩
  let z : V3 := c x
  obtain ⟨eps, heps, htarget⟩ := Metric.isOpen_iff.mp c.open_target z (c.map_source hxc)
  let r : ℝ := eps / 2
  have hr : 0 < r := half_pos heps
  let a : V3 ≃ₜ V3 := (Homeomorph.smulOfNeZero r hr.ne').trans
    (ContinuousAffineEquiv.constVAdd ℝ V3 z).toHomeomorph
  let f : V3 →ᴬ[ℝ] V3 :=
    ContinuousAffineMap.const ℝ V3 z + r • ContinuousAffineMap.id ℝ V3
  have ha (u : V3) : a u = z + r • u := rfl
  have hf (u : V3) : f u = a u := rfl
  let C : Set V3 := closedBall 0 1
  let B : Set V3 := a '' C
  have hBC : B ⊆ c.target := by
    rintro y ⟨u, hu, rfl⟩
    apply htarget
    rw [mem_ball, dist_eq_norm, ha, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    have hu' : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
    have hbound : r * ‖u‖ ≤ r := by nlinarith
    exact hbound.trans_lt (by dsimp [r]; linarith)
  let D : Set X := c.symm '' B
  have hB : IsCompact B := (isCompact_closedBall (0 : V3) 1).image a.continuous
  have hD : IsCompact D := hB.image_of_continuousOn (c.symm.continuousOn.mono hBC)
  have hDU : D ⊆ U := by
    rintro y ⟨v, hv, rfl⟩
    exact (c.map_target (hBC hv)).2
  let b : C ≃ₜ D := (a.image C).trans (c.symm.homeomorphOfImageSubsetSource hBC rfl)
  have hb (u : C) : (b u : X) = c.symm (a u) := rfl
  have hBD : c.symm.IsImage B D := by
    intro u hu
    constructor
    · rintro ⟨v, hv, heq⟩
      exact c.symm.injOn (hBC hv) hu heq ▸ hv
    · exact fun hv => mem_image_of_mem _ hv
  have hfrontB : frontier B = a '' sphere (0 : V3) 1 := by
    change frontier (a '' closedBall (0 : V3) 1) = _
    rw [← a.image_frontier, frontier_closedBall _ one_ne_zero]
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKC, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3 C (sphere (0 : V3) 1))
  have hfPL : FinitePiecewiseAffineOn f K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine f⟩
  have hformula : PolyhedralPLInCharts e (c.symm ∘ f) C := by
    change PolyhedralPLInCharts e ((e i).symm ∘ f) (closedBall (0 : V3) 1)
    rw [← hKC]
    apply polyhedralPLInCharts_of_one_chart_inverse K hK hfPL i
    intro u hu
    rw [hf]
    exact (hBC ⟨u, hKC.subset hu, rfl⟩).1
  have hball : ChartwisePLBall e D (frontier D) := {
    boundary_subset := hD.isClosed.frontier_subset
    parametrization := b
    map := c.symm ∘ f
    map_eq := fun u => congrArg c.symm (hf u)
    piecewiseAffine := hformula
    boundary_eq := by
      intro u
      rw [hb, hBD.frontier.apply_mem_iff (hBC ⟨u, u.property, rfl⟩), hfrontB]
      exact a.injective.mem_set_image
  }
  have hxD : x ∈ D := by
    refine ⟨z, ?_, c.left_inv hxc⟩
    exact ⟨0, mem_closedBall_self zero_le_one, by simp only [ha, smul_zero, add_zero]⟩
  exact ⟨D, hD, hxD, hDU, ⟨hball⟩⟩

theorem PLDomain.exists_ball_in_interior {R : Set X} (he : PLDomain e R)
    (hne : (interior R).Nonempty) :
    ∃ D : Set X, IsCompact D ∧ D ⊆ interior R ∧
      Nonempty (ChartwisePLBall e D (frontier D)) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, hxi⟩ := he.cover x
  obtain ⟨D, hD, _, hDR, hb⟩ := exists_original_chart_ball i x hxi isOpen_interior hx
  exact ⟨D, hD, hDR, hb⟩

end PoincareConjecture.M76
