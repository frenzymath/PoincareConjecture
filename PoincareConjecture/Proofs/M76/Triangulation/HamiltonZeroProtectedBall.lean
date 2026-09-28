import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroLatticePuncturedAtlas
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "W" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "V3" => (Fin 3 → ℝ)





theorem exists_hamilton_zero_protected_chart_ball
    {α : Type*} (e : α → OpenPartialHomeomorph W V3)
    (i : α) (x : W) (hx : x ∈ (e i).source) :
    ∃ P : Set W, x ∈ P ∧
      Nonempty (HamiltonMarkedProtectedBall (Fin 0) (Fin 3)
        hamiltonZeroPeriodLattice e P) := by
  classical
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space W := hamiltonZeroHandleProductEquiv.isEmbedding.t2Space
  let z : V3 := e i x
  obtain ⟨eps, heps, htarget⟩ := Metric.isOpen_iff.mp (e i).open_target z
    ((e i).map_source hx)
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
  have hBC : B ⊆ (e i).target := by
    rintro y ⟨u, hu, rfl⟩
    apply htarget
    rw [mem_ball, dist_eq_norm, ha, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    have hu' : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
    have hbound : r * ‖u‖ ≤ r := by nlinarith
    exact hbound.trans_lt (by dsimp [r]; linarith)
  let P : Set W := (e i).symm '' B
  have hB : IsCompact B := (isCompact_closedBall (0 : V3) 1).image a.continuous
  have hP : IsCompact P := hB.image_of_continuousOn ((e i).symm.continuousOn.mono hBC)
  let b : C ≃ₜ P := (a.image C).trans
    ((e i).symm.homeomorphOfImageSubsetSource hBC rfl)
  have hb (u : C) : (b u : W) = (e i).symm (a u) := rfl
  have hBP : (e i).symm.IsImage B P := by
    intro u hu
    constructor
    · rintro ⟨v, hv, heq⟩
      exact ((e i).symm.injOn (hBC hv) hu heq) ▸ hv
    · exact fun hv => mem_image_of_mem _ hv
  have hfrontB : frontier B = a '' sphere (0 : V3) 1 := by
    change frontier (a '' closedBall (0 : V3) 1) = _
    rw [← a.image_frontier, frontier_closedBall _ one_ne_zero]
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKC, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3 C (sphere (0 : V3) 1))
  have hfPL : FinitePiecewiseAffineOn f K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine f⟩
  have hformula : PolyhedralPLInCharts e ((e i).symm ∘ f) C := by
    change PolyhedralPLInCharts e ((e i).symm ∘ f) (closedBall (0 : V3) 1)
    rw [← hKC]
    apply polyhedralPLInCharts_of_one_chart_inverse K hK hfPL i
    intro u hu
    rw [hf]
    exact hBC ⟨u, hKC.subset hu, rfl⟩
  have hball : ChartwisePLBall e P (frontier P) := {
    boundary_subset := hP.isClosed.frontier_subset
    parametrization := b
    map := (e i).symm ∘ f
    map_eq := fun u => congrArg (e i).symm (hf u)
    piecewiseAffine := hformula
    boundary_eq := by
      intro u
      rw [hb]
      rw [hBP.frontier.apply_mem_iff (hBC ⟨u, u.property, rfl⟩), hfrontB]
      exact a.injective.mem_set_image }
  have hxP : x ∈ P := by
    refine ⟨z, ?_, (e i).left_inv hx⟩
    exact ⟨0, mem_closedBall_self zero_le_one, by simp only [ha, smul_zero, add_zero]⟩
  have hR : latticeHandleDomain (Fin 0) (Fin 3) hamiltonZeroPeriodLattice = univ := by
    ext y
    have hy : y.1 = 0 := Subsingleton.elim _ _
    simp [latticeHandleDomain, hy]
  refine ⟨P, hxP, ⟨{
    ball := hball
    subset_domain := by rw [hR]; exact subset_univ P
    position := Or.inl ⟨by simp, by rw [hR, interior_univ]; exact subset_univ P⟩
  }⟩⟩

end PoincareConjecture.M76
