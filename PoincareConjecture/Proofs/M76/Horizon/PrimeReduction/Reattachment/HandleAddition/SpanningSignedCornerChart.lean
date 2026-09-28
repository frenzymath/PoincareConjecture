import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorSurfaceGerms



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private def sphereCornerCoordinates (positive : Bool) : V3 ≃L[ℝ] C3 where
  toFun z := ((z 0,z 2),if positive then z 1 else -z 1)
  invFun z := ![z.1.1,if positive then z.2 else -z.2,z.1.2]
  left_inv z := by ext i; fin_cases i <;> cases positive <;> simp
  right_inv z := by cases positive <;> ext <;> simp
  map_add' z w := by cases positive <;> ext <;> simp [add_comm]
  map_smul' c z := by cases positive <;> ext <;> simp
  continuous_toFun := by cases positive <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop
  continuous_invFun := by cases positive <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop



theorem exists_signed_original_sphere_corner_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {W S F : Set X}
    (hW : PLDomain e W) (hfront : frontier W = S)
    {x : X} (hxS : x ∈ S)
    (H : OpenPartialHomeomorph X V3) (hxH : x ∈ H.source) (hHx : H x = 0)
    (hHe : ∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3)
    (hHS : ∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0)
    (hHF : ∀ y ∈ H.source,y ∈ F ↔ H y 0 = 0) :
    ∃ (B : OpenPartialHomeomorph X V3) (L : V3 ≃L[ℝ] C3),
      x ∈ B.source ∧ B x = 0 ∧ B.source ⊆ H.source ∧
      (∀ i,(e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (∀ z ∈ B.target,B.symm z ∈ W ↔ 0 ≤ (L z).2) ∧
      (∀ z ∈ B.target,B.symm z ∈ S ↔ (L z).2 = 0) ∧
      ∀ z ∈ B.target,B.symm z ∈ F ↔ (L z).1.1 = 0 := by
  obtain ⟨B,hxB,hBx,hcv,hBH,_,_,hval,_⟩ :=
    H.exists_convex_target_avoiding hxH hHx isClosed_empty (notMem_empty x)
  have hBe (i : ι) : (e i).symm.trans B ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have h := (hHe i).1.mono ((e i).symm.trans B).open_source
      (fun _ hz => ⟨hz.1,hBH hz.2⟩)
    exact h.congr (fun z _ => (hval ((e i).symm z)).symm)
  have hBS (y : X) (hy : y ∈ B.source) : y ∈ S ↔ B y 1 = 0 := by
    rw [hval]
    exact hHS y (hBH hy)
  have hBF (y : X) (hy : y ∈ B.source) : y ∈ F ↔ B y 0 = 0 := by
    rw [hval]
    exact hHF y (hBH hy)
  have hfrontB (y : X) (hy : y ∈ B.source) : y ∈ frontier W ↔ B y 1 = 0 := by
    rw [hfront]
    exact hBS y hy
  rcases halfspace_of_convex_linear_frontier_chart hW.closed hW.closure_interior
    (hfront.symm ▸ hxS) B hxB (ContinuousLinearMap.proj 1) hcv hfrontB with hpos | hneg
  · refine ⟨B,sphereCornerCoordinates true,hxB,hBx,hBH,hBe,?_,?_,?_⟩
    · intro z hz
      change B.symm z ∈ W ↔ 0 ≤ z 1
      simpa only [ContinuousLinearMap.proj_apply,B.right_inv hz] using hpos (B.symm z) (B.map_target hz)
    · intro z hz
      change B.symm z ∈ S ↔ z 1 = 0
      simpa only [B.right_inv hz] using hBS (B.symm z) (B.map_target hz)
    · intro z hz
      change B.symm z ∈ F ↔ z 0 = 0
      simpa only [B.right_inv hz] using hBF (B.symm z) (B.map_target hz)
  · refine ⟨B,sphereCornerCoordinates false,hxB,hBx,hBH,hBe,?_,?_,?_⟩
    · intro z hz
      change B.symm z ∈ W ↔ 0 ≤ -z 1
      simpa only [ContinuousLinearMap.proj_apply,B.right_inv hz,neg_nonneg] using hneg (B.symm z) (B.map_target hz)
    · intro z hz
      change B.symm z ∈ S ↔ -z 1 = 0
      simpa only [B.right_inv hz,neg_eq_zero] using hBS (B.symm z) (B.map_target hz)
    · intro z hz
      change B.symm z ∈ F ↔ z 0 = 0
      simpa only [B.right_inv hz] using hBF (B.symm z) (B.map_target hz)

end PoincareConjecture.M76
