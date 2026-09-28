import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ConvexFrontierSides
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ConvexTargetRestriction
import PoincareConjecture.Proofs.M76.Rigidity.CenteredHalfspaceCharts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall



set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private noncomputable def relativeSignedCoordinates
    (ε η : ℝ) (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1) :
    V3 ≃L[ℝ] C3 :=
  ({ toFun := fun z ↦ ((η * z 1, z 2), ε * z 0)
     invFun := fun z ↦ ![ε * z.2, η * z.1.1, z.1.2]
     left_inv := by
       intro z
       rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;>
         funext i <;> fin_cases i <;> simp
     right_inv := by
       intro z
       rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> ext <;> simp
     map_add' := by intro z w; ext <;> simp [mul_add]
     map_smul' := by intro a z; ext <;> simp [mul_left_comm] } :
    V3 ≃ₗ[ℝ] C3).toContinuousLinearEquiv

private theorem relative_affine_postcomp
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (H : OpenPartialHomeomorph X V3)
    (hH : ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3)
    (a : V3 ≃ᴬ[ℝ] C3) (i : ι) :
    LocallyPiecewiseAffineOn ((e i).symm.trans
      (H.trans a.toHomeomorph.toOpenPartialHomeomorph))
      ((e i).symm.trans (H.trans a.toHomeomorph.toOpenPartialHomeomorph)).source := by
  have ha : LocallyPiecewiseAffineOn a.toHomeomorph.toOpenPartialHomeomorph
      a.toHomeomorph.toOpenPartialHomeomorph.source :=
    locallyPiecewiseAffineOn_affine a.toContinuousAffineMap isOpen_univ
  have hh : LocallyPiecewiseAffineOn
      (((e i).symm.trans H).trans a.toHomeomorph.toOpenPartialHomeomorph)
      (((e i).symm.trans H).trans a.toHomeomorph.toOpenPartialHomeomorph).source :=
    ha.comp (hH i).1
  simpa only [OpenPartialHomeomorph.trans_assoc] using hh





theorem PLDomain.exists_signed_relative_frontier_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D W : Set X}
    (hD : PLDomain e D) (hW : PLDomain e W)
    (hcross : ∀ x ∈ frontier D ∩ frontier W,
      ∃ H : OpenPartialHomeomorph X V3,
        x ∈ H.source ∧ H x = 0 ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source, y ∈ frontier D ↔ H y 0 = 0) ∧
        ∀ y ∈ H.source, y ∈ frontier W ↔ H y 1 = 0)
    {x : X} (hx : x ∈ frontier D ∩ W) :
    ∃ B : OpenPartialHomeomorph X C3,
      x ∈ B.source ∧ B x = 0 ∧
      (∀ i, LocallyPiecewiseAffineOn ((e i).symm.trans B)
        ((e i).symm.trans B).source) ∧
      (∀ y ∈ B.source, y ∈ D ↔ 0 ≤ (B y).2) ∧
      (∀ y ∈ B.source, y ∈ frontier D ↔ (B y).2 = 0) ∧
      ((x ∈ interior W ∧ B.source ⊆ interior W) ∨
        (x ∈ frontier W ∧
          (∀ y ∈ B.source, y ∈ W ↔ 0 ≤ (B y).1.1) ∧
          ∀ y ∈ B.source, y ∈ frontier W ↔ (B y).1.1 = 0)) := by
  by_cases hxW : x ∈ frontier W
  · obtain ⟨H, hxH, hHz, hHe, hHD, hHW⟩ := hcross x ⟨hx.1, hxW⟩
    obtain ⟨T, hxT, hTz, hcv, hTH, _, _, hval, _⟩ :=
      H.exists_convex_target_avoiding hxH hHz isClosed_empty (notMem_empty x)
    have hTe (i : ι) : (e i).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact ((hHe i).1.mono ((e i).symm.trans T).open_source
        (fun _ hz ↦ ⟨hz.1, hTH hz.2⟩)).congr (fun z _ ↦ (hval ((e i).symm z)).symm)
    have hTD (y : X) (hy : y ∈ T.source) : y ∈ frontier D ↔ T y 0 = 0 := by
      rw [hval]
      exact hHD y (hTH hy)
    have hTW (y : X) (hy : y ∈ T.source) : y ∈ frontier W ↔ T y 1 = 0 := by
      rw [hval]
      exact hHW y (hTH hy)
    obtain ⟨ε, hε, hDs⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ y ∈ T.source, y ∈ D ↔ 0 ≤ ε * T y 0 := by
      rcases halfspace_of_convex_linear_frontier_chart hD.closed hD.closure_interior
        hx.1 T hxT (ContinuousLinearMap.proj 0) hcv hTD with hp | hn
      · exact ⟨1, Or.inl rfl, fun y hy ↦ by simpa using hp y hy⟩
      · exact ⟨-1, Or.inr rfl, fun y hy ↦ by simpa using hn y hy⟩
    obtain ⟨η, hη, hWs⟩ : ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
        ∀ y ∈ T.source, y ∈ W ↔ 0 ≤ η * T y 1 := by
      rcases halfspace_of_convex_linear_frontier_chart hW.closed hW.closure_interior
        hxW T hxT (ContinuousLinearMap.proj 1) hcv hTW with hp | hn
      · exact ⟨1, Or.inl rfl, fun y hy ↦ by simpa using hp y hy⟩
      · exact ⟨-1, Or.inr rfl, fun y hy ↦ by simpa using hn y hy⟩
    let c := relativeSignedCoordinates ε η hε hη
    let B := T.trans c.toHomeomorph.toOpenPartialHomeomorph
    refine ⟨B, ⟨hxT, mem_univ _⟩, ?_,
      relative_affine_postcomp T hTe c.toContinuousAffineEquiv, ?_, ?_, Or.inr ?_⟩
    · change c (T x) = 0
      rw [hTz, map_zero]
    · intro y hy
      exact hDs y hy.1
    · intro y hy
      change y ∈ frontier D ↔ ε * T y 0 = 0
      rw [hTD y hy.1]
      rcases hε with rfl | rfl <;> simp
    · refine ⟨hxW, fun y hy ↦ hWs y hy.1, ?_⟩
      intro y hy
      change y ∈ frontier W ↔ η * T y 1 = 0
      rw [hTW y hy.1]
      rcases hη with rfl | rfl <;> simp
  · have hxWi : x ∈ interior W := (mem_interior_iff_notMem_frontier hx.2).mpr hxW
    obtain ⟨ell, v, H, hv, hxH, hzero, hHe, hhalf⟩ := hD.halfspace x hx.1
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [h] at hval
      norm_num at hval
    obtain ⟨f, _, hf⟩ := ZeroChargeJoint.exists_affine_height_coordinates
      (E := ℝ × ℝ) ell.toAffineMap hell (by simp) 0
    let a := f.symm.trans (ContinuousAffineEquiv.constVAdd ℝ C3 (-(f.symm (H x))))
    let T := H.restrOpen (interior W) isOpen_interior
    let B := T.trans a.toHomeomorph.toOpenPartialHomeomorph
    have hheight (y : X) : (B y).2 = ell (H y) := by
      change -(f.symm (H x)).2 + (f.symm (H y)).2 = ell (H y)
      rw [hf, hf]
      change -(ell (H x) - 0) + (ell (H y) - 0) = ell (H y)
      rw [hzero]
      simp
    have hTe (i : ι) : (e i).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact (hHe i).1.mono ((e i).symm.trans T).open_source
        (fun _ hy ↦ ⟨hy.1, hy.2.1⟩)
    refine ⟨B, ⟨⟨hxH, hxWi⟩, mem_univ _⟩, ?_, relative_affine_postcomp T hTe a,
      ?_, ?_, Or.inl ⟨hxWi, fun _ hy ↦ hy.1.2⟩⟩
    · change -f.symm (H x) + f.symm (H x) = 0
      exact neg_add_cancel _
    · intro y hy
      rw [hheight]
      exact hhalf y hy.1.1
    · intro y hy
      rw [hheight]
      exact ((H.isImage_frontier_of_affine_nonneg ell hell hhalf).apply_mem_iff hy.1.1).symm

end PoincareConjecture.M76
