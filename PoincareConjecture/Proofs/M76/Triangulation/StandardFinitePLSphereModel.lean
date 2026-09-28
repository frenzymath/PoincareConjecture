import PoincareConjecture.Proofs.M76.Mathlib.ConvexSpherePoleNormalization
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryExtension
import PoincareConjecture.Proofs.M76.Mathlib.TriangularHalfBalls

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsFinitePL.exists_standard_three_sphere_model
    {S : Set E} {D : Set F} {e : S ≃ₜ frontier D} (he : e.IsFinitePL)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hdim : Module.finrank ℝ F = 3) :
    ∃ f : S ≃ₜ frontier (halfBall 1), f.IsFinitePL := by
  let : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨p, hp⟩ := (NormedSpace.sphere_nonempty (E := F) (x := (0 : F))).mpr
    (show (0 : ℝ) ≤ 1 from zero_le_one)
  obtain ⟨_, eunit, _⟩ := hD.exists_compatible_unitBall_models hcv hne
  let pD : frontier D := eunit.symm ⟨p, hp⟩
  have hecopy := he.symm
  obtain ⟨_, ⟨KD, hKD, hKDspace, _⟩, _⟩ := hecopy
  let cD : F ≃L[ℝ] (Fin 3 → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hdim])
  obtain ⟨fD, hfD, _⟩ := KD.exists_finitePL_convex_frontier_cube_pole
    hKD hD hcv hne hKDspace cD pD
  have hB := isFinitePLBallPair_halfBall (h := 1) (Or.inl rfl)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨KB, hKB, hKBspace, _⟩, _⟩, _⟩ := hB
  have hBcompact := isCompact_halfBall (h := 1) (Or.inl rfl)
  have hBinterior := interior_halfBall_nonempty (h := 1) (Or.inl rfl)
  have hBconvex : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  have hzero : (0 : (ℝ × ℝ) × ℝ) ∈ frontier (halfBall 1) := by
    rw [frontier_halfBall (Or.inl rfl)]
    apply Or.inr
    apply (mem_disk 0).mpr
    refine ⟨(roof_nonneg_iff _).mp ?_, rfl⟩
    norm_num [roof]
  let cB : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨fB, hfB, _⟩ :=
    (KB.frontierSubcomplex (halfBall 1)).exists_finitePL_convex_frontier_cube_pole
      (KB.frontierSubcomplex_finite _ hKB) hBcompact hBconvex hBinterior
      (KB.frontierSubcomplex_space hBcompact.isClosed hBconvex hBinterior hKBspace)
      cB ⟨0, hzero⟩
  exact ⟨e.trans (fD.trans fB.symm), he.trans (hfD.trans hfB.symm)⟩

end Homeomorph
