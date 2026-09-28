import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalBoxDomain
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.InteriorSphereLinks









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E3" => ((ℝ × ℝ) × ℝ)

theorem exists_finitePL_terminalBox_boundary_sphere
    {u v a b alpha beta : ℝ}
    (huv : u < v) (hab : a < b) (halpha : alpha < beta) :
    ∃ H : sphere (0 : V3) 1 ≃ₜ frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta),
      H.IsFinitePL := by
  classical
  have hpair := ((isFinitePLBallPair_Icc huv).prod
    (isFinitePLBallPair_Icc hab)).prod (isFinitePLBallPair_Icc halpha)
  have hfront := hpair.frontier_eq_of_finrank_eq rfl
  rw [← hfront] at hpair
  let c : E3 ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨H, hH, hHfront⟩ := hpair.exists_cube_chart c
  have hmem (z : closedBall (0 : V3) 1) :
      (z : V3) ∈ sphere (0 : V3) 1 ↔
      (H.symm z : E3) ∈ frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) := by
    have h := hHfront (H.symm z)
    rw [H.apply_symm_apply, frontier_closedBall _ one_ne_zero] at h
    exact h.symm
  have hb : frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ⊆
      ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) :=
    ((isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc).frontier_subset
  obtain ⟨J, hJ, hJS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  exact ⟨H.symm.restrictSubsets sphere_subset_closedBall hb hmem,
    hH.symm.restrictSubsets sphere_subset_closedBall hb hmem J hJ hJS⟩

theorem nonempty_chartwisePLSphere_terminalBox
    {u v a b alpha beta : ℝ}
    (huv : u < v) (hab : a < b) (halpha : alpha < beta) :
    Nonempty (ChartwisePLSphere terminalBoxAtlas
      (frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta))) := by
  obtain ⟨H, f, hf, hfeq⟩ := exists_finitePL_terminalBox_boundary_sphere huv hab halpha
  exact ⟨⟨H, f, fun x => (hfeq x).symm,
    polyhedralPL_terminalBoxAtlas_of_finitePiecewiseAffineOn hf⟩⟩

theorem simplyConnectedSpace_terminalBox_frontier
    {u v a b alpha beta : ℝ}
    (huv : u < v) (hab : a < b) (halpha : alpha < beta) :
    SimplyConnectedSpace (frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) := by
  obtain ⟨H, _⟩ := exists_finitePL_terminalBox_boundary_sphere huv hab halpha
  let : SimplyConnectedSpace (sphere (0 : V3) 1) := unitThreeSphere_lifting_properties.1
  exact H.symm.toHomotopyEquiv.simplyConnectedSpace

theorem locallyPathConnectedSpace_terminalBox_frontier
    {u v a b alpha beta : ℝ}
    (huv : u < v) (hab : a < b) (halpha : alpha < beta) :
    LocallyPathConnectedSpace (frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) := by
  obtain ⟨H, _⟩ := exists_finitePL_terminalBox_boundary_sphere huv hab halpha
  let : LocallyPathConnectedSpace (sphere (0 : V3) 1) := unitThreeSphere_lifting_properties.2
  exact H.symm.isOpenEmbedding.locallyPathConnectedSpace

end PoincareConjecture.M76
