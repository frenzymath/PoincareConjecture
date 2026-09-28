import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneShellCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOnePlaneDiskPatches
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeAffineHeightStep
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinderHalfspace
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "W" => (ℝ × (ℝ × ℝ))
local notation "V" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)

def squareShell : Set W :=
  Icc (-1) 1 ×ˢ ((norm : (ℝ × ℝ) → ℝ) ⁻¹' Icc (3 / 2) 2)

private noncomputable def shellCoordinateLinear : W ≃ₗ[ℝ] V3 where
  toFun p := ![p.1, p.2.1, 4 * p.2.2]
  invFun x := (x 0, (x 1, x 2 / 4))
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · dsimp
        ring
  right_inv x := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change 4 * (x 2 / 4) = x 2
      ring
  map_add' p q := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change 4 * (p.2.2 + q.2.2) = 4 * p.2.2 + 4 * q.2.2
      ring
  map_smul' a p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change 4 * (a * p.2.2) = a * (4 * p.2.2)
      ring

theorem exists_square_shell_frontier_disk_patch {x : W}
    (hx : x ∈ frontier squareShell) :
    ∃ d q : Set W, IsFinitePLBallPair (ℝ × ℝ) d q ∧ d ⊆ frontier squareShell ∧
      x ∈ d \ q ∧ IsOpen ((Subtype.val : frontier squareShell → W) ⁻¹' (d \ q)) := by
  have hclosed : IsClosed squareShell :=
    isClosed_Icc.prod (isClosed_Icc.preimage continuous_norm)
  have hxS := hclosed.frontier_subset hx
  obtain ⟨P, hxP, hPPL, hnorm⟩ := exists_square_shell_radial_chart hxS.2
  let B := (OpenPartialHomeomorph.refl ℝ).prod P
  let c := shellCoordinateLinear.toContinuousLinearEquiv.toContinuousAffineEquiv
  let Q := B.symm.trans c.toHomeomorph.toOpenPartialHomeomorph
  have hBPL : LocallyPiecewiseAffineOn B B.source :=
    (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ).prodMap hPPL.1
  have hQiPL : LocallyPiecewiseAffineOn Q.symm Q.target :=
    hBPL.comp (locallyPiecewiseAffineOn_affine c.symm.toContinuousAffineMap isOpen_univ)
  have hxQ : x ∈ Q.source := ⟨⟨mem_univ _, hxP⟩, mem_univ _⟩
  let J : Finset (Fin 3) := {0, 2}
  have himage : Q.IsImage squareShell (coordinateCylinder J) := by
    intro y hy
    have hyP : y.2 ∈ P.target := hy.1.2
    have hn := hnorm (P.symm y.2) (P.map_target hyP)
    rw [P.right_inv hyP] at hn
    constructor
    · intro hcyl
      have hs : |y.1| ≤ 1 := hcyl 0 (by simp [J])
      have ht : |4 * (P.symm y.2).2| ≤ 1 := hcyl 2 (by simp [J])
      have hs' := abs_le.mp hs
      have ht' := abs_le.mp ht
      refine ⟨hs', ?_⟩
      change ‖y.2‖ ∈ Icc (3 / 2 : ℝ) 2
      constructor <;> linarith [ht'.1, ht'.2]
    · intro hyS i hi
      have hi' : i = 0 ∨ i = 2 := by simpa only [J, Finset.mem_insert,
        Finset.mem_singleton] using hi
      rcases hi' with rfl | rfl
      · change |y.1| ≤ 1
        exact abs_le.mpr hyS.1
      · change |4 * (P.symm y.2).2| ≤ 1
        apply abs_le.mpr
        have hb : ‖y.2‖ ∈ Icc (3 / 2 : ℝ) 2 := hyS.2
        constructor <;> linarith [hb.1, hb.2]
  have hxfront : Q x ∈ frontier (coordinateCylinder J) :=
    (himage.frontier.apply_mem_iff hxQ).mpr hx
  obtain ⟨ell, w, H, hw, hxH, _, _, hHPL, hhalf⟩ :=
    exists_coordinateCylinder_halfspace_chart J hxfront
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro hz
    have hw' : ell.toAffineMap.linear w = 1 := hw
    rw [hz] at hw'
    norm_num at hw'
  obtain ⟨f, _, hfinv⟩ := ZeroChargeJoint.exists_affine_height_coordinates
    (E := ℝ × ℝ) ell.toAffineMap hell (by simp) 0
  let D := (Q.trans H).trans f.symm.toHomeomorph.toOpenPartialHomeomorph
  have hxD : x ∈ D.source := ⟨⟨hxQ, hxH⟩, mem_univ _⟩
  have hDiPL : LocallyPiecewiseAffineOn D.symm D.target :=
    (hQiPL.comp hHPL.2).comp
      (locallyPiecewiseAffineOn_affine f.toContinuousAffineMap isOpen_univ)
  have hfront : ∀ y ∈ D.source, y ∈ frontier squareShell ↔ (D y).2 = 0 := by
    intro y hy
    have hDy : (D y).2 = ell (H (Q y)) := by
      change (f.symm (H (Q y))).2 = ell (H (Q y))
      simpa only [sub_zero, ContinuousAffineMap.coe_toAffineMap] using hfinv (H (Q y))
    rw [hDy]
    exact (himage.frontier.apply_mem_iff hy.1.1).symm.trans
      ((H.isImage_frontier_of_affine_nonneg ell hell hhalf).apply_mem_iff hy.1.2).symm
  exact exists_disk_patch_of_plane_chart D hDiPL hfront hx hxD

end PoincareConjecture.M76.HamiltonIndexOne
