import PoincareConjecture.Proofs.M25.Topology3D.Plane.AnnularExtension

set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

section Normed

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def curveTubeProjection [NormedSpace ℝ E] (q0 : sphere (0 : E) 1)
    (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E)) (y : ℝ × E) : sphere (0 : E) 1 :=
  unitRadialProjection q0 (e.symm y).2

noncomputable def curveTubeHeight (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (y : ℝ × E) : ℝ := ‖(e.symm y).2‖ - 1

variable [NormedSpace ℝ E]

theorem curveTubeCoordinates_apply_radial (q0 : sphere (0 : E) 1)
    (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E)) (z : ℝ) (q : sphere (0 : E) 1)
    {r : ℝ} (hr : -1 < r) (hp : (z, (1 + r) • (q : E)) ∈ e.source) :
    curveTubeProjection q0 e (e (z, (1 + r) • (q : E))) = q ∧
      curveTubeHeight e (e (z, (1 + r) • (q : E))) = r := by
  have hpos : 0 < 1 + r := by linarith
  simp only [curveTubeProjection, curveTubeHeight, e.left_inv hp]
  constructor
  · exact (unitRadialProjection_pos_smul q0 hpos (q : E)).trans
      (unitRadialProjection_apply_coe q0 q)
  · simp [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, norm_eq_of_mem_sphere q]

theorem curveTubeCoordinates_reconstruct (q0 : sphere (0 : E) 1)
    (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E)) (y : ℝ × E)
    (hy : (e.symm y).2 ≠ 0) :
    (1 + curveTubeHeight e y) • (curveTubeProjection q0 e y : E) = (e.symm y).2 := by
  change (1 + (‖(e.symm y).2‖ - 1)) • (unitRadialProjection q0 (e.symm y).2 : E) = _
  rw [unitRadialProjection_coe_of_ne_zero q0 hy, smul_smul,
    show 1 + (‖(e.symm y).2‖ - 1) = ‖(e.symm y).2‖ by ring,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiffOn_curveTubeHeight (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {k : ℕ∞ω} (hInv : ContDiffOn ℝ k e.symm e.target)
    (hx : ∀ y ∈ e.target, (e.symm y).2 ≠ 0) :
    ContDiffOn ℝ k (curveTubeHeight e) e.target := by
  intro y hy
  have h := (hInv.contDiffAt (e.open_target.mem_nhds hy)).snd
  exact (((contDiffAt_norm ℝ (hx y hy)).comp y h).sub contDiffAt_const).contDiffWithinAt

theorem contMDiffOn_curveTubeProjection {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (q0 : sphere (0 : E) 1) (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {k : ℕ∞ω} (hInv : ContDiffOn ℝ k e.symm e.target)
    (hx : ∀ y ∈ e.target, (e.symm y).2 ≠ 0) :
    ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) k (curveTubeProjection q0 e) e.target := by
  exact (contMDiffOn_unitRadialProjection (n := n) (m := k) q0).comp
    hInv.snd.contMDiffOn (fun y hy => hx y hy)

variable [Fact (Module.finrank ℝ E = 2)]
variable (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
variable (c : ℝ → sphere (0 : E) 1 → E)
variable (e : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
variable {l u w : ℝ} (hw : w < 1)
variable (hs : e.source = Ioo l u ×ˢ {x : E | |‖x‖ - 1| < w})
variable (he : ∀ p : ℝ × E, e p = (p.1, curveAnnularExtension o q0 c p))

include hw hs he

theorem curveAnnularTube_coordinates {y : ℝ × E} (hy : y ∈ e.target) :
    (e.symm y).2 ≠ 0 ∧ y.1 ∈ Ioo l u ∧ |curveTubeHeight e y| < w ∧
      e.symm y = (y.1, (1 + curveTubeHeight e y) • (curveTubeProjection q0 e y : E)) ∧
      y.2 = c y.1 (curveTubeProjection q0 e y) + curveTubeHeight e y •
        curveFamilyNormal o (radialFamilyExtension q0 c)
          (y.1, (curveTubeProjection q0 e y : E)) := by
  have hp : e.symm y ∈ Ioo l u ×ˢ {x : E | |‖x‖ - 1| < w} :=
    hs ▸ e.map_target hy
  have hr : |‖(e.symm y).2‖ - 1| < w := hp.2
  have hnorm : 0 < ‖(e.symm y).2‖ := by linarith [(abs_lt.mp hr).1]
  have hx0 : (e.symm y).2 ≠ 0 := norm_pos_iff.mp hnorm
  have himage : ((e.symm y).1, curveAnnularExtension o q0 c (e.symm y)) = y :=
    (he _).symm.trans (e.right_inv hy)
  have htime : (e.symm y).1 = y.1 := by
    simpa only using congrArg (fun p : ℝ × E => p.1) himage
  have hpair : e.symm y =
      (y.1, (1 + curveTubeHeight e y) • (curveTubeProjection q0 e y : E)) :=
    Prod.ext htime (curveTubeCoordinates_reconstruct q0 e y hx0).symm
  refine ⟨hx0, htime ▸ hp.1, hr, hpair, ?_⟩
  have hheight : -1 < curveTubeHeight e y := by
    change -1 < ‖(e.symm y).2‖ - 1
    linarith
  calc
    y.2 = curveAnnularExtension o q0 c (e.symm y) := (congrArg Prod.snd himage).symm
    _ = _ := by
      rw [hpair]
      exact curveAnnularExtension_apply_radial o q0 c y.1 (curveTubeProjection q0 e y) hheight

theorem curveAnnularTube_coordinates_apply (z : ℝ) (hz : z ∈ Ioo l u)
    (q : sphere (0 : E) 1) {r : ℝ} (hr : |r| < w) :
    let y := (z, c z q + r • curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E)))
    y ∈ e.target ∧ curveTubeProjection q0 e y = q ∧ curveTubeHeight e y = r := by
  have hr1 : -1 < r := by linarith [(abs_lt.mp hr).1]
  have hpos : 0 < 1 + r := by linarith
  have hp : (z, (1 + r) • (q : E)) ∈ e.source := by
    rw [hs]
    refine ⟨hz, ?_⟩
    change |‖(1 + r) • (q : E)‖ - 1| < w
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, norm_eq_of_mem_sphere q] using hr
  have himage : e (z, (1 + r) • (q : E)) =
      (z, c z q + r • curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) := by
    rw [he, curveAnnularExtension_apply_radial o q0 c z q hr1]
  dsimp only
  rw [← himage]
  exact ⟨e.map_source hp, curveTubeCoordinates_apply_radial q0 e z q hr1 hp⟩

end InnerProduct

end PoincareConjecture.M25.Topology3D
