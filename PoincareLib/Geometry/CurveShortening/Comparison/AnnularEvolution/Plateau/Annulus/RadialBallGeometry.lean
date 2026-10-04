import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.RadialGeometry

/-! Concrete disk geometry near a radial boundary edge.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT

/-- Each coordinate difference is bounded by the Euclidean plane distance. Proof expansion
for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64LoopPlane_coordinate_dist_le (p q : LoopPlane) (i : Fin 2) :
    |p i - q i| ≤ dist p q := by
  simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using
    PiLp.norm_apply_le (p - q) i

/-- Distance to the vertical projection onto the radial axis equals the absolute height.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64RadialAxis_dist (b : LoopPlane) :
    dist b (annulusPoint (b 0) 0) = |b 1| := by
  have heq : b - annulusPoint (b 0) 0 = EuclideanSpace.single (1 : Fin 2) (b 1) := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  rw [dist_eq_norm, heq, PiLp.norm_single, Real.norm_eq_abs]

/-- Control the height and projected center of a point near a radial-axis center. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64RadialAxis_near_edge_center {a b : LoopPlane} {rho : ℝ}
    (ha : a 1 = 0) (hb : b ∈ closedBall a rho) :
    |b 1| ≤ rho ∧ dist (annulusPoint (b 0) 0) a ≤ 2 * rho := by
  have hba := mem_closedBall.mp hb
  have hrad : |b 1| ≤ rho := by
    simpa only [ha, sub_zero] using (m64LoopPlane_coordinate_dist_le b a 1).trans hba
  refine ⟨hrad, ?_⟩
  calc
    _ ≤ dist (annulusPoint (b 0) 0) b + dist b a := dist_triangle _ _ _
    _ = |b 1| + dist b a := by rw [dist_comm, m64RadialAxis_dist]
    _ ≤ 2 * rho := by linarith

/-- A disk in the extended strip with radius below its positive center height lies in the
annulus interior. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusLower_closedBall_upper {b : LoopPlane} {r : ℝ}
    (hball : closedBall b r ⊆ m64AnnulusLowerDomain) (hr : r < b 1) :
    closedBall b r ⊆ interior m64AnnulusDomain := by
  intro p hp
  have hpO := hball hp
  apply (m64AnnulusInterior_coordinates p).mpr
  have hd := (m64LoopPlane_coordinate_dist_le p b 1).trans (mem_closedBall.mp hp)
  exact ⟨hpO.1, hpO.2.1, by linarith [neg_abs_le (p 1 - b 1)], hpO.2.2.2⟩

/-- A disk in the extended strip with radius below its negative center height lies in the
prescribed lower strip. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusLower_closedBall_lower {b : LoopPlane} {r : ℝ}
    (hball : closedBall b r ⊆ m64AnnulusLowerDomain) (hr : r < -b 1) :
    closedBall b r ⊆ m64AnnulusLowerStrip := by
  intro p hp
  have hpO := hball hp
  apply (m64AnnulusLowerStrip_coordinates p).mpr
  have hd := (m64LoopPlane_coordinate_dist_le p b 1).trans (mem_closedBall.mp hp)
  exact ⟨hpO.1, hpO.2.1, hpO.2.2.1, by linarith [le_abs_self (p 1 - b 1)]⟩

end PoincareMT
