import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.ChainTopSectors







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

theorem coordinate_bend_positive_sector_rays
    (c d : AffineBasis (Fin 3) ℝ Plane) {α σ : ℝ}
    (hd1 : d.coord 1 = σ • c.coord 2)
    (hd2 : d.coord 2 = σ • (c.coord 2 + α • c.coord 1))
    (hσα : 0 < σ * α) (v w : Plane)
    (hv1 : 0 < (c.coord 1).linear v) (hv2 : (c.coord 2).linear v = 0)
    (hw1 : (c.coord 1).linear w < 0)
    (hw2 : (c.coord 2 + α • c.coord 1).linear w = 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ v = a • (d 2 - d 0) ∧ w = b • (d 1 - d 0) := by
  have hvd1 : (d.coord 1).linear v = 0 := by
    rw [hd1]
    change σ * (c.coord 2).linear v = 0
    rw [hv2, mul_zero]
  have hvd2 : 0 < (d.coord 2).linear v := by
    rw [hd2]
    change 0 < σ * ((c.coord 2).linear v + α * (c.coord 1).linear v)
    rw [hv2, zero_add, ← mul_assoc]
    exact mul_pos hσα hv1
  have hwd2 : (d.coord 2).linear w = 0 := by
    rw [hd2]
    change σ * (c.coord 2 + α • c.coord 1).linear w = 0
    rw [hw2, mul_zero]
  have hwd1 : 0 < (d.coord 1).linear w := by
    change (c.coord 2).linear w + α * (c.coord 1).linear w = 0 at hw2
    rw [hd1]
    change 0 < σ * (c.coord 2).linear w
    have he : (c.coord 2).linear w = -(α * (c.coord 1).linear w) := by linarith
    rw [he, mul_neg, ← mul_assoc]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hσα hw1)
  refine ⟨(d.coord 2).linear v, (d.coord 1).linear w, hvd2, hwd1, ?_, ?_⟩
  · simpa only [hvd1, zero_smul, zero_add] using affineBasis_direction_expansion d v
  · simpa only [hwd2, zero_smul, add_zero] using affineBasis_direction_expansion d w

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]

theorem coordinate_bend_outward_angle_pos
    (g : RiemannianMetric 2 M) (x : M) (L : Plane →L[ℝ] Plane)
    (c d : AffineBasis (Fin 3) ℝ Plane) {α : ℝ} (hα : 0 < α)
    (hd1 : d.coord 1 = c.coord 2) (hd2 : d.coord 2 = c.coord 2 + α • c.coord 1)
    (v w u : Plane)
    (hv1 : 0 < (c.coord 1).linear v) (hv2 : (c.coord 2).linear v = 0)
    (hw1 : (c.coord 1).linear w < 0)
    (hw2 : (c.coord 2 + α • c.coord 1).linear w = 0)
    (hu1 : (c.coord 1).linear u = 0) (hu2 : 0 < (c.coord 2).linear u)
    (hu : L u ≠ 0) :
    g.cornerAngle x (L v) (L u) + g.cornerAngle x (L w) (L u) =
      g.cornerAngle x (L (d 1 - d 0)) (L (d 2 - d 0)) := by
  obtain ⟨a, b, ha, hb, hv, hw⟩ := coordinate_bend_positive_sector_rays c d
    (σ := 1) (by simpa only [one_smul] using hd1) (by simpa only [one_smul] using hd2)
    (by simpa only [one_mul] using hα) v w hv1 hv2 hw1 hw2
  have h1 : 0 < (d.coord 1).linear u := by rw [hd1]; exact hu2
  have h2 : 0 < (d.coord 2).linear u := by
    rw [hd2]
    change 0 < (c.coord 2).linear u + α * (c.coord 1).linear u
    simpa only [hu1, mul_zero, add_zero] using hu2
  have hs := cornerAngle_split_of_positive_sector_coordinates g x d L u h1 h2 hu
  dsimp only [TangentSpace] at hs ⊢
  rw [hv, hw, map_smul, map_smul, g.cornerAngle_smul_pos_left _ _ _ ha,
    g.cornerAngle_smul_pos_left _ _ _ hb, g.cornerAngle_comm x _ (L u),
    g.cornerAngle_comm x _ (L u)]
  linarith

theorem coordinate_bend_outward_angle_neg
    (g : RiemannianMetric 2 M) (x : M) (L : Plane →L[ℝ] Plane)
    (c d : AffineBasis (Fin 3) ℝ Plane) {α : ℝ} (hα : α < 0)
    (hd1 : d.coord 1 = -c.coord 2) (hd2 : d.coord 2 = -(c.coord 2 + α • c.coord 1))
    (v w u : Plane)
    (hv1 : 0 < (c.coord 1).linear v) (hv2 : (c.coord 2).linear v = 0)
    (hw1 : (c.coord 1).linear w < 0)
    (hw2 : (c.coord 2 + α • c.coord 1).linear w = 0)
    (hu1 : (c.coord 1).linear u = 0) (hu2 : 0 < (c.coord 2).linear u)
    (hu : L u ≠ 0) :
    g.cornerAngle x (L v) (L u) + g.cornerAngle x (L w) (L u) =
      2 * Real.pi - g.cornerAngle x (L (d 1 - d 0)) (L (d 2 - d 0)) := by
  obtain ⟨a, b, ha, hb, hv, hw⟩ := coordinate_bend_positive_sector_rays c d
    (σ := -1) (by simpa only [neg_one_smul] using hd1)
    (by simpa only [neg_one_smul] using hd2) (by linarith) v w hv1 hv2 hw1 hw2
  have h1 : 0 < (d.coord 1).linear (-u) := by
    rw [hd1]
    change 0 < -(c.coord 2).linear (-u)
    simpa only [map_neg, neg_neg] using hu2
  have h2 : 0 < (d.coord 2).linear (-u) := by
    rw [hd2]
    change 0 < -((c.coord 2).linear (-u) + α * (c.coord 1).linear (-u))
    simpa only [map_neg, hu1, neg_zero, mul_zero, add_zero, neg_neg] using hu2
  have hn : L (-u) ≠ 0 := by rwa [map_neg, neg_ne_zero]
  have hs := cornerAngle_split_of_positive_sector_coordinates g x d L (-u) h1 h2 hn
  dsimp only [TangentSpace] at hs ⊢
  rw [L.map_neg u, g.cornerAngle_neg_left, g.cornerAngle_neg_left] at hs
  rw [hv, hw, map_smul, map_smul, g.cornerAngle_smul_pos_left _ _ _ ha,
    g.cornerAngle_smul_pos_left _ _ _ hb, g.cornerAngle_comm x _ (L u),
    g.cornerAngle_comm x _ (L u)]
  linarith

theorem coordinate_bend_outward_angle_zero
    (g : RiemannianMetric 2 M) (x : M) (L : Plane →L[ℝ] Plane)
    (c : AffineBasis (Fin 3) ℝ Plane) (v w u : Plane)
    (hv1 : 0 < (c.coord 1).linear v) (hv2 : (c.coord 2).linear v = 0)
    (hw1 : (c.coord 1).linear w < 0) (hw2 : (c.coord 2).linear w = 0) :
    g.cornerAngle x (L v) (L u) + g.cornerAngle x (L w) (L u) = Real.pi := by
  have hv : v = (c.coord 1).linear v • (c 1 - c 0) := by
    simpa only [hv2, zero_smul, add_zero] using affineBasis_direction_expansion c v
  have hw : w = (-(c.coord 1).linear w) • (-(c 1 - c 0)) := by
    simpa only [hw2, zero_smul, add_zero, neg_smul, smul_neg, neg_neg] using
      affineBasis_direction_expansion c w
  rw [hv, hw, map_smul, map_smul, map_neg,
    g.cornerAngle_smul_pos_left _ _ _ hv1,
    g.cornerAngle_smul_pos_left _ _ _ (neg_pos.mpr hw1), g.cornerAngle_neg_left]
  ring

namespace FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

variable {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane M} {a b : ℝ}
  {S : D.OrientedEdgeGraphSubdivision e R C a b}
  {dLeft dRight : Plane} (K : S.CutChain dLeft dRight)
  {δ r : ℝ}
  (B : ∀ i : Fin S.count, (S.piece i).FixedStripBandFaces (K.graphCuts i) δ r r)



theorem adjacent_top_refined_fan_add_outward_angles
    (g : RiemannianMetric 2 M)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (i j : Fin S.count) (hij : i.succ = j.castSucc)
    (linesi : (Fin (B i).faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (linesj : (Fin (B j).faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ)) :
    let q := C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ
    let L := mfderiv (𝓡 2) (𝓡 2) C q
    ((∑ p : Fin (B i).faces.interface.count × Bool,
      meshVertexAngleContribution g ((B i).faces.faceCoordinates p)
        ((TriangleMesh.single ((B i).faces.faceBasis p) ((B i).faces.faceBasis p).ind).refineByLines (linesi p))
        (C q)) +
     ∑ p : Fin (B j).faces.interface.count × Bool,
      meshVertexAngleContribution g ((B j).faces.faceCoordinates p)
        ((TriangleMesh.single ((B j).faces.faceBasis p) ((B j).faces.faceBasis p).ind).refineByLines (linesj p))
        (C q)) +
      (g.cornerAngle (C q) (L ((B i).chartTopVertex (B i).faces.lastCell.castSucc - q))
        (L (K.direction i.succ)) +
       g.cornerAngle (C q) (L ((B j).chartTopVertex (B j).faces.firstCell.succ - q))
        (L (K.direction i.succ))) = 2 * Real.pi := by
  let q := C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ
  have hlast : (B i).faces.lastCell.succ = Fin.last (B i).faces.interface.count := by
    apply Fin.ext
    dsimp [ObliqueBandFaces.lastCell]
    have hn := (B i).faces.interface.count_pos
    omega
  have hi : (B i).chartTopVertex (B i).faces.lastCell.succ = q := by
    rw [hlast, (B i).chart_last_top_eq_physical (S.cut_lt i).le]
    simp only [q, Prod.eta, ContinuousLinearEquiv.symm_apply_apply]
  have hj : (B j).chartTopVertex 0 = q := by
    rw [(B j).chart_first_top_eq_physical (S.cut_lt j).le]
    simp only [q, Prod.eta, ContinuousLinearEquiv.symm_apply_apply, hij]
  have hiangle := (B i).last_refined_fan_add_physical_angle g hC hCi linesi
  have hjangle := (B j).first_refined_fan_add_physical_angle g hC hCi (S.cut_lt j).le linesj
  dsimp only at hiangle hjangle ⊢
  simp only [hi, hj, Prod.eta, ContinuousLinearEquiv.symm_apply_apply, ← hij] at hiangle hjangle
  have hai := congrArg (fun z : Plane => g.cornerAngle (C z)
    ((mfderiv (𝓡 2) (𝓡 2) C z) ((B i).chartTopVertex (B i).faces.lastCell.castSucc - q))
    ((mfderiv (𝓡 2) (𝓡 2) C z) (K.direction i.succ))) hi
  have haj := congrArg (fun z : Plane => g.cornerAngle (C z)
    ((mfderiv (𝓡 2) (𝓡 2) C z) ((B j).chartTopVertex (B j).faces.firstCell.succ - q))
    ((mfderiv (𝓡 2) (𝓡 2) C z) (K.direction i.succ))) hj
  rw [hai] at hiangle
  rw [haj] at hjangle
  change _ + (_ + _) = 2 * Real.pi
  linarith

end FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

end PoincareConjecture.Topology.Surface
