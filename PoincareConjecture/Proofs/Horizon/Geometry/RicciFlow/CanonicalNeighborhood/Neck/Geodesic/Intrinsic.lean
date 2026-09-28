import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Competitor

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

private theorem exists_spherical_competitor (x y : UnitTwoSphere) :
    ∃ σ : ℝ → UnitTwoSphere, σ 0 = x ∧ σ 1 = y ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 σ (Icc (0 : ℝ) 1) ∧
      (roundSphereMetric 2).pathELength σ 0 1 ≤ ENNReal.ofReal (Real.pi + 1) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
    ⟨(roundSphereMetric 2).toRiemannianMetric⟩
  have hdist : (roundSphereMetric 2).edist x y < ENNReal.ofReal (Real.pi + 1) := by
    rw [roundSphereMetric_edist_eq_angle (by norm_num : 1 ≤ 2)]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
    exact (Real.arccos_le_pi _).trans_lt (by linarith)
  obtain ⟨σ, h0, h1, hσ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hdist
  exact ⟨σ, h0, h1, hσ, hlen.le⟩

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem cylinderIntrinsicEDist_le_axial_add (N : EpsilonNeck g)
    {z w : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain) (hw : w ∈ N.cylinderDomain) :
    N.cylinderIntrinsicEDist z w ≤
      ENNReal.ofReal (|w.2 - z.2| + Real.sqrt 2 * (Real.pi + 1)) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  obtain ⟨σ, h0, h1, hσ, hlen⟩ := exists_spherical_competitor z.1 w.1
  let η : ℝ → RoundCylinderSpace := fun t => (σ t, z.2 + t * (w.2 - z.2))
  let e := roundCylinderModelDiffeomorph
  have hη := model_path_smooth (z := z) (w := w) hσ
  have hpath : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (e ∘ η) (Icc (0 : ℝ) 1) :=
    (e.contMDiff.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp_contMDiffOn hη
  have hend0 : (e ∘ η) 0 = z := by
    change (σ 0, z.2 + 0 * (w.2 - z.2)) = z
    simp [h0]
  have hend1 : (e ∘ η) 1 = w := by
    change (σ 1, z.2 + 1 * (w.2 - z.2)) = w
    simp [h1]
  apply roundCylinderMetric.intrinsicEDist_le_of_path hpath hend0 hend1
  · exact image_subset_iff.mpr (model_path_mem hz.2 hw.2)
  · have hh := model_path_length_le (z := z) (w := w) hσ hlen
    rw [ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
    simpa only [abs_sub_comm, add_comm] using hh

theorem intrinsicEDist_le_axial_add (N : EpsilonNeck g) {x y : M}
    (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    intrinsicEDist g N.carrier x y ≤ ENNReal.ofReal
      (N.scale * Real.sqrt (1 + N.epsilon) *
        (|(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
          Real.sqrt 2 * (Real.pi + 1))) := by
  have hx' := N.coordinate_inverse_mem x hx
  have hy' := N.coordinate_inverse_mem y hy
  have h := (N.intrinsicEDist_bounds hx' hy').2
  rw [N.coordinate_map_coordinate_inverse hx, N.coordinate_map_coordinate_inverse hy] at h
  exact (h.trans (mul_le_mul_of_nonneg_left
    (N.cylinderIntrinsicEDist_le_axial_add hx' hy') zero_le)).trans_eq
      (ENNReal.ofReal_mul (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))).symm

end PoincareConjecture.EpsilonNeck
