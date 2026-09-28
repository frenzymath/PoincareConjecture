import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

private theorem exists_spherical_region_competitor (x y : UnitTwoSphere) :
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


theorem intrinsicEDist_region_le_axial_add (N : EpsilonNeck g) {a b : ℝ} {x y : M}
    (hx : x ∈ N.region a b) (hy : y ∈ N.region a b) :
    intrinsicEDist g (N.region a b) x y ≤ ENNReal.ofReal
      (N.scale * Real.sqrt (1 + N.epsilon) *
        (|(N.coordinate_inverse y).2 - (N.coordinate_inverse x).2| +
          Real.sqrt 2 * (Real.pi + 1))) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let z := N.coordinate_inverse x
  let w := N.coordinate_inverse y
  have hz := N.coordinate_inverse_mem x hx.1
  have hw := N.coordinate_inverse_mem y hy.1
  obtain ⟨σ, h0, h1, hσ, hlen⟩ := exists_spherical_region_competitor z.1 w.1
  let η : ℝ → RoundCylinderSpace := fun t => (σ t, z.2 + t * (w.2 - z.2))
  let e := roundCylinderModelDiffeomorph
  have hpath : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (e ∘ η) (Icc (0 : ℝ) 1) :=
    (e.contMDiff.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp_contMDiffOn
      (model_path_smooth (z := z) (w := w) hσ)
  have hmap : MapsTo (e ∘ η) (Icc (0 : ℝ) 1) N.cylinderDomain :=
    model_path_mem hz.2 hw.2
  have hregion : MapsTo (N.coordinate_map ∘ (e ∘ η)) (Icc (0 : ℝ) 1)
      (N.region a b) := by
    intro t ht
    refine ⟨N.coordinate_map_mem (hmap ht), ?_⟩
    change a < (N.coordinate_inverse (N.coordinate_map ((e ∘ η) t))).2 ∧
      (N.coordinate_inverse (N.coordinate_map ((e ∘ η) t))).2 < b
    rw [N.coordinate_inverse_coordinate_map (hmap ht)]
    have hseg : z.2 + t • (w.2 - z.2) ∈ Ioo a b := by
      apply (convex_Ioo (𝕜 := ℝ) a b).segment_subset hx.2 hy.2
      rw [segment_eq_image' (𝕜 := ℝ) z.2 w.2]
      exact ⟨t, ht, rfl⟩
    change a < z.2 + t * (w.2 - z.2) ∧ z.2 + t * (w.2 - z.2) < b
    simpa only [smul_eq_mul, mem_Ioo] using hseg
  have hquad : ∀ p ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent p,
      (N.scale * Real.sqrt (1 - N.epsilon)) ^ 2 * EvolvingRoundCylinderMetric 0 p v v ≤
          roundCylinderPullback g N.coordinate_map p v v ∧
        roundCylinderPullback g N.coordinate_map p v v ≤
          (N.scale * Real.sqrt (1 + N.epsilon)) ^ 2 * EvolvingRoundCylinderMetric 0 p v v := by
    intro p hp v
    have hlo : (N.scale * Real.sqrt (1 - N.epsilon)) ^ 2 =
        (1 - N.epsilon) * N.scale ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_lt_half])]
      ring
    have hhi : (N.scale * Real.sqrt (1 + N.epsilon)) ^ 2 =
        (1 + N.epsilon) * N.scale ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos])]
      ring
    simpa only [hlo, hhi] using N.pullback_metric_bounds hp.2 v
  have htangent := N.coordinate_tangentNorm_bounds
    (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
    (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)) hquad
  have hlength := roundCylinderMetric.pathELength_comp_le_of_tangentNorm_le_on g
    N.cylinderDomain_open (N.coordinate_map_flat_smooth.of_le (by simp))
    (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
    (fun p hp v => (htangent p hp v).2) hpath hmap
  have hend0 : (e ∘ η) 0 = z := by
    change (σ 0, z.2 + 0 * (w.2 - z.2)) = z
    simp [h0]
  have hend1 : (e ∘ η) 1 = w := by
    change (σ 1, z.2 + 1 * (w.2 - z.2)) = w
    simp [h1]
  apply g.intrinsicEDist_le_of_path (U := N.region a b)
    ((N.coordinate_map_flat_smooth.of_le (by simp)).comp hpath hmap)
    (by
      change N.coordinate_map ((e ∘ η) 0) = x
      rw [hend0]
      exact N.coordinate_map_coordinate_inverse hx.1)
    (by
      change N.coordinate_map ((e ∘ η) 1) = y
      rw [hend1]
      exact N.coordinate_map_coordinate_inverse hy.1)
    (image_subset_iff.mpr hregion)
  apply hlength.trans
  have hmodel := model_path_length_le (z := z) (w := w) hσ hlen
  have hmodel' : roundCylinderMetric.pathELength (e ∘ η) 0 1 ≤
      ENNReal.ofReal (|w.2 - z.2| + Real.sqrt 2 * (Real.pi + 1)) := by
    rw [ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
    simpa only [abs_sub_comm, add_comm] using hmodel
  exact (mul_le_mul_of_nonneg_left hmodel' zero_le).trans_eq
    (ENNReal.ofReal_mul (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))).symm

end PoincareConjecture.EpsilonNeck
