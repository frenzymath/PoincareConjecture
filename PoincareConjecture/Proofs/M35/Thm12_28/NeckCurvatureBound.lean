import PoincareConjecture.Proofs.M35.Thm12_28.NeckCurvatureLimit

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

private theorem cylinderChart_zero (q : UnitTwoSphere) : cylinderChart q 0 = (q, 0) := by
  change ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm (cylinderCoordinateEquiv 0).1,
    (cylinderCoordinateEquiv 0).2) = _
  rw [map_zero]
  apply Prod.ext
  · have h := (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv
      (mem_chart_source (EuclideanSpace ℝ (Fin 2)) q)
    simpa only [sphere_chart_center, Prod.fst_zero] using h
  · rfl

theorem exists_cylinder_curvature_bound :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
        (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x) (q : UnitTwoSphere),
        RoundCylinderClose epsilon 0 (roundCylinderPullback g N.coordinate) →
          D.curvatureTensorNorm (N.coordinate (q, 0)) < 2 := by
  classical
  by_contra h
  push Not at h
  have hbad (n : ℕ) := h (min (1 / 4) (1 / ((n : ℝ) + 1))) (by positivity)
  choose epsilon he hemax g D x N q hclose hlarge using hbad
  have hequarter (n : ℕ) : epsilon n ≤ 1 / 4 :=
    (hemax n).trans (min_le_left _ _)
  have hk (n : ℕ) : 2 ≤ ⌊(epsilon n)⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div, le_div_iff₀ (he n)]
    norm_num
    linarith [hequarter n]
  have hezero : Tendsto epsilon atTop (𝓝 0) :=
    squeeze_zero (fun n => (he n).le)
      (fun n => (hemax n).trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hp (n : ℕ) : (cylinderCoordinateEquiv (0 : EuclideanSpace ℝ (Fin 3))).2 ∈
      Ioo (-(epsilon n)⁻¹) (epsilon n)⁻¹ := by
    simp only [map_zero, Prod.snd_zero, mem_Ioo]
    exact ⟨neg_neg_of_pos (inv_pos.mpr (he n)), inv_pos.mpr (he n)⟩
  have hreal (n : ℕ) : ∃ (G : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
      (DG : LeviCivitaData G),
      (∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)), G.euclideanCoefficients y =
        (g n).pullbackCoefficients ((N n).coordinate ∘ cylinderChart (q n)) y) ∧
      DG.curvatureTensorNorm 0 = (D n).curvatureTensorNorm ((N n).coordinate (q n, 0)) := by
    obtain ⟨G, DG, hG, hnorm⟩ :=
      (N n).exists_euclidean_curvature_realization (g n) (D n) (q n) (hp n)
    refine ⟨G, DG, hG, ?_⟩
    exact hnorm.trans (congrArg (D n).curvatureTensorNorm
      (congrArg (N n).coordinate (cylinderChart_zero (q n))))
  choose G DG hG hnorm using hreal
  have hlimit := cylinder_curvatureTensorNorm_tendsto G DG epsilon
    (fun n => roundCylinderPullback (g n) (N n).coordinate) q he hk hclose hezero
    (fun n i j => (N n).euclidean_realization_coefficient_germ
      (g n) (q n) (hp n) (G n) (hG n) i j)
  obtain ⟨n, hn⟩ := (hlimit.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))).exists
  have hge := hlarge n
  rw [← hnorm n] at hge
  linarith

theorem exists_neck_center_curvature_bound :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
        (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x),
        RoundCylinderClose epsilon 0 (roundCylinderPullback g N.coordinate) →
          D.curvatureTensorNorm x < 2 := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_cylinder_curvature_bound
  refine ⟨delta, hdelta, fun epsilon he hedelta g D x N hclose => ?_⟩
  obtain ⟨q, hq⟩ := N.center_sphere
  simpa only [hq] using hbound epsilon he hedelta g D x N q hclose

end PoincareConjecture.M35
