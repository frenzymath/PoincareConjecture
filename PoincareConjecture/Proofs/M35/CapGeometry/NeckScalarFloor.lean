import PoincareConjecture.Proofs.M35.Thm12_28.NeckCurvatureScale
import PoincareConjecture.Proofs.M35.CapGeometry.CoreBallVolume

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

theorem exists_cylinder_curvature_lower_bound :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
        (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x) (q : UnitTwoSphere),
        RoundCylinderClose epsilon 0 (roundCylinderPullback g N.coordinate) →
          1 / 2 < D.curvatureTensorNorm (N.coordinate (q, 0)) := by
  classical
  by_contra h
  push Not at h
  have hbad (n : ℕ) := h (min (1 / 4) (1 / ((n : ℝ) + 1))) (by positivity)
  choose epsilon he hemax g D x N q hclose hsmall using hbad
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
    exact ⟨G, DG, hG, hnorm.trans (congrArg (D n).curvatureTensorNorm
      (congrArg (N n).coordinate (cylinderChart_zero (q n))))⟩
  choose G DG hG hnorm using hreal
  have hlimit := cylinder_curvatureTensorNorm_tendsto G DG epsilon
    (fun n => roundCylinderPullback (g n) (N n).coordinate) q he hk hclose hezero
    (fun n i j => (N n).euclidean_realization_coefficient_germ
      (g n) (q n) (hp n) (G n) (hG n) i j)
  obtain ⟨n, hn⟩ := (hlimit.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
  have hle := hsmall n
  rw [← hnorm n] at hle
  exact (not_lt_of_ge hle) hn

theorem exists_scaled_nonnegative_cylinder_scalar_floor (P : RicciFlowCurvatureTheory.{0}) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ (A : StandardCylinderAtlas) (g : RiemannianMetric 3 StandardCapSpace)
        (D : LeviCivitaData g) (Q : ℝ), 0 < Q →
        ∀ (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x)
          (q : UnitTwoSphere), StandardSpatialCylinderClose A g epsilon Q N →
          (∀ v w : TangentSpace (𝓡 3) (N.coordinate (q, 0)),
            0 ≤ D.curvatureTensor (N.coordinate (q, 0)) v w v w) →
          Q / 2 < D.scalarCurvature (N.coordinate (q, 0)) := by
  obtain ⟨delta, hdelta, hbound⟩ := exists_cylinder_curvature_lower_bound
  refine ⟨delta, hdelta, ?_⟩
  intro epsilon he hedelta A g D Q hQ x N q hclose hsec
  let G := M13.scaleSmoothMetric g Q hQ
  let DG := M13.scaleLeviCivitaData D Q hQ
  have hscaled : RoundCylinderClose epsilon 0
      (roundCylinderPullback G N.coordinate) := hclose
  have h := hbound epsilon he hedelta G DG x N q hscaled
  have hnorm := M13.homothety_curvatureTensorNorm_eq g G
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ) D DG (N.coordinate (q, 0))
  change DG.curvatureTensorNorm (N.coordinate (q, 0)) =
    D.curvatureTensorNorm (N.coordinate (q, 0)) / Q at hnorm
  rw [hnorm] at h
  have hlower : Q / 2 < D.curvatureTensorNorm (N.coordinate (q, 0)) := by
    have hmul := (lt_div_iff₀ hQ).mp h
    linarith
  exact hlower.trans_le (D.curvatureTensorNorm_le_scalar_of_nonnegative_sectional_three
    (P.tensor_calculus 3 StandardCapSpace g D) (N.coordinate (q, 0)) hsec)

end PoincareConjecture.M35
