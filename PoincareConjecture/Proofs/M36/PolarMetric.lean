import PoincareConjecture.Proofs.M36.AdaptedPolar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => StandardCapSpace
local notation "C" => StandardCylinderCoordinates
local notation "I" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

noncomputable def adaptedAngularEmbedding (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) : E₃ := (cylindricalBoundaryDirection g₀ theta).1

theorem adaptedAngularEmbedding_contMDiff (g₀ : StandardInitialMetric) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (adaptedAngularEmbedding g₀) := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  exact (contMDiff_coe_sphere (E := E₃) (n := 2)).comp
    (cylindricalBoundaryDirection_contMDiff g₀)

theorem adaptedAngularEmbedding_norm (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) : ‖adaptedAngularEmbedding g₀ theta‖ = 1 := by
  simp [adaptedAngularEmbedding]

theorem adaptedAngularEmbedding_inner_mvfderiv (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) (v : E₂) :
    inner ℝ (adaptedAngularEmbedding g₀ theta)
      (mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) theta v) = 0 := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  let q := cylindricalBoundaryDirection g₀ theta
  have hmem : mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.1) q
      (mfderiv (𝓡 2) (𝓡 2) (cylindricalBoundaryDirection g₀) theta v) ∈ (ℝ ∙ q.1)ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := 2) q]
    exact ⟨_, rfl⟩
  have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
  have hc := mfderiv_comp theta
    ((contMDiff_coe_sphere (n := 2) (m := ∞) q).mdifferentiableAt (by simp))
    ((cylindricalBoundaryDirection_contMDiff g₀ theta).mdifferentiableAt (by simp))
  have hv : mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) theta v =
      mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.1) q
        (mfderiv (𝓡 2) (𝓡 2) (cylindricalBoundaryDirection g₀) theta v) := by
    exact congrArg (fun L => L v) hc
  rw [hv]
  exact h

theorem adaptedPolarPoint_mvfderiv (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (v : C) :
    mvfderiv I (adaptedPolarPoint g₀) z v =
      radialEuclideanRadius g₀ z.2 •
        mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1 +
      ((radialSpeed g₀ (radialEuclideanRadius g₀ z.2))⁻¹ * v.2) •
        adaptedAngularEmbedding g₀ z.1 := by
  have hr : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun w : StandardCylinderSpace => radialEuclideanRadius g₀ w.2) z :=
    (((radialEuclideanRadius_contDiff g₀).contMDiff.comp contMDiff_snd) z).mdifferentiableAt
      (by simp)
  have ha : MDifferentiableAt I (𝓡 3)
      (fun w : StandardCylinderSpace => adaptedAngularEmbedding g₀ w.1) z :=
    (((adaptedAngularEmbedding_contMDiff g₀).comp contMDiff_fst) z).mdifferentiableAt
      (by simp)
  have hR : mvfderiv I (fun w : StandardCylinderSpace => radialEuclideanRadius g₀ w.2) z v =
      (radialSpeed g₀ (radialEuclideanRadius g₀ z.2))⁻¹ * v.2 := by
    change mvfderiv I (radialEuclideanRadius g₀ ∘ Prod.snd) z v = _
    erw [mvfderiv_comp z
      (((radialEuclideanRadius_contDiff g₀).contMDiff z.2).mdifferentiableAt (by simp))
      mdifferentiableAt_snd, mfderiv_snd]
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (radialEuclideanRadius g₀) z.2 v.2 = _
    rw [mfderiv_eq_fderiv, (radialEuclideanRadius_hasDerivAt g₀ z.2).hasFDerivAt.fderiv]
    change v.2 * (radialSpeed g₀ (radialEuclideanRadius g₀ z.2))⁻¹ = _
    ring
  have hA : mvfderiv I (fun w : StandardCylinderSpace => adaptedAngularEmbedding g₀ w.1) z v =
      mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1 := by
    have hf : MDifferentiableAt I (𝓡 2) (Prod.fst : StandardCylinderSpace → UnitTwoSphere) z :=
      mdifferentiableAt_fst
    have hc := mfderiv_comp z
      ((adaptedAngularEmbedding_contMDiff g₀ z.1).mdifferentiableAt (by simp))
      hf
    rw [mfderiv_fst] at hc
    exact congrArg (fun L => L v) hc
  change mvfderiv I (fun w : StandardCylinderSpace =>
    radialEuclideanRadius g₀ w.2 • adaptedAngularEmbedding g₀ w.1) z v = _
  rw [mvfderiv_fun_smul hr ha]
  change radialEuclideanRadius g₀ z.2 •
      mvfderiv I (fun w : StandardCylinderSpace => adaptedAngularEmbedding g₀ w.1) z v +
    (mvfderiv I (fun w : StandardCylinderSpace => radialEuclideanRadius g₀ w.2) z v) •
      adaptedAngularEmbedding g₀ z.1 = _
  rw [hA, hR]

theorem standard_metric_radial_split (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) (theta : UnitTwoSphere) (w : E₃)
    (hw : inner ℝ theta.1 w = 0) (a : ℝ) :
    g₀.metric.inner (r • theta.1) (r • w + a • theta.1) (r • w + a • theta.1) =
      euclideanWarpRadius g₀ r ^ 2 * inner ℝ w w + radialSpeed g₀ r ^ 2 * a ^ 2 := by
  have hn : ‖r • theta.1‖ = r := by simp [norm_smul, abs_of_pos hr]
  have hx : r • theta.1 ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hn
    exact hr.ne hn
  have hdir : ‖r • theta.1‖⁻¹ • (r • theta.1) = theta.1 := by
    rw [hn, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hu : inner ℝ theta.1 theta.1 = 1 := by
    rw [real_inner_self_eq_norm_sq]
    simp
  have hwu : inner ℝ w theta.1 = 0 := by rw [real_inner_comm, hw]
  rw [standard_metric_radial_formula g₀ _ hx, hdir, hn]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hw, hwu, hu, mul_zero, add_zero, zero_add, mul_one]
  rw [euclideanWarpRadius, mul_pow, radialSpeed,
    Real.sq_sqrt (axisTangentialCoefficient_pos g₀ r).le,
    Real.sq_sqrt (axisRadialCoefficient_pos g₀ r).le]
  ring

theorem adaptedPolarPoint_quadratic (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 < z.2) (v : C) :
    g₀.metric.inner (adaptedPolarPoint g₀ z)
      (mfderiv I (𝓡 3) (adaptedPolarPoint g₀) z v)
      (mfderiv I (𝓡 3) (adaptedPolarPoint g₀) z v) =
      euclideanWarpRadius g₀ (radialEuclideanRadius g₀ z.2) ^ 2 *
        inner ℝ (mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1)
          (mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1) + v.2 ^ 2 := by
  change g₀.metric.inner (adaptedPolarPoint g₀ z)
    (mvfderiv I (adaptedPolarPoint g₀) z v)
    (mvfderiv I (adaptedPolarPoint g₀) z v) = _
  rw [adaptedPolarPoint_mvfderiv]
  change g₀.metric.inner
    (radialEuclideanRadius g₀ z.2 • (cylindricalBoundaryDirection g₀ z.1).1)
    (radialEuclideanRadius g₀ z.2 •
        mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1 +
      ((radialSpeed g₀ (radialEuclideanRadius g₀ z.2))⁻¹ * v.2) •
        (cylindricalBoundaryDirection g₀ z.1).1)
    (radialEuclideanRadius g₀ z.2 •
        mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1 +
      ((radialSpeed g₀ (radialEuclideanRadius g₀ z.2))⁻¹ * v.2) •
        (cylindricalBoundaryDirection g₀ z.1).1) = _
  rw [standard_metric_radial_split g₀ ((radialEuclideanRadius_pos_iff g₀ _).mpr hz) _ _
    (adaptedAngularEmbedding_inner_mvfderiv g₀ z.1 v.1)]
  field_simp [(radialSpeed_pos g₀ (radialEuclideanRadius g₀ z.2)).ne']

theorem adaptedPolarPoint_eq_end (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : g₀.cylindrical_end.radius ≤ z.2) :
    adaptedPolarPoint g₀ z =
      g₀.cylindrical_end.coordinate (z.1, z.2 - g₀.cylindrical_end.radius) := by
  rw [cylindrical_coordinate_radial g₀ _ (sub_nonneg.mpr hz)]
  change radialEuclideanRadius g₀ z.2 • adaptedAngularEmbedding g₀ z.1 =
    radialEuclideanRadius g₀ (g₀.cylindrical_end.radius +
      (z.2 - g₀.cylindrical_end.radius)) • adaptedAngularEmbedding g₀ z.1
  congr 2
  ring

end PoincareConjecture.M36
