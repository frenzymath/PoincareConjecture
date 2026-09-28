import PoincareConjecture.Proofs.M35.Thm12_28.NeckCurvatureLimit
import PoincareConjecture.Proofs.M35.CapGeometry.NeckScalarFloor
import PoincareConjecture.Definitions.M34StandardCapExistence












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35



theorem cylinder_curvatureTensorNorm_tendsto_at_fixed_time
    (g : ℕ → RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (D : ∀ n, LeviCivitaData (g n)) (epsilon : ℕ → ℝ)
    (B : ℕ → RoundCylinderTwoTensor) (q : ℕ → UnitTwoSphere)
    {t : ℝ} (ht : t ∈ Ico 0 1)
    (he : ∀ n, 0 < epsilon n) (hk : ∀ n, 2 ≤ ⌊(epsilon n)⁻¹⌋₊)
    (hclose : ∀ n, RoundCylinderClose (epsilon n) t (B n))
    (hlim : Tendsto epsilon atTop (𝓝 0))
    (hcoeff : ∀ n (i j : Fin 3),
      (fun p : EuclideanSpace ℝ (Fin 3) => (g n).inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
      (fun p => roundCylinderTensorCoefficient (B n)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q n)) (cylinderCoordinateEquiv p) i j)) :
    Tendsto (fun n => (D n).curvatureTensorNorm 0) atTop (𝓝 (1 / (1 - t))) := by
  let model := cylinderEuclideanMetric t ht.2
  let modelD := cylinderEuclideanConnection t ht.2
  have hjet (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) :
      Tendsto (fun n => iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) =>
        (g n).inner p (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) => model.inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0)) := by
    apply tendsto_cylinder_jet_of_components
    intro a
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hbound (n : ℕ) :
        ‖iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) => (g n).inner p
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
            0 (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k)) -
          iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) => model.inner p
            (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
            0 (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))‖ ≤ 52 * epsilon n := by
      have hr' : (r : ℕ∞ω) ≤ ∞ := by norm_cast; exact le_top
      have hsub := iteratedFDeriv_sub_apply
        ((metric_component_contDiffAt (g n) 0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)).of_le hr')
        ((metric_component_contDiffAt model 0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)).of_le hr')
      have hsv := congrArg (fun A => A (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))) hsub
      have hb := (hclose n).euclidean_metric_error_component_abs_lt
        (he n) (by linarith [ht.1]) ht.2 (q n) (hk n) (g n) i j (hcoeff n i j) hr a
      exact ((congrArg abs hsv).symm.trans_lt hb).le
    exact squeeze_zero (fun n => norm_nonneg _) hbound
      (by simpa only [mul_zero] using hlim.const_mul 52)
  have hnorm := LeviCivitaData.tendsto_curvatureTensorNorm_of_scalar_metric_jets
    D modelD 0 (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis hjet
  have hmodel : modelD.curvatureTensorNorm 0 = 1 / (1 - t) := by
    have h := cylinder_curvatureTensorNorm_center t ht.2 modelD (q 0) 0
    simpa only [← Prod.zero_eq_mk, map_zero] using h
  exact hmodel ▸ hnorm



theorem exists_cylinder_curvature_lower_bound_at_time {t : ℝ} (ht : t ∈ Ico 0 1) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
        (x : StandardCapSpace) (N : StandardCylinderPatch epsilon⁻¹ x) (q : UnitTwoSphere),
        RoundCylinderClose epsilon t (roundCylinderPullback g N.coordinate) →
          1 / (2 * (1 - t)) < D.curvatureTensorNorm (N.coordinate (q, 0)) := by
  classical
  by_contra h
  push Not at h
  have hbad (n : ℕ) := h (min (1 / 4) (1 / ((n : ℝ) + 1))) (by positivity)
  choose epsilon he hemax g D x N q hclose hsmall using hbad
  have hk (n : ℕ) : 2 ≤ ⌊(epsilon n)⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div, le_div_iff₀ (he n)]
    have hquarter := (hemax n).trans (min_le_left _ _)
    norm_num
    linarith
  have hezero : Tendsto epsilon atTop (𝓝 0) :=
    squeeze_zero (fun n => (he n).le)
      (fun n => (hemax n).trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hp (n : ℕ) : (cylinderCoordinateEquiv (0 : EuclideanSpace ℝ (Fin 3))).2 ∈
      Ioo (-(epsilon n)⁻¹) (epsilon n)⁻¹ := by
    simp only [map_zero, Prod.snd_zero, mem_Ioo]
    exact ⟨neg_neg_of_pos (inv_pos.mpr (he n)), inv_pos.mpr (he n)⟩
  have hz (q : UnitTwoSphere) : cylinderChart q 0 = (q, 0) := by
    change ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm (cylinderCoordinateEquiv 0).1,
      (cylinderCoordinateEquiv 0).2) = _
    rw [map_zero]
    apply Prod.ext
    · have h := (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv
        (mem_chart_source (EuclideanSpace ℝ (Fin 2)) q)
      simpa only [sphere_chart_center, Prod.fst_zero] using h
    · rfl
  have hreal (n : ℕ) :=
    (N n).exists_euclidean_curvature_realization (g n) (D n) (q n) (hp n)
  choose G DG hG hnorm using hreal
  have hlimit := cylinder_curvatureTensorNorm_tendsto_at_fixed_time G DG epsilon
    (fun n => roundCylinderPullback (g n) (N n).coordinate) q ht he hk hclose hezero
    (fun n i j => (N n).euclidean_realization_coefficient_germ
      (g n) (q n) (hp n) (G n) (hG n) i j)
  have hhalf : 1 / (2 * (1 - t)) < 1 / (1 - t) := by
    have htpos : 0 < 1 - t := sub_pos.mpr ht.2
    field_simp
    nlinarith
  obtain ⟨n, hn⟩ := (hlimit.eventually (eventually_gt_nhds hhalf)).exists
  rw [hnorm n, hz] at hn
  exact not_lt_of_ge (hsmall n) hn

end PoincareConjecture.M35

namespace PoincareConjecture.RepairedStandardCapExistenceData



theorem exists_compact_exterior_terminal_scalar_floor
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {t : ℝ}
    (ht : t ∈ Ico 0 E.flow.base.lifetime) :
    ∃ K : Set StandardCapSpace, IsCompact K ∧ ∀ x, x ∉ K →
      1 / (2 * (1 - t)) < (E.flow.connection t).scalarCurvature x := by
  obtain ⟨delta, hdelta, hfloor⟩ :=
    M35.exists_cylinder_curvature_lower_bound_at_time (E.lifetime_one ▸ ht)
  obtain ⟨C⟩ := E.asymptotic t ht delta hdelta
  refine ⟨C.compact_set, C.compact, ?_⟩
  intro x hx
  obtain ⟨N, hN⟩ := C.patches x hx
  obtain ⟨q, hq⟩ := N.center_sphere
  have hclose : RoundCylinderClose delta t
      (roundCylinderPullback (E.flow.metric t) N.coordinate) := by
    obtain ⟨hsmooth, bound, hbound, hjet⟩ := hN
    have htime : t ∈ Icc 0 t := ⟨ht.1, le_rfl⟩
    refine ⟨?_, bound, hbound, ?_⟩
    · simpa only [zero_add, div_one, one_mul] using hsmooth t htime
    · simpa only [zero_add, div_one, one_mul] using hjet t htime
  have hnorm := hfloor delta hdelta le_rfl (E.flow.metric t) (E.flow.connection t)
    x N q hclose
  rw [hq] at hnorm
  exact hnorm.trans_le
    ((E.flow.connection t).curvatureTensorNorm_le_scalar_of_nonnegative_sectional_three
      (P.tensor_calculus 3 StandardCapSpace _ _) x (E.nonnegative_sectional t ht x))

end PoincareConjecture.RepairedStandardCapExistenceData
