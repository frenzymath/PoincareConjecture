import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Laplacian.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.FourJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.EuclideanModel











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem roundCylinderEuclideanMetric_scalar_laplacian
    (D : LeviCivitaData roundCylinderEuclideanMetric)
    (x : EuclideanSpace ℝ (Fin 3)) : D.laplacian D.scalarCurvature x = 0 := by
  have heq : D.scalarCurvature = fun _ => (1 : ℝ) :=
    funext (roundCylinderEuclideanMetric_scalarCurvature D)
  rw [heq, D.laplacian_eq_sum_fderiv_sub_christoffel contDiffAt_const]
  simp

namespace EpsilonNeck



theorem exists_normalized_scalar_laplacian_control {α : ℝ} (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g), N.epsilon ≤ ε₀ →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ {h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (D : LeviCivitaData h),
      (h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s) →
        |D.laplacian D.scalarCurvature 0| < α := by
  let D₀ := roundCylinderEuclideanMetric.euclideanLeviCivitaData
  obtain ⟨δ, hδ, hcontrol⟩ := D₀.exists_scalar_laplacian_control_of_metric_fourJet
    0 roundCylinderEuclideanBasis hα
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalizedEuclideanCoefficients_scalar_fourJet_bound.{u}
  refine ⟨min (1 / 200) (δ / (2 * C)), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N hε q s hs h D heq
  have hεsmall : N.epsilon ≤ 1 / 4 :=
    (hε.trans (min_le_left _ _)).trans (by norm_num)
  have hlap := hcontrol h D (by
    intro r hr i j
    have hjet : (fun x => h.inner x (roundCylinderEuclideanBasis i)
        (roundCylinderEuclideanBasis j) -
          roundCylinderEuclideanMetric.inner x (roundCylinderEuclideanBasis i)
            (roundCylinderEuclideanBasis j)) =ᶠ[𝓝 0]
        (fun x => N.normalizedEuclideanCoefficients q s x
            (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
          roundCylinderEuclideanCoefficients x
            (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) := by
      filter_upwards [heq] with x hx
      change h.euclideanCoefficients x _ _ - _ = _
      rw [hx, roundCylinderEuclideanMetric_inner]
    have hsmooth (h' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) :
        ContDiffAt ℝ r (fun x => h'.inner x (roundCylinderEuclideanBasis i)
          (roundCylinderEuclideanBasis j)) 0 :=
      (((h'.contDiffAt_euclideanCoefficients 0).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const).of_le (by norm_cast; exact le_top)
    rw [← iteratedFDeriv_sub_apply (hsmooth h) (hsmooth roundCylinderEuclideanMetric)]
    simp only [Pi.sub_def]
    rw [(hjet.iteratedFDeriv ℝ r).self_of_nhds]
    have hε' := hε.trans (min_le_right (1 / 200) (δ / (2 * C)))
    have hsmall : C * N.epsilon < δ := by
      have hh := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp hε'
      nlinarith
    exact (hbound N hεsmall q hs r hr i j).trans_lt hsmall)
  simpa only [roundCylinderEuclideanMetric_scalar_laplacian, sub_zero] using hlap



theorem exists_ambient_scalar_laplacian_control {α : ℝ} (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ ε₀ →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        |N.scale ^ 4 * D.laplacian D.scalarCurvature (N.coordinate_map (q, s))| < α := by
  obtain ⟨ε₀, hε₀, hsmall, hcontrol⟩ := exists_normalized_scalar_laplacian_control.{u} hα
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hε q s hs
  obtain ⟨h, Dh, heq⟩ := N.exists_normalizedEuclideanCoefficients_realization q hs
  rw [← N.normalized_realization_scalar_laplacian D q hs Dh heq]
  exact hcontrol N hε q hs Dh heq



theorem exists_normalized_scalar_laplacian_lower_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ ε₀ →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        -(1 / 6 : ℝ) ≤ N.scale ^ 4 *
          D.laplacian D.scalarCurvature (N.coordinate_map (q, s)) := by
  obtain ⟨ε₀, hε₀, hsmall, hcontrol⟩ :=
    exists_ambient_scalar_laplacian_control.{u} (α := 1 / 6) (by norm_num)
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hε q s hs
  exact (abs_lt.mp (hcontrol N D hε q hs)).1.le

end EpsilonNeck
end PoincareConjecture
