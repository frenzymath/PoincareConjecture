import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Ellipticity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Reparametrization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.MetricJets












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

private theorem contDiffAt_bilinearComp_const
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {B : G → E →L[ℝ] E →L[ℝ] ℝ} {x : G} (hB : ContDiffAt ℝ ∞ B x)
    (T : F →L[ℝ] E) : ContDiffAt ℝ ∞ (fun y => (B y).bilinearComp T T) x := by
  let L₁ : (F →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] F →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ F E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let L₂ : (F →L[ℝ] F →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ F F ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have h₁ := hB.clm_comp (contDiffAt_const (c := T))
  have hf₁ : ContDiff ℝ ∞ L₁ := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (E := F →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] F →L[ℝ] ℝ) L₁
  have hf₂ : ContDiff ℝ ∞ L₂ := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (E := F →L[ℝ] F →L[ℝ] ℝ) (F := F →L[ℝ] F →L[ℝ] ℝ) L₂
  exact hf₂.contDiffAt.comp x
    ((hf₁.contDiffAt.comp x h₁).clm_comp (contDiffAt_const (c := T)))

theorem contDiff_roundCylinderEuclideanCoefficients :
    ContDiff ℝ ∞ roundCylinderEuclideanCoefficients := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact contDiffAt_bilinearComp_const
    (contDiff_roundCylinderModelCoefficients.contDiffAt.comp x
      (RiemannianMetric.lineModelEquiv 2).symm.contDiff.contDiffAt) _

theorem roundCylinderEuclideanCoefficients_symm
    (x v w : EuclideanSpace ℝ (Fin 3)) :
    roundCylinderEuclideanCoefficients x v w =
      roundCylinderEuclideanCoefficients x w v := by
  simp only [roundCylinderEuclideanCoefficients, ContinuousLinearMap.bilinearComp_apply,
    roundCylinderModelCoefficients_apply]
  rw [real_inner_comm]
  ring

theorem roundCylinderEuclideanCoefficients_pos
    (x v : EuclideanSpace ℝ (Fin 3)) (hv : v ≠ 0) :
    0 < roundCylinderEuclideanCoefficients x v v := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  have hvT : T v ≠ 0 := by
    intro hz
    apply hv
    apply T.injective
    simpa only [map_zero] using hz
  change 0 < roundCylinderModelCoefficients (T x) (T v) (T v)
  rw [roundCylinderModelCoefficients_apply, real_inner_self_eq_norm_sq]
  have hfactor : 0 < 2 * (16 / (‖(T x).1‖ ^ 2 + 4) ^ 2) := by positivity
  by_cases h₁ : (T v).1 = 0
  · have h₂ : (T v).2 ≠ 0 := by
      intro h₂
      exact hvT (Prod.ext h₁ h₂)
    simpa only [h₁, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add,
      ← sq] using sq_pos_of_ne_zero h₂
  · exact add_pos_of_pos_of_nonneg
      (mul_pos hfactor (sq_pos_of_pos (norm_pos_iff.mpr h₁))) (mul_self_nonneg _)


def roundCylinderEuclideanMetric : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)) :=
  RiemannianMetric.ofEuclideanCoefficients roundCylinderEuclideanCoefficients
    contDiff_roundCylinderEuclideanCoefficients roundCylinderEuclideanCoefficients_symm
    roundCylinderEuclideanCoefficients_pos

@[simp] theorem roundCylinderEuclideanMetric_inner (x v w : EuclideanSpace ℝ (Fin 3)) :
    roundCylinderEuclideanMetric.inner x v w =
      roundCylinderEuclideanCoefficients x v w := rfl

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem normalizedEuclideanCoefficients_contDiffAt (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContDiffAt ℝ ∞ (N.normalizedEuclideanCoefficients q s) x := by
  have hcoord : ContDiffAt ℝ ∞
      (fun y => (0, s) + (RiemannianMetric.lineModelEquiv 2).symm y) x :=
    contDiffAt_const.add (RiemannianMetric.lineModelEquiv 2).symm.contDiff.contDiffAt
  have hcoef : ContDiffAt ℝ ∞
      (fun y => N.normalizedCenteredCoefficients q
        ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm y)) x :=
    ContDiffAt.comp (f := fun y => (0, s) + (RiemannianMetric.lineModelEquiv 2).symm y)
      (g := N.normalizedCenteredCoefficients q) x
      (N.normalizedCenteredCoefficients_contDiffAt q hx) hcoord
  exact contDiffAt_bilinearComp_const hcoef
    (RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem normalizedEuclideanCoefficients_symm (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) (x v w : EuclideanSpace ℝ (Fin 3)) :
    N.normalizedEuclideanCoefficients q s x v w =
      N.normalizedEuclideanCoefficients q s x w v := by
  change N.scale⁻¹ ^ 2 * g.inner _ _ _ = N.scale⁻¹ ^ 2 * g.inner _ _ _
  rw [g.symm]


theorem exists_normalizedEuclideanCoefficients_realization
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (_D : LeviCivitaData h),
      h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s := by
  let B := N.normalizedEuclideanCoefficients q s
  let e := RiemannianMetric.lineModelEquiv 2
  let U : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | ((0, s) + e.symm x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp (continuous_const.add e.symm.continuous))
  have h0U : 0 ∈ U := by simpa only [U, mem_ofPred_eq, map_zero, add_zero] using hs
  have hB : ContDiffOn ℝ ∞ B U :=
    fun x hx => (N.normalizedEuclideanCoefficients_contDiffAt q s hx).contDiffWithinAt
  let c : ℝ := (2 * (max 1 ‖e.toContinuousLinearMap‖) ^ 2)⁻¹
  have hc : 0 < c := by dsimp only [c]; positivity
  have hlow (v : EuclideanSpace ℝ (Fin 3)) : c * ‖v‖ ^ 2 ≤ B 0 v v := by
    have h := quadratic_lower_rechart e (N.normalizedCenteredCoefficients q (0, s))
      (r := 1) (fun w => ?_) v
    · simpa only [one_pow, mul_one, B, normalizedEuclideanCoefficients, map_zero, add_zero]
        using h
    · have hl := N.normalizedCenteredCoefficients_lower q hs w
      have hε := N.epsilon_lt_half
      nlinarith [sq_nonneg ‖w‖]
  have hclose : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)), ‖B x - B 0‖ < c / 2 := by
    have h := ((hB.contDiffAt (hU.mem_nhds h0U)).continuousAt.sub
      (continuousAt_const (y := B 0))).norm
    exact h.eventually (Iio_mem_nhds (by
      simpa only [Pi.sub_apply, sub_self, norm_zero] using half_pos hc))
  obtain ⟨W, hW, hWo, h0W⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds h0U) hclose)
  have hWU : W ⊆ U := fun x hx => (hW hx).1
  have hpos : ∀ x ∈ W, ∀ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 → 0 < B x v v := by
    intro x hx v hv
    have he := ((B x - B 0) v).le_opNorm v
    have he' := (B x - B 0).le_opNorm v
    have habs : |B x v v - B 0 v v| ≤ ‖B x - B 0‖ * ‖v‖ ^ 2 := by
      simpa only [sub_apply, Real.norm_eq_abs, mul_assoc, ← sq] using
        he.trans (mul_le_mul_of_nonneg_right he' (norm_nonneg v))
    have hsq := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hsmall := mul_lt_mul_of_pos_right (hW hx).2 hsq
    have hdiff := (abs_le.mp habs).1
    nlinarith [hlow v]
  obtain ⟨h, D, V, hVo, h0V, hVW, heq⟩ := RiemannianMetric.exists_local_realization
    hWo h0W B (hB.mono hWU) (fun x _ => N.normalizedEuclideanCoefficients_symm q s x) hpos
  exact ⟨h, D, Filter.Eventually.mono (hVo.mem_nhds h0V) heq⟩



theorem exists_normalizedEuclideanCoefficients_curvature_control
    {α : ℝ} (hα : 0 < α) :
    let D₀ := roundCylinderEuclideanMetric.euclideanLeviCivitaData
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g), N.epsilon ≤ ε₀ → ∀ (q : UnitTwoSphere) {s : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∃ (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D : LeviCivitaData h),
        (h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s) ∧
        |D.scalarCurvature 0 - D₀.scalarCurvature 0| < α ∧
        ∀ i j : Fin 3,
          |D.ricci 0 (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
            D₀.ricci 0 (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)| < α := by
  dsimp only
  let D₀ := roundCylinderEuclideanMetric.euclideanLeviCivitaData
  obtain ⟨δ, hδ, hcurv⟩ := D₀.exists_scalar_ricci_control_of_metric_twoJet
    0 roundCylinderEuclideanBasis hα
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalizedEuclideanCoefficients_scalar_twoJet_bound.{u}
  refine ⟨min (1 / 200) (δ / (2 * C)), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N hε q s hs
  obtain ⟨h, D, heq⟩ := N.exists_normalizedEuclideanCoefficients_realization q hs
  refine ⟨h, D, heq, hcurv h D ?_⟩
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
  exact (hbound N q hs r hr i j).trans_lt hsmall

end EpsilonNeck
end PoincareConjecture
