import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.LocallyConvex.Bounded










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

section ConstantCharts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hchart : ∀ x y : M,
      chartAt (EuclideanSpace ℝ (Fin n)) x = chartAt (EuclideanSpace ℝ (Fin n)) y)

include hchart

private lemma constant_chart_tangent_symmL (x y : M) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).symmL ℝ y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    rw [hchart x y]
    exact mem_chart_source _ y
  rw [TangentBundle.symmL_trivializationAt_eq_core hy]
  have hachart : achart (EuclideanSpace ℝ (Fin n)) x =
      achart (EuclideanSpace ℝ (Fin n)) y := Subtype.ext (hchart x y)
  rw [hachart]
  apply ContinuousLinearMap.ext
  intro v
  exact (tangentBundleCore (𝓡 n) M).coordChange_self
    (achart (EuclideanSpace ℝ (Fin n)) y) y (mem_chart_source _ y) v

lemma constant_chart_bilinear_coordinates
    (x y : M) (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun z : M => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x y x y B = B := by
  have hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun z : M => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x).baseSet := by
    simp [hchart x y]
  ext v w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp,
    Function.comp_apply, constant_chart_tangent_symmL hchart]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy]
  simp +instances [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    constant_chart_tangent_symmL hchart]
  rfl

private theorem contMDiff_constant_chart_section
    (B : M → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContMDiff (𝓡 n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞ B) :
    ContMDiff (𝓡 n) ((𝓡 n).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
        x (B x)) := by
  intro x
  rw [Bundle.contMDiffAt_section]
  simp only [hom_trivializationAt_apply, constant_chart_bilinear_coordinates hchart]
  exact hB x

private noncomputable def constantChartMetric
    (B : M → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hsmooth : ContMDiff (𝓡 n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞ B)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hlower : ∀ x, ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ B x v v) :
    RiemannianMetric n M where
  inner x := B x
  symm := hsymm
  pos x := by
    change ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < B x v v
    intro v hv
    obtain ⟨c, hc, hbound⟩ := hlower x
    have hv' : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    exact (mul_pos hc hv').trans_le (hbound v)
  isVonNBounded x := by
    obtain ⟨c, hc, hbound⟩ := hlower x
    change Bornology.IsVonNBounded ℝ
      {v : EuclideanSpace ℝ (Fin n) | B x v v < 1}
    apply (NormedSpace.isVonNBounded_closedBall ℝ (EuclideanSpace ℝ (Fin n)) (c⁻¹ + 1)).subset
    intro v hv
    change B x v v < 1 at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖v‖ ^ 2 < c⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hc]
      nlinarith [hbound v]
    nlinarith [sq_nonneg (‖v‖ - 1 / 2)]
  contMDiff := contMDiff_constant_chart_section hchart B hsmooth



theorem exists_of_constant_chart_limit
    (Bseq : ℕ → M → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hsmooth : ContMDiff (𝓡 n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞ B)
    (hsymm : ∀ k x v w, Bseq k x v w = Bseq k x w v)
    (hconv : ∀ x v w, Tendsto (fun k => Bseq k x v w) atTop (𝓝 (B x v w)))
    (hlower : ∀ x, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ v, c * ‖v‖ ^ 2 ≤ Bseq k x v v) :
    ∃ g : RiemannianMetric n M, ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = B x v w := by
  have hsymmB : ∀ x v w, B x v w = B x w v := by
    intro x v w
    apply tendsto_nhds_unique (hconv x v w)
    exact (hconv x w v).congr' (Eventually.of_forall fun k => hsymm k x w v)
  have hlowerB : ∀ x, ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ B x v v := by
    intro x
    obtain ⟨c, hc, hbound⟩ := hlower x
    refine ⟨c, hc, fun v => ?_⟩
    exact ge_of_tendsto (hconv x v v) (hbound.mono fun k hk => hk v)
  exact ⟨constantChartMetric hchart B hsmooth hsymmB hlowerB, fun _ _ _ => rfl⟩

end ConstantCharts



theorem exists_of_coordinate_limit
    {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n)))
    (Bseq : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hsmooth : ContDiffOn ℝ ∞ B U)
    (hsymm : ∀ k x, x ∈ U → ∀ v w, Bseq k x v w = Bseq k x w v)
    (hconv : ∀ x, x ∈ U → ∀ v w,
      Tendsto (fun k => Bseq k x v w) atTop (𝓝 (B x v w)))
    (hlower : ∀ x, x ∈ U → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ v, c * ‖v‖ ^ 2 ≤ Bseq k x v v) :
    ∃ g : RiemannianMetric n U, ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = B x v w := by
  apply exists_of_constant_chart_limit (M := U) (fun x y => by simp [Opens.chartAt_eq])
    (fun k x => Bseq k x) (fun x => B x) ?_
    (fun k x => hsymm k x x.property) (fun x => hconv x x.property)
    (fun x => hlower x x.property)
  intro x
  exact ((hsmooth x x.property).contDiffAt (U.isOpen.mem_nhds x.property)).contMDiffAt.comp x
    (contMDiff_subtype_val (I := 𝓡 n) (U := U) x)

end PoincareConjecture.RiemannianMetric
