import PoincareConjecture.Proofs.M60.Mathlib.SUConvexIntegral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem suBilinear_diagonal_convex (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v, 0 ≤ B v v) : ConvexOn ℝ univ (fun v => B v v) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ a b ha hb hab
  have hid : a * B v v + b * B w w - B (a • v + b • w) (a • v + b • w) =
      a * b * B (v - w) (v - w) := by
    rw [show a = 1 - b by linarith]
    simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul]
    ring
  change B (a • v + b • w) (a • v + b • w) ≤ a * B v v + b * B w w
  have := mul_nonneg (mul_nonneg ha hb) (hB (v - w))
  linarith

def suRegularizedQuadratic (B : E →L[ℝ] E →L[ℝ] ℝ) (c p : ℝ) (v : E) : ℝ :=
  (c + B v v) ^ p

theorem suRegularizedQuadratic_continuous (B : E →L[ℝ] E →L[ℝ] ℝ)
    (c : ℝ) {p : ℝ} (hp : 0 ≤ p) : Continuous (suRegularizedQuadratic B c p) := by
  exact (Real.continuous_rpow_const hp).comp
    (continuous_const.add (B.continuous.clm_apply continuous_id))

theorem suRegularizedQuadratic_convex (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v, 0 ≤ B v v) {c p : ℝ} (hc : 0 ≤ c) (hp : 1 ≤ p) :
    ConvexOn ℝ univ (suRegularizedQuadratic B c p) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ a b ha hb hab
  have hq := (suBilinear_diagonal_convex B hB).2 (mem_univ v) (mem_univ w) ha hb hab
  have hmix : c + B (a • v + b • w) (a • v + b • w) ≤
      a * (c + B v v) + b * (c + B w w) := by
    change B (a • v + b • w) (a • v + b • w) ≤ a * B v v + b * B w w at hq
    nlinarith
  exact (Real.rpow_le_rpow (add_nonneg hc (hB _)) hmix (by linarith)).trans
    ((convexOn_rpow hp).2 (add_nonneg hc (hB v)) (add_nonneg hc (hB w)) ha hb hab)

section Measurable

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

local instance : MeasurableSpace (E →L[ℝ] E →L[ℝ] ℝ) := borel _
local instance : BorelSpace (E →L[ℝ] E →L[ℝ] ℝ) := ⟨rfl⟩

theorem suRegularizedQuadratic_measurable
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (hB : Measurable B)
    (c : X → ℝ) (hc : Measurable c) {p : ℝ} (hp : 0 ≤ p) :
    Measurable (fun q : X × E => suRegularizedQuadratic (B q.1) (c q.1) p q.2) := by
  have hquad : Continuous (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × E => q.1 q.2 q.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  exact (Real.continuous_rpow_const hp).measurable.comp
    ((hc.comp measurable_fst).add (hquad.measurable.comp
      ((hB.comp measurable_fst).prodMk measurable_snd)))

theorem suRegularizedQuadratic_le_liminf
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (hB : Measurable B)
    (hpos : ∀ x v, 0 ≤ B x v v) (c : X → ℝ) (hc : Measurable c)
    (hc0 : ∀ x, 0 ≤ c x) {p : ℝ} (hp : 1 ≤ p)
    {u : ℕ → Lp E 2 mu} {v : Lp E 2 mu}
    (hw : ∀ L : StrongDual ℝ (Lp E 2 mu),
      Tendsto (fun n => L (u n)) atTop (𝓝 (L v))) :
    (∫⁻ x, ENNReal.ofReal (suRegularizedQuadratic (B x) (c x) p (v x)) ∂mu) ≤
      liminf (fun n => ∫⁻ x,
        ENNReal.ofReal (suRegularizedQuadratic (B x) (c x) p (u n x)) ∂mu) atTop := by
  exact suConvexIntegral_le_liminf _
    (suRegularizedQuadratic_measurable B hB c hc (by linarith))
    (fun x => suRegularizedQuadratic_continuous (B x) (c x) (by linarith))
    (fun x => suRegularizedQuadratic_convex (B x) (hpos x) (hc0 x) hp) hw

end Measurable

end PoincareConjecture.M60
