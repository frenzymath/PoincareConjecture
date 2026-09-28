import PoincareConjecture.Proofs.M03.Existence.EuclideanDerivativeClosedNative

set_option autoImplicit false

open MeasureTheory Filter LineDeriv
open scoped Topology ENNReal SchwartzMap LineDeriv

noncomputable section

namespace PoincareConjecture.EuclideanDerivativeNative

variable {n : ℕ}

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

theorem inner_weightedSchwartzLineDeriv (a φ f : 𝓢(ModelE, ℝ)) (v : ModelE) :
    inner ℝ (φ.toLp 2 volume)
        ((SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) a (∂_{v} f)).toLp 2 volume) =
      -inner ℝ
        ((∂_{v} (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) a φ)).toLp 2 volume)
        (f.toLp 2 volume) := by
  rw [inner_schwartzToLp, inner_schwartzToLp]
  calc
    _ = ∫ x, SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) a φ x * ∂_{v} f x := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change φ x * (a x * ∂_{v} f x) = (a x * φ x) * ∂_{v} f x
      ring
    _ = _ := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) a φ) f v

variable {iota : Type*} [Fintype iota]

def firstOrderSchwartz (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE) :
    𝓢(ModelE, ℝ) →L[ℝ] 𝓢(ModelE, ℝ) :=
  ∑ i, (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) (a i)).comp
    (lineDerivOpCLM ℝ 𝓢(ModelE, ℝ) (v i))

def firstOrderAdjointSchwartz (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE) :
    𝓢(ModelE, ℝ) →L[ℝ] 𝓢(ModelE, ℝ) :=
  -∑ i, (lineDerivOpCLM ℝ 𝓢(ModelE, ℝ) (v i)).comp
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) (a i))

theorem inner_firstOrderSchwartz (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE)
    (φ f : 𝓢(ModelE, ℝ)) :
    inner ℝ (φ.toLp 2 volume) ((firstOrderSchwartz a v f).toLp 2 volume) =
      inner ℝ ((firstOrderAdjointSchwartz a v φ).toLp 2 volume) (f.toLp 2 volume) := by
  change inner ℝ (SchwartzMap.toLpCLM ℝ ℝ 2 volume φ)
      (SchwartzMap.toLpCLM ℝ ℝ 2 volume (firstOrderSchwartz a v f)) =
    inner ℝ (SchwartzMap.toLpCLM ℝ ℝ 2 volume (firstOrderAdjointSchwartz a v φ))
      (SchwartzMap.toLpCLM ℝ ℝ 2 volume f)
  simp only [firstOrderSchwartz, firstOrderAdjointSchwartz,
    sum_apply, neg_apply,
    ContinuousLinearMap.comp_apply, map_sum, map_neg, inner_sum, inner_neg_left,
    sum_inner, SchwartzMap.toLpCLM_apply, LineDeriv.lineDerivOpCLM_apply]
  simp_rw [inner_weightedSchwartzLineDeriv]
  simp only [Finset.sum_neg_distrib]

theorem firstOrderSchwartz_limit_zero (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE)
    (f : ℕ → 𝓢(ModelE, ℝ)) (w : Lp ℝ 2 (volume : Measure ModelE))
    (hf : Tendsto (fun j => (f j).toLp 2 volume) atTop (𝓝 0))
    (hAf : Tendsto (fun j => (firstOrderSchwartz a v (f j)).toLp 2 volume)
      atTop (𝓝 w)) : w = 0 := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure ModelE)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  apply hdense.eq_zero_of_inner_right ℝ
  intro φ
  change inner ℝ (φ.toLp 2 volume) w = 0
  have hleft : Tendsto (fun j => inner ℝ (φ.toLp 2 volume)
      ((firstOrderSchwartz a v (f j)).toLp 2 volume))
      atTop (𝓝 (inner ℝ (φ.toLp 2 volume) w)) :=
    tendsto_const_nhds.inner hAf
  have hright : Tendsto (fun j => inner ℝ ((firstOrderAdjointSchwartz a v φ).toLp 2 volume)
      ((f j).toLp 2 volume))
      atTop (𝓝 (inner ℝ ((firstOrderAdjointSchwartz a v φ).toLp 2 volume)
        (0 : Lp ℝ 2 volume))) :=
    tendsto_const_nhds.inner hf
  have hright' := hright.congr' (Eventually.of_forall (fun j =>
    (inner_firstOrderSchwartz a v φ (f j)).symm))
  simpa only [inner_zero_right] using tendsto_nhds_unique hleft hright'

end PoincareConjecture.EuclideanDerivativeNative
