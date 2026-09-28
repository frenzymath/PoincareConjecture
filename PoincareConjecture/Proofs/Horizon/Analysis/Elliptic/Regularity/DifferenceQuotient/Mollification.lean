import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution










noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace Poincare.Analysis.Sobolev.DifferenceQuotient

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def mollifyEps {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) : E → ℝ :=
  Poincare.Analysis.Sobolev.mollifierEps (d := d) hε ⋆[
    ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u

omit [NeZero d] in
theorem mollifyEps_contDiff {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_loc : LocallyIntegrable u (volume : Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyEps (d := d) hε u) := by
  unfold mollifyEps
  exact HasCompactSupport.contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (Poincare.Analysis.Sobolev.mollifierEps_compactSupport hε)
    (Poincare.Analysis.Sobolev.mollifierEps_smooth hε)
    hu_loc

omit [NeZero d] in
theorem mollifyEps_continuous {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_loc : LocallyIntegrable u (volume : Measure E)) :
    Continuous (mollifyEps (d := d) hε u) :=
  (mollifyEps_contDiff (d := d) hε hu_loc).continuous

omit [NeZero d] in
lemma mollifyEps_apply {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) (x : E) :
    mollifyEps (d := d) hε u x =
      ∫ t,
        Poincare.Analysis.Sobolev.mollifierEps (d := d) hε t * u (x - t)
        ∂(volume : Measure E) := by
  simp [mollifyEps, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

omit [NeZero d] in
theorem mollifyEps_hasCompactSupport {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_supp : HasCompactSupport u) :
    HasCompactSupport (mollifyEps (d := d) hε u) :=
  HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure E))
    (Poincare.Analysis.Sobolev.mollifierEps_compactSupport hε)
    hu_supp

omit [NeZero d] in
theorem mollifyEps_memLp_two_of_hasCompactSupport {ε : ℝ} (hε : 0 < ε)
    {u : E → ℝ} (hu_l2 : MemLp u 2 (volume : Measure E))
    (hu_supp : HasCompactSupport u) :
    MemLp (mollifyEps (d := d) hε u) 2 (volume : Measure E) := by
  have hu_loc : LocallyIntegrable u (volume : Measure E) :=
    hu_l2.locallyIntegrable (by norm_num)
  have h_cont : Continuous (mollifyEps (d := d) hε u) :=
    mollifyEps_continuous (d := d) hε hu_loc
  have h_supp : HasCompactSupport (mollifyEps (d := d) hε u) :=
    mollifyEps_hasCompactSupport (d := d) hε hu_supp
  exact h_cont.memLp_of_hasCompactSupport h_supp

omit [NeZero d] in
theorem tendsto_mollifyEps_of_continuous {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hε_tendsto : Tendsto ε l (𝓝 0))
    {u : E → ℝ} (hu : Continuous u) (x₀ : E) :
    Tendsto (fun i => mollifyEps (d := d) (hε i) u x₀) l (𝓝 (u x₀)) := by
  have h_bump_rOut : ∀ i,
      (Poincare.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i := by
    intro i
    show (Poincare.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i
    rfl
  have h_rOut_tendsto :
      Tendsto
        (fun i => (Poincare.Analysis.Sobolev.mollifierBumpEps
            (d := d) (hε i)).rOut)
        l (𝓝 0) := by
    have h_funeq : (fun i => (Poincare.Analysis.Sobolev.mollifierBumpEps
        (d := d) (hε i)).rOut) = ε := by
      funext i; exact h_bump_rOut i
    rw [h_funeq]
    exact hε_tendsto
  have h_conv_tendsto :
      Tendsto
        (fun i =>
          ((Poincare.Analysis.Sobolev.mollifierBumpEps (d := d)
              (hε i)).normed (volume : Measure E) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀)
        l (𝓝 (u x₀)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure E))
      h_rOut_tendsto hu x₀
  have h_fn_eq : ∀ i,
      ((Poincare.Analysis.Sobolev.mollifierBumpEps (d := d)
            (hε i)).normed (volume : Measure E) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀ := by
    intro i
    show ((Poincare.Analysis.Sobolev.mollifierBumpEps (d := d)
            (hε i)).normed (volume : Measure E) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀
    rfl
  refine h_conv_tendsto.congr ?_
  intro i; exact h_fn_eq i

omit [NeZero d] in
theorem ae_tendsto_mollifyEps_of_locallyIntegrable {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hε_tendsto : Tendsto ε l (𝓝 0))
    {u : E → ℝ} (hu_loc : LocallyIntegrable u (volume : Measure E)) :
    ∀ᵐ x₀ ∂(volume : Measure E),
      Tendsto (fun i => mollifyEps (d := d) (hε i) u x₀) l (𝓝 (u x₀)) := by
  have h_bump_rOut : ∀ i,
      (Poincare.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i := by
    intro i
    show (Poincare.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i
    rfl
  have h_bump_rIn : ∀ i,
      (Poincare.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rIn
        = ε i / 2 := by
    intro i
    show (Poincare.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rIn
        = ε i / 2
    rfl
  have h_rOut_tendsto :
      Tendsto
        (fun i =>
          (Poincare.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut)
        l (𝓝 0) := by
    have h_funeq : (fun i => (Poincare.Analysis.Sobolev.mollifierBumpEps
        (d := d) (hε i)).rOut) = ε := by
      funext i; exact h_bump_rOut i
    rw [h_funeq]
    exact hε_tendsto
  have h_ratio :
      ∀ᶠ i in l,
        (Poincare.Analysis.Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
          ≤ 2 *
            (Poincare.Analysis.Sobolev.mollifierBumpEps (d := d)
              (hε i)).rIn := by
    refine Filter.Eventually.of_forall fun i => ?_
    rw [h_bump_rOut, h_bump_rIn]
    have : ε i = 2 * (ε i / 2) := by ring
    linarith
  have h_ae :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (volume : Measure E)) h_rOut_tendsto h_ratio hu_loc
  filter_upwards [h_ae] with x₀ hx₀
  have h_eq : ∀ i,
      ((Poincare.Analysis.Sobolev.mollifierBumpEps (d := d)
          (hε i)).normed (volume : Measure E) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀ := by
    intro i
    show ((Poincare.Analysis.Sobolev.mollifierBumpEps (d := d)
          (hε i)).normed (volume : Measure E) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀
    rfl
  refine hx₀.congr ?_
  intro i; exact h_eq i

end Poincare.Analysis.Sobolev.DifferenceQuotient
