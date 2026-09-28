import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Approximation.Closure
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Approximation
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Density
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.TestFunction.Weak













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergDiffQuotTestFunction

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)





theorem m64MemW01p_of_halfspace_support
    {u : E → ℝ} (w : MemW1pWitness 2 u univ)
    (hc : HasCompactSupport u) (k : Fin d)
    (hzero : ∀ x : E, x k < 0 → u x = 0) :
    MemW01p 2 u {x : E | 0 < x k} := by
  let H : Set E := {x | 0 < x k}
  have hH : IsOpen H := isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) k).continuous
  have hs : tsupport u ⊆ {x : E | 0 ≤ x k} := by
    apply closure_minimal ?_
      (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) k).continuous)
    intro x hx
    exact le_of_not_gt fun hneg => hx (hzero x hneg)
  have hu : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using w.memLp
  have hg (i : Fin d) : MemLp (fun x => w.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using w.weakGrad_component_memLp i
  let delta := fun j : ℕ => 1 / ((j : ℝ) + 1)
  let v := fun j : ℕ => delta j • EuclideanSpace.single k (1 : ℝ)
  let f := fun j : ℕ => fun x : E => u (x - v j)
  have hd (j : ℕ) : 0 < delta j := by dsimp [delta]; positivity
  have hv : Tendsto v atTop (𝓝 (0 : E)) := by
    have hdelta : Tendsto delta atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [zero_smul] using hdelta.smul_const (EuclideanSpace.single k (1 : ℝ))
  have hshift (j : ℕ) : MeasurePreserving (fun x : E => x - v j) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure E) (-v j)
  have hweak (j : ℕ) (i : Fin d) :
      HasWeakPartialDeriv i (fun x => w.weakGrad (x - v j) i) (f j) univ := by
    have h := hasWeakPartialDeriv_translate k i (delta j) (w.isWeakGrad i)
    change HasWeakPartialDeriv i
      (fun x => w.weakGrad (x + (-delta j) • EuclideanSpace.single k 1) i)
      (fun x => u (x + (-delta j) • EuclideanSpace.single k 1)) univ at h
    simpa only [v, f, neg_smul, ← sub_eq_add_neg] using h
  let ws := fun j : ℕ => ({
    memLp := (hu.comp_measurePreserving (hshift j)).restrict H
    weakGrad := fun x => w.weakGrad (x - v j)
    weakGrad_component_memLp := fun i => ((hg i).comp_measurePreserving (hshift j)).restrict H
    isWeakGrad := fun i => (hweak j i).restrict hH (subset_univ H)
  } : MemW1pWitness 2 (f j) H)
  let wr : MemW1pWitness 2 u H := {
    memLp := hu.restrict H
    weakGrad := w.weakGrad
    weakGrad_component_memLp := fun i => (hg i).restrict H
    isWeakGrad := fun i => (w.isWeakGrad i).restrict hH (subset_univ H) }
  have hseq (j : ℕ) : MemW01p 2 (f j) H := by
    let tau : E ≃ₜ E := Homeomorph.addRight (-v j)
    have hcompact : HasCompactSupport (f j) := by
      have h := hc.comp_homeomorph tau
      change HasCompactSupport (fun x => u (x + (-v j))) at h
      simpa only [f, sub_eq_add_neg] using h
    have hsupport : tsupport (f j) ⊆ H := by
      intro x hx
      have hx' : x - v j ∈ tsupport u := by
        exact tsupport_comp_subset_preimage u (continuous_id.sub continuous_const) hx
      have hnonneg := hs hx'
      have hcoord : (x - v j) k = x k - delta j := by
        simp [v]
      change 0 ≤ (x - v j) k at hnonneg
      rw [hcoord] at hnonneg
      change 0 < x k
      linarith [hd j]
    simpa using memW01p_of_memW1p_of_tsupport_subset hH (by norm_num : (1 : ℝ) < 2)
      (by simpa using (ws j).memW1p) hcompact hsupport
  apply MemW01p.of_tendsto_eLpNorm hH hseq ws wr
  · have ht := (tendsto_eLpNorm_translate_sub_of_memLp
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hu).comp hv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le)
    intro j
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  · intro i
    have ht := (tendsto_eLpNorm_translate_sub_of_memLp
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hg i)).comp hv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le)
    intro j
    exact eLpNorm_mono_measure _ Measure.restrict_le_self

end PoincareConjecture
