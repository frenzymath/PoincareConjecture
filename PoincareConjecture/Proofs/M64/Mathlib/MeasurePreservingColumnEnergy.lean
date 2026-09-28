import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory

namespace PoincareConjecture

theorem m64MeasurePreserving_column_energy_le
    {X Y E F ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [Fintype ι]
    {mu : Measure X} {nu : Measure Y} {T : X → Y} {S : Set X} {O : Set Y}
    (hT : MeasurePreserving T mu nu) (hTe : MeasurableEmbedding T)
    (hS : MeasurableSet S) (hSO : MapsTo T S O)
    (V : ι → Y → F) (W : ι → X → E)
    (hV : ∀ i, MemLp (V i) 2 (nu.restrict O))
    (hW : ∀ i, MemLp (W i) 2 (mu.restrict S))
    {L : ℝ}
    (hbound : ∀ i, ∀ x ∈ S, ‖W i x‖ ≤ L * ‖V i (T x)‖) :
    (∫ x in S, ∑ i, ‖W i x‖ ^ 2 ∂mu) ≤
      L ^ 2 * ∫ y in O, ∑ i, ‖V i y‖ ^ 2 ∂nu := by
  have hsub : S ⊆ T ⁻¹' O := hSO
  have hcomp (i : ι) : MemLp (V i ∘ T) 2 (mu.restrict (T ⁻¹' O)) :=
    (hV i).comp_measurePreserving (hT.restrict_preimage_emb hTe O)
  have hsum : IntegrableOn (fun x => ∑ i, ‖V i (T x)‖ ^ 2) (T ⁻¹' O) mu :=
    integrable_finsetSum _ (fun i _ => (hcomp i).norm.integrable_sq)
  have hw : IntegrableOn (fun x => ∑ i, ‖W i x‖ ^ 2) S mu :=
    integrable_finsetSum _ (fun i _ => (hW i).norm.integrable_sq)
  calc
    _ ≤ ∫ x in S, L ^ 2 * ∑ i, ‖V i (T x)‖ ^ 2 ∂mu := by
      apply integral_mono_ae hw ((hsum.mono_set hsub).const_mul _)
      filter_upwards [ae_restrict_mem hS] with x hx
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖W i x‖ ^ 2 ≤ (L * ‖V i (T x)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hbound i x hx) 2
        _ = _ := mul_pow _ _ _
    _ = L ^ 2 * ∫ x in S, ∑ i, ‖V i (T x)‖ ^ 2 ∂mu := integral_const_mul _ _
    _ ≤ L ^ 2 * ∫ x in T ⁻¹' O, ∑ i, ‖V i (T x)‖ ^ 2 ∂mu := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg L)
      exact setIntegral_mono_set hsum
        (Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
        (Eventually.of_forall fun x hx => hsub hx)
    _ = _ := congrArg (fun z : ℝ => L ^ 2 * z)
      (hT.setIntegral_preimage_emb hTe (fun y => ∑ i, ‖V i y‖ ^ 2) O)

end PoincareConjecture
