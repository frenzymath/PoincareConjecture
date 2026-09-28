import PoincareConjecture.Proofs.M10.EquicontinuousCompactRange
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.M10

variable {X ι : Type*} [MetricSpace X]


theorem equicontinuous_clipped_curves {γ : ι → ℝ → X} {S : ι → ℝ} {B K : ℝ}
    (hS : ∀ i, 0 ≤ S i) (hK : 0 ≤ K)
    (hmod : ∀ i a b, 0 ≤ a → a ≤ b → b ≤ S i →
      dist (γ i a) (γ i b) ≤ Real.sqrt (K * (b - a))) :
    Equicontinuous (fun i (t : Icc (0 : ℝ) B) ↦ γ i (min (t : ℝ) (S i))) := by
  have hlim : Tendsto (fun r : ℝ ↦ Real.sqrt (K * r)) (𝓝 0) (𝓝 0) := by
    have ht : Tendsto (fun r : ℝ ↦ K * r) (𝓝 0) (𝓝 (K * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simpa only [mul_zero, Real.sqrt_zero] using ht.sqrt
  apply Metric.equicontinuous_of_continuity_modulus _ hlim
  intro s t i
  have hordered (a b : Icc (0 : ℝ) B) (hab : (a : ℝ) ≤ b) :
      dist (γ i (min (a : ℝ) (S i))) (γ i (min (b : ℝ) (S i))) ≤
        Real.sqrt (K * dist a b) := by
    have hab' : min (a : ℝ) (S i) ≤ min (b : ℝ) (S i) := min_le_min_right _ hab
    apply (hmod i _ _ (le_min a.property.1 (hS i)) hab' (min_le_right _ _)).trans
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ hK
    have hclip := (LipschitzWith.id.min_const (S i)).dist_le_mul (a : ℝ) (b : ℝ)
    simpa only [id_eq, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab),
      abs_of_nonpos (sub_nonpos.mpr hab'), NNReal.coe_one, one_mul, neg_sub] using hclip
  rcases le_total (s : ℝ) (t : ℝ) with hst | hts
  · exact hordered s t hst
  · simpa only [dist_comm] using hordered t s hts


theorem exists_compact_clipped_range [CompleteSpace X] [LocallyCompactSpace X]
    {γ : ι → ℝ → X} {S : ι → ℝ} {B K : ℝ} (hB : 0 ≤ B)
    (hS : ∀ i, 0 ≤ S i) (hSB : ∀ i, S i ≤ B) (hK : 0 ≤ K)
    (hmod : ∀ i a b, 0 ≤ a → a ≤ b → b ≤ S i →
      dist (γ i a) (γ i b) ≤ Real.sqrt (K * (b - a)))
    (p : X) (hanchor : ∀ i, γ i 0 = p) :
    ∃ C : Set X, IsCompact C ∧ ∀ i, γ i (S i) ∈ C := by
  let : PreconnectedSpace (Icc (0 : ℝ) B) := Subtype.preconnectedSpace isPreconnected_Icc
  have hf := equicontinuous_clipped_curves (B := B) hS hK hmod
  obtain ⟨C, hC, hrange⟩ := exists_compact_range_of_anchored_equicontinuous
    hf (⟨0, le_rfl, hB⟩ : Icc (0 : ℝ) B) p (by
      intro i
      simpa only [min_eq_left (hS i)] using hanchor i)
  refine ⟨C, hC, fun i ↦ ?_⟩
  simpa only [min_self] using hrange i ⟨S i, hS i, hSB i⟩

end PoincareConjecture.M10
