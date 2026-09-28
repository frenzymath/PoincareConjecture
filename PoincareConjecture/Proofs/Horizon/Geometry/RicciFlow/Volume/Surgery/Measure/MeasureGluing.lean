import PoincareConjecture.Proofs.M10.MeasureGluing
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false

open MeasureTheory Set Filter Function
open scoped Topology ENNReal

namespace PoincareConjecture.SurgeryVolume.Measure

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

theorem measure_le_mul_of_local_comparison {μ ν : Measure X} {U : Set X} {c : ℝ≥0∞}
    (hlocal : ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ A : Set X, MeasurableSet A → A ⊆ V → μ A ≤ c * ν A)
    {A : Set X} (hA : MeasurableSet A) (hAU : A ⊆ U) : μ A ≤ c * ν A := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hU
  · have hAe : A = ∅ := subset_empty_iff.mp hAU
    simp only [hAe, measure_empty, mul_zero, le_refl]
  let : Nonempty U := hU.to_subtype
  choose V hVo hxV hV using fun x : U ↦ hlocal x x.2
  obtain ⟨e, he⟩ := (HereditarilyLindelofSpace.isLindelof U).indexed_countable_subcover
    V hVo (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let W : ℕ → Set X := fun k ↦ V (e k)
  let D : ℕ → Set X := fun k ↦ A ∩ disjointed W k
  have hDm : ∀ k, MeasurableSet (D k) := fun k ↦
    hA.inter (MeasurableSet.disjointed (fun j ↦ (hVo (e j)).measurableSet) k)
  have hDd : Pairwise (Disjoint on D) :=
    (disjoint_disjointed W).mono fun _ _ h ↦ h.mono inter_subset_right inter_subset_right
  have hcover : ⋃ k, D k = A := by
    dsimp only [D]
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left.mpr (hAU.trans he)]
  calc
    μ A = ∑' k, μ (D k) := by rw [← hcover, measure_iUnion hDd hDm]
    _ ≤ ∑' k, c * ν (D k) := ENNReal.tsum_le_tsum fun k ↦
      hV (e k) (D k) (hDm k) (inter_subset_right.trans (disjointed_subset W k))
    _ = c * ν A := by rw [ENNReal.tsum_mul_left, ← measure_iUnion hDd hDm, hcover]

theorem measure_eq_of_local_comparisons {μ ν : Measure X} {U : Set X}
    (c : ℕ → ℝ≥0∞) (hc : Tendsto c atTop (𝓝 1))
    (hforward : ∀ k, ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ A : Set X, MeasurableSet A → A ⊆ V → μ A ≤ c k * ν A)
    (hreverse : ∀ k, ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ A : Set X, MeasurableSet A → A ⊆ V → ν A ≤ c k * μ A)
    {A : Set X} (hA : MeasurableSet A) (hAU : A ⊆ U) : μ A = ν A := by
  have hlim (a : ℝ≥0∞) : Tendsto (fun k ↦ c k * a) atTop (𝓝 a) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hc (b := a) (Or.inl one_ne_zero)
  apply le_antisymm
  · exact ge_of_tendsto' (hlim (ν A)) fun k ↦
      measure_le_mul_of_local_comparison (hforward k) hA hAU
  · exact ge_of_tendsto' (hlim (μ A)) fun k ↦
      measure_le_mul_of_local_comparison (hreverse k) hA hAU

theorem restrict_eq_of_local_comparisons {μ ν : Measure X} {U : Set X}
    (hU : MeasurableSet U) (c : ℕ → ℝ≥0∞) (hc : Tendsto c atTop (𝓝 1))
    (hforward : ∀ k, ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ A : Set X, MeasurableSet A → A ⊆ V → μ A ≤ c k * ν A)
    (hreverse : ∀ k, ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ A : Set X, MeasurableSet A → A ⊆ V → ν A ≤ c k * μ A) :
    μ.restrict U = ν.restrict U := by
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact measure_eq_of_local_comparisons c hc hforward hreverse (hA.inter hU) inter_subset_right

end PoincareConjecture.SurgeryVolume.Measure
