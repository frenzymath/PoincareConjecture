import Mathlib.MeasureTheory.Integral.Bochner.Set
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Selection

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped BigOperators

namespace Poincare.CurvatureIntegral

theorem integral_le_sum_of_finset_cover
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {U : Set X} (hU : MeasurableSet U) (S : Finset ι) (B : ι → Set X)
    (hB : ∀ q ∈ S, MeasurableSet (B q))
    {h : X → ℝ} (hhn : ∀ x, 0 ≤ h x)
    (hUi : IntegrableOn h U μ) (hBi : ∀ q ∈ S, IntegrableOn h (B q) μ)
    (hcover : U ⊆ ⋃ q ∈ S, B q) :
    (∫ x in U, h x ∂μ) ≤ ∑ q ∈ S, ∫ x in B q, h x ∂μ := by
  classical
  have hind (q) (hq : q ∈ S) : Integrable ((B q).indicator h) μ :=
    (integrable_indicator_iff (hB q hq)).mpr (hBi q hq)
  have hpoint (x : X) : U.indicator h x ≤ ∑ q ∈ S, (B q).indicator h x := by
    by_cases hx : x ∈ U
    · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hcover hx)
      rw [indicator_of_mem hx]
      calc
        h x = (B q).indicator h x := (indicator_of_mem hxq h).symm
        _ ≤ _ := Finset.single_le_sum
          (fun y _ => indicator_nonneg (fun z _ => hhn z) x) hq
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg fun q _ => indicator_nonneg (fun z _ => hhn z) x
  have h := integral_mono ((integrable_indicator_iff hU).mpr hUi)
    (integrable_finsetSum S hind) hpoint
  rw [integral_indicator hU, integral_finsetSum S hind] at h
  refine h.trans_eq (Finset.sum_congr rfl ?_)
  intro q hq
  exact integral_indicator (hB q hq)

theorem integral_le_complement_add_sum
    {X ι : Type*} [MeasurableSpace X] [Fintype ι] {μ : Measure X}
    {U : Set X} (hU : MeasurableSet U) (V : ι → Set X)
    (hV : ∀ i, MeasurableSet (V i)) {h : X → ℝ} (hhn : ∀ x, 0 ≤ h x)
    (hUi : IntegrableOn h U μ) (hVi : ∀ i, IntegrableOn h (V i) μ) :
    (∫ x in U, h x ∂μ) ≤ (∫ x in U \ ⋃ i, V i, h x ∂μ) +
      ∑ i, ∫ x in V i, h x ∂μ := by
  classical
  let B : Option ι → Set X := Option.elim' (U \ ⋃ i, V i) V
  have hB (i : Option ι) : MeasurableSet (B i) := by
    cases i with
    | none => exact hU.diff (MeasurableSet.iUnion hV)
    | some i => exact hV i
  have hiB (i : Option ι) : IntegrableOn h (B i) μ := by
    cases i with
    | none => exact hUi.mono_set sdiff_subset
    | some i => exact hVi i
  have hcover : U ⊆ ⋃ i ∈ (Finset.univ : Finset (Option ι)), B i := by
    intro x hx
    by_cases hv : x ∈ ⋃ i, V i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hv
      exact mem_iUnion₂.mpr ⟨some i, Finset.mem_univ _, hi⟩
    · exact mem_iUnion₂.mpr ⟨none, Finset.mem_univ _, hx, hv⟩
  simpa [B, Fintype.sum_option, add_comm] using integral_le_sum_of_finset_cover
    hU Finset.univ B (fun i _ => hB i) hhn hUi (fun i _ => hiB i) hcover

theorem exists_subseq_fixed_member_integral_tendsto_atTop
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)] {ι : Type*} [Fintype ι]
    (μ : ∀ j, Measure (X j)) (U : ∀ j, Set (X j)) (V : ∀ j, ι → Set (X j))
    (h : ∀ j, X j → ℝ) (hU : ∀ j, MeasurableSet (U j))
    (hV : ∀ j i, MeasurableSet (V j i)) (hhn : ∀ j x, 0 ≤ h j x)
    (hUi : ∀ j, IntegrableOn (h j) (U j) (μ j))
    (hVi : ∀ j i, IntegrableOn (h j) (V j i) (μ j))
    (C : ℝ) (houtside : ∀ j, (∫ x in U j \ ⋃ i, V j i, h j x ∂μ j) ≤ C)
    (hlarge : ∀ B : ℝ, ∃ j, B < ∫ x in U j, h j x ∂μ j) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun j => ∫ x in V (phi j) i, h (phi j) x ∂μ (phi j)) atTop atTop := by
  classical
  have hlargei : ∃ i : ι, ∀ B : ℝ, ∃ j, B < ∫ x in V j i, h j x ∂μ j := by
    by_contra hb
    push Not at hb
    choose b hb using hb
    obtain ⟨j, hj⟩ := hlarge (C + ∑ i, b i)
    have hcover := integral_le_complement_add_sum (hU j) (V j) (hV j)
      (hhn j) (hUi j) (hVi j)
    exact (not_le_of_gt hj) (hcover.trans (add_le_add (houtside j)
      (Finset.sum_le_sum (fun i _ => hb i j))))
  obtain ⟨i, hi⟩ := hlargei
  obtain ⟨phi, hphi, hvalue⟩ := exists_strictMono_above_thresholds
    (fun j => ∫ x in V j i, h j x ∂μ j) (fun j => (j : ℝ)) hi
  exact ⟨i, phi, hphi, tendsto_atTop_mono (fun j => (hvalue j).le)
    tendsto_natCast_atTop_atTop⟩

end Poincare.CurvatureIntegral
