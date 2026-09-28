import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarAreaOverlap














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Cover" => ℝ × ℝ





theorem scalar_area_ge_one_of_integer_cover {E : Set Cover} (hE : MeasurableSet E)
    (hcover : ∀ᵐ z : Cover ∂volume,
      z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 → ∃ n : ℤ, z + (0, (n : ℝ)) ∈ E) :
    1 ≤ volume E := by
  let Q : Set Cover := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
  let B : ℤ → Set Cover := fun n => Q ∩ (fun z : Cover => z + (0, (n : ℝ))) ⁻¹' E
  let C : ℤ → Set Cover := fun n => E ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (n : ℝ) ((n : ℝ) + 1))
  have hQ : volume Q = 1 := by
    simp [Q, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
  have hcover_le : volume Q ≤ volume (⋃ n : ℤ, B n) := by
    apply measure_mono_ae
    filter_upwards [hcover] with z hz hzQ
    obtain ⟨n, hn⟩ := hz hzQ
    exact mem_iUnion.mpr ⟨n, hzQ, hn⟩
  have hBC (n : ℤ) : volume (B n) = volume (C n) := by
    have heq : (fun z : Cover => z + (0, (n : ℝ))) ⁻¹' C n = B n := by
      ext z
      constructor
      · rintro ⟨hzE, hz1, hz2⟩
        refine ⟨⟨?_, ?_⟩, hzE⟩
        · simpa only [Prod.fst_add, add_zero] using hz1
        · change (n : ℝ) < z.2 + n ∧ z.2 + n < (n : ℝ) + 1 at hz2
          constructor <;> linarith
      · rintro ⟨⟨hz1, hz2⟩, hzE⟩
        refine ⟨hzE, ?_, ?_⟩
        · simpa only [Prod.fst_add, add_zero] using hz1
        · change (n : ℝ) < z.2 + n ∧ z.2 + n < (n : ℝ) + 1
          constructor <;> linarith [hz2.1, hz2.2]
    rw [← heq]
    exact measure_preimage_add_right volume (0, (n : ℝ)) (C n)
  have hCm (n : ℤ) : MeasurableSet (C n) :=
    hE.inter (measurableSet_Ioo.prod measurableSet_Ioo)
  have hdisjoint : Pairwise (fun m n : ℤ => Disjoint (C m) (C n)) := by
    intro m n hmn
    apply disjoint_left.mpr
    intro z hzm hzn
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · have hstep : (m : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast Int.add_one_le_iff.mpr hlt
      linarith [hzm.2.2.2, hzn.2.2.1]
    · have hstep : (n : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast Int.add_one_le_iff.mpr hlt
      linarith [hzn.2.2.2, hzm.2.2.1]
  calc
    1 = volume Q := hQ.symm
    _ ≤ volume (⋃ n : ℤ, B n) := hcover_le
    _ ≤ ∑' n : ℤ, volume (B n) := measure_iUnion_le _
    _ = ∑' n : ℤ, volume (C n) := tsum_congr hBC
    _ = volume (⋃ n : ℤ, C n) := (measure_iUnion hdisjoint hCm).symm
    _ ≤ volume E := measure_mono (iUnion_subset fun _ => inter_subset_left)

end PoincareConjecture.M64Uniformization
