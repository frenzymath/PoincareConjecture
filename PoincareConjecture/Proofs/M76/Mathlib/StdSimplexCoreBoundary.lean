import PoincareConjecture.Proofs.M76.Mathlib.StdSimplexCore
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicFaceSaturation

set_option autoImplicit false

open Set

variable {ι : Type*} [Fintype ι]

theorem sum_eq_one_of_mem_affineSpan_stdSimplexCore {η : ℝ} {q : ι → ℝ}
    (hq : q ∈ affineSpan ℝ (stdSimplexCore ι η)) : ∑ i, q i = 1 := by
  refine affineSpan_induction hq (fun r hr => hr.2) (fun c u v w hu hv hw => ?_)
  simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    hu, hv, hw, sub_self, mul_zero, zero_add]

variable [Nonempty ι]

theorem mem_intrinsicInterior_stdSimplexCore_iff {η : ℝ}
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ} :
    q ∈ intrinsicInterior ℝ (stdSimplexCore ι η) ↔
      (∑ i, q i = 1) ∧ ∀ i, η < q i := by
  constructor
  · intro hq
    have hqc := intrinsicInterior_subset hq
    refine ⟨hqc.2, fun i => ?_⟩
    have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    let p : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹
    have hpstrict : ∀ j, η < p j := by
      intro j
      change η < (Fintype.card ι : ℝ)⁻¹
      rw [inv_eq_one_div, lt_div_iff₀ hn]
      nlinarith [hbound]
    have hp : p ∈ stdSimplexCore ι η := ⟨fun j => (hpstrict j).le, by simp [p]⟩
    by_contra hnot
    have he : q i = η := le_antisymm (not_lt.mp hnot) (hqc.1 i)
    have hdir : q - p ∈ (affineSpan ℝ (stdSimplexCore ι η)).direction :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan _ _ hqc) (subset_affineSpan _ _ hp)
    obtain ⟨r, hr, hmem⟩ := Set.exists_pos_smul_add_mem_of_intrinsicInterior hq hdir
    have hlow := hmem.1 i
    change η ≤ r * (q i - p i) + q i at hlow
    rw [he] at hlow
    nlinarith [hpstrict i]
  · rintro ⟨hsum, hstrict⟩
    have hqc : q ∈ stdSimplexCore ι η := ⟨fun i => (hstrict i).le, hsum⟩
    let A := affineSpan ℝ (stdSimplexCore ι η)
    let qA : A := ⟨q, subset_affineSpan _ _ hqc⟩
    have hcont (i : ι) : Continuous (fun r : A => (r : ι → ℝ) i) :=
      (continuous_apply i).comp continuous_subtype_val
    have ho : IsOpen {r : A | ∀ i, η < (r : ι → ℝ) i} := by
      convert isOpen_iInter_of_finite (fun i : ι =>
        isOpen_lt (show Continuous (fun _ : A => η) from continuous_const) (hcont i)) using 1
      ext r
      simp
    refine mem_intrinsicInterior.mpr ⟨qA, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
    have hmem : qA ∈ {r : A | ∀ i, η < (r : ι → ℝ) i} := hstrict
    apply Filter.mem_of_superset (ho.mem_nhds hmem)
    intro r hr
    exact ⟨fun i => (hr i).le, sum_eq_one_of_mem_affineSpan_stdSimplexCore r.property⟩

theorem mem_intrinsicFrontier_stdSimplexCore_iff {η : ℝ}
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ} :
    q ∈ intrinsicFrontier ℝ (stdSimplexCore ι η) ↔
      q ∈ stdSimplexCore ι η ∧ ∃ i, q i = η := by
  rw [← closure_sdiff_intrinsicInterior (𝕜 := ℝ) (stdSimplexCore ι η),
    (isClosed_stdSimplexCore ι η).closure_eq]
  change (q ∈ stdSimplexCore ι η ∧ q ∉ intrinsicInterior ℝ (stdSimplexCore ι η)) ↔ _
  constructor
  · rintro ⟨hq, hn⟩
    have hnot : ¬∀ i, η < q i := fun hi =>
      hn ((mem_intrinsicInterior_stdSimplexCore_iff hbound).mpr ⟨hq.2, hi⟩)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact ⟨hq, i, le_antisymm (not_lt.mp hi) (hq.1 i)⟩
  · rintro ⟨hq, i, hi⟩
    refine ⟨hq, fun hn => ?_⟩
    have h := ((mem_intrinsicInterior_stdSimplexCore_iff hbound).mp hn).2 i
    simp only [hi, lt_self_iff_false] at h
