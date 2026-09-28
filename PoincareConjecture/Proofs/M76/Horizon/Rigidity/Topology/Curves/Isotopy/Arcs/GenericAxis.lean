import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.Contacts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteCircleRegularValues









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

private theorem real_affine_formula (A : ℝ →ᴬ[ℝ] ℝ) (x : ℝ) :
    A x = x * (A 1 - A 0) + A 0 := by
  have h := A.toAffineMap.apply_lineMap (0 : ℝ) 1 x
  simpa [AffineMap.lineMap_apply_ring'] using h

theorem exists_generic_annular_axis_partition {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) :
    ∃ (c : ℝ) (n : ℕ) (t : Fin (n + 4) → ℝ),
      c ∈ Ioo (0 : ℝ) 32 ∧ StrictMono t ∧ t 0 = 0 ∧
      t (Fin.last (n + 3)) = 1 ∧
      (∀ i : Fin (n + 3), ∃ A : ℝ →ᴬ[ℝ] ℝ,
        EqOn f A (Icc (t i.castSucc) (t i.succ))) ∧
      ∀ (i : Fin (n + 4)) (k : ℤ), f (t i) ≠ c + 32 * (k : ℝ) := by
  obtain ⟨n, t, ht, ht0, ht1, hA⟩ := hf.exists_interval_partition_four
  let : Fact ((0 : ℝ) < 32) := ⟨by norm_num⟩
  obtain ⟨c, hc, hcZ⟩ := AddCircle.exists_representative_in_interval_avoiding_finite
    (32 : ℝ) (finite_range (fun i => (f (t i) : AddCircle (32 : ℝ))))
    (a := 0) (b := 32) le_rfl (by norm_num) le_rfl
  refine ⟨c, n, t, hc, ht, ht0, ht1, hA, ?_⟩
  intro i k heq
  apply hcZ
  refine ⟨i, ?_⟩
  change (f (t i) : AddCircle (32 : ℝ)) = (c : AddCircle (32 : ℝ))
  rw [heq, AddCircle.coe_add]
  have hz : ((32 * (k : ℝ) : ℝ) : AddCircle (32 : ℝ)) = 0 := by
    rw [mul_comm, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero]
  rw [hz, add_zero]

theorem affine_partition_regular_contact {f : ℝ → ℝ} {n : ℕ}
    {t : Fin (n + 4) → ℝ} (ht : StrictMono t) (ht0 : t 0 = 0)
    (ht1 : t (Fin.last (n + 3)) = 1)
    (hA : ∀ i : Fin (n + 3), ∃ A : ℝ →ᴬ[ℝ] ℝ,
      EqOn f A (Icc (t i.castSucc) (t i.succ)))
    {c x : ℝ} (hc : ∀ i, f (t i) ≠ c) (hx : x ∈ Icc (0 : ℝ) 1)
    (hfx : f x = c) :
    ∃ (i : Fin (n + 3)) (m : ℝ), x ∈ Ioo (t i.castSucc) (t i.succ) ∧
      m ≠ 0 ∧ ∀ y ∈ Icc (t i.castSucc) (t i.succ),
        f y - c = m * (y - x) := by
  have hx' : x ∈ Icc (t 0) (t (Fin.last (n + 3))) := by simpa [ht0, ht1] using hx
  obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc hx'
  obtain ⟨A, hAf⟩ := hA i
  have hleft : t i.castSucc < x := lt_of_le_of_ne hi.1 (fun heq => hc _ (heq ▸ hfx))
  have hright : x < t i.succ := lt_of_le_of_ne hi.2 (fun heq => hc _ (heq ▸ hfx))
  have hm : A 1 - A 0 ≠ 0 := by
    intro hz
    apply hc i.castSucc
    rw [hAf ⟨le_rfl, (ht Fin.castSucc_lt_succ).le⟩, real_affine_formula, hz,
      mul_zero, zero_add]
    have hh := (hAf hi).symm.trans hfx
    rw [real_affine_formula, hz, mul_zero, zero_add] at hh
    exact hh
  refine ⟨i, A 1 - A 0, ⟨hleft, hright⟩, hm, ?_⟩
  intro y hy
  have hh := (hAf hi).symm.trans hfx
  rw [real_affine_formula] at hh
  rw [hAf hy, real_affine_formula]
  nlinarith

theorem affine_partition_regular_level_finite {f : ℝ → ℝ} {n : ℕ}
    {t : Fin (n + 4) → ℝ} (ht : StrictMono t) (ht0 : t 0 = 0)
    (ht1 : t (Fin.last (n + 3)) = 1)
    (hA : ∀ i : Fin (n + 3), ∃ A : ℝ →ᴬ[ℝ] ℝ,
      EqOn f A (Icc (t i.castSucc) (t i.succ)))
    {c : ℝ} (hc : ∀ i, f (t i) ≠ c) :
    {x ∈ Icc (0 : ℝ) 1 | f x = c}.Finite := by
  classical
  choose A hAf using hA
  apply (finite_range fun i => (c - A i 0) / (A i 1 - A i 0)).subset
  rintro x ⟨hx, hfx⟩
  have hx' : x ∈ Icc (t 0) (t (Fin.last (n + 3))) := by simpa [ht0, ht1] using hx
  obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc hx'
  have hh := (hAf i hi).symm.trans hfx
  rw [real_affine_formula] at hh
  have hm : A i 1 - A i 0 ≠ 0 := by
    intro hz
    apply hc i.castSucc
    rw [hAf i ⟨le_rfl, (ht Fin.castSucc_lt_succ).le⟩, real_affine_formula, hz,
      mul_zero, zero_add]
    simpa [hz] using hh
  exact ⟨i, (div_eq_iff hm).mpr (by nlinarith)⟩

theorem exists_generic_annular_axis {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) :
    ∃ c ∈ Ioo (0 : ℝ) 32,
      {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, f x = c + 32 * (k : ℝ)}.Finite ∧
      ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → f x = c + 32 * (k : ℝ) →
        ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
          ∀ y ∈ Icc a b, f y - (c + 32 * (k : ℝ)) = m * (y - x) := by
  obtain ⟨c, n, t, hc, ht, ht0, ht1, hA, havoid⟩ :=
    exists_generic_annular_axis_partition hf
  have hconst (z : ℝ) : FinitePiecewiseAffineOn (fun _ : ℝ => z) (Icc 0 1) :=
    hf.postcomp (ContinuousAffineMap.const ℝ ℝ z)
  have hr : FinitePiecewiseAffineOn (fun x => (f x - c, (0 : ℝ))) (Icc 0 1) :=
    (hf.sub (hconst c)).prod_mk (hconst 0)
  have hK := finite_annular_axes_met hr
  have hlevel (k : ℤ) := affine_partition_regular_level_finite ht ht0 ht1 hA
    (fun i => havoid i k)
  refine ⟨c, hc, ?_, ?_⟩
  · apply (hK.biUnion (fun k _ => hlevel k)).subset
    rintro x ⟨hx, k, hk⟩
    exact mem_iUnion₂.mpr ⟨k, ⟨x, hx, by dsimp; linarith⟩, hx, hk⟩
  · intro x k hx hk
    obtain ⟨i, m, hi, hm, hformula⟩ :=
      affine_partition_regular_contact ht ht0 ht1 hA (fun i => havoid i k) hx hk
    refine ⟨t i.castSucc, t i.succ, m, ?_, hi.1, hi.2, ?_, hm, hformula⟩
    · rw [← ht0]
      exact ht.monotone (Fin.zero_le _)
    · rw [← ht1]
      exact ht.monotone (Fin.le_last _)

end PoincareConjecture.M76.Dehn
