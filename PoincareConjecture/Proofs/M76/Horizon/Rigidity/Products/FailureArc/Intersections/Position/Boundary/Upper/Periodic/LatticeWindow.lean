import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.PeriodicSquare

private theorem coe_eq_iff_integer_translate {p x y : ℝ} :
    (x : AddCircle p) = (y : AddCircle p) ↔
      ∃ n : ℤ, x = y + (n : ℝ) * p := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul] at hn
    linarith
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul]
    linarith

theorem exists_finite_lattice_window
    {p : ℝ} (hp : 0 < p) {S W : Set (ℝ × ℝ)}
    (hS : IsCompact S) (hW : IsCompact W) :
    ∃ J : Finset (ℤ × ℤ), ∀ z ∈ W,
      ((z.1 : AddCircle p), (z.2 : AddCircle p)) ∈
        (fun x : ℝ × ℝ => ((x.1 : AddCircle p), (x.2 : AddCircle p))) '' S ↔
      z ∈ ⋃ n : J, (fun x : ℝ × ℝ =>
        (x.1 + (n.val.1 : ℝ) * p, x.2 + (n.val.2 : ℝ) * p)) '' S := by
  classical
  obtain ⟨B, hB⟩ := hS.isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := hW.isBounded.exists_norm_le
  obtain ⟨m, hm⟩ := exists_nat_gt ((B + C) / p)
  let J := (Finset.Icc (-(m : ℤ)) m) ×ˢ (Finset.Icc (-(m : ℤ)) m)
  refine ⟨J, ?_⟩
  intro z hz
  constructor
  · rintro ⟨x, hx, heq⟩
    obtain ⟨a, ha⟩ := coe_eq_iff_integer_translate.mp (congrArg Prod.fst heq).symm
    obtain ⟨b, hb⟩ := coe_eq_iff_integer_translate.mp (congrArg Prod.snd heq).symm
    have hbound {u v : ℝ} {n : ℤ} (hu : |u| ≤ C) (hv : |v| ≤ B)
        (hn : u = v + (n : ℝ) * p) : n ∈ Finset.Icc (-(m : ℤ)) m := by
      have hm' : B + C < (m : ℝ) * p := (div_lt_iff₀ hp).mp hm
      have hnp : |(n : ℝ) * p| ≤ B + C := by
        calc
          |(n : ℝ) * p| = |u - v| := by congr 1; linarith
          _ ≤ |u| + |v| := abs_sub u v
          _ ≤ B + C := by linarith
      rw [abs_mul, abs_of_pos hp] at hnp
      have habs : |(n : ℝ)| < m := by nlinarith
      have hlow : (-(m : ℤ) : ℝ) ≤ (n : ℝ) := by
        push_cast
        linarith [abs_le.mp (le_of_lt habs)]
      have hhigh : (n : ℝ) ≤ (m : ℤ) := by
        exact le_trans (le_abs_self _) (le_of_lt habs)
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlow, by exact_mod_cast hhigh⟩
    have haJ := hbound ((Real.norm_eq_abs _).symm ▸ (norm_fst_le z).trans (hC z hz))
      ((Real.norm_eq_abs _).symm ▸ (norm_fst_le x).trans (hB x hx)) ha
    have hbJ := hbound ((Real.norm_eq_abs _).symm ▸ (norm_snd_le z).trans (hC z hz))
      ((Real.norm_eq_abs _).symm ▸ (norm_snd_le x).trans (hB x hx)) hb
    exact mem_iUnion.mpr ⟨⟨(a, b), Finset.mem_product.mpr ⟨haJ, hbJ⟩⟩,
      x, hx, Prod.ext ha.symm hb.symm⟩
  · intro hzJ
    obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.mp hzJ
    refine ⟨x, hx, Prod.ext ?_ ?_⟩
    · exact (coe_eq_iff_integer_translate.mpr ⟨n.val.1, rfl⟩).symm
    · exact (coe_eq_iff_integer_translate.mpr ⟨n.val.2, rfl⟩).symm

end PoincareConjecture.M76.PeriodicSquare
