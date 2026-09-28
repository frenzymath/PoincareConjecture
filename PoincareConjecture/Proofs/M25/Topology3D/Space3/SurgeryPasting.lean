import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

noncomputable def levelPaste {X Y : Type*} (h : X → ℝ) (f g : X → Y) (x : X) : Y :=
  if 0 ≤ h x then f x else g x

theorem levelPaste_of_nonneg {X Y : Type*} (h : X → ℝ) (f g : X → Y)
    {x : X} (hx : 0 ≤ h x) : levelPaste h f g x = f x := by
  simp only [levelPaste, if_pos hx]

theorem levelPaste_of_neg {X Y : Type*} (h : X → ℝ) (f g : X → Y)
    {x : X} (hx : h x < 0) : levelPaste h f g x = g x := by
  simp only [levelPaste, if_neg (not_le.mpr hx)]

theorem levelPaste_eqOn_upper {X Y : Type*} (h : X → ℝ) (f g : X → Y)
    {d : ℝ} (hd : 0 < d) (heq : ∀ x, |h x| < d → f x = g x) :
    EqOn (levelPaste h f g) f {x | -d < h x} := by
  intro x hx
  by_cases hp : 0 ≤ h x
  · exact levelPaste_of_nonneg h f g hp
  · rw [levelPaste_of_neg h f g (lt_of_not_ge hp)]
    exact (heq x (abs_lt.mpr ⟨hx, lt_trans (lt_of_not_ge hp) hd⟩)).symm

theorem levelPaste_eqOn_lower {X Y : Type*} (h : X → ℝ) (f g : X → Y)
    {d : ℝ} (hd : 0 < d) (heq : ∀ x, |h x| < d → f x = g x) :
    EqOn (levelPaste h f g) g {x | h x < d} := by
  intro x hx
  by_cases hp : 0 ≤ h x
  · rw [levelPaste_of_nonneg h f g hp]
    exact heq x (abs_lt.mpr ⟨lt_of_lt_of_le (neg_neg_of_pos hd) hp, hx⟩)
  · exact levelPaste_of_neg h f g (lt_of_not_ge hp)

variable {E F H K X Y : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
variable [TopologicalSpace X] [ChartedSpace H X]
variable [TopologicalSpace Y] [ChartedSpace K Y]

theorem levelPaste_contMDiff (h : X → ℝ) (hh : Continuous h) (f g : X → Y)
    {d : ℝ} (hd : 0 < d) (heq : ∀ x, |h x| < d → f x = g x)
    (hf : ContMDiffOn I J ∞ f {x | -d < h x})
    (hg : ContMDiffOn I J ∞ g {x | h x < d}) :
    ContMDiff I J ∞ (levelPaste h f g) := by
  have hU : IsOpen {x | -d < h x} := isOpen_lt continuous_const hh
  have hV : IsOpen {x | h x < d} := isOpen_lt hh continuous_const
  apply contMDiff_of_contMDiffOn_union_of_isOpen
    (hf.congr (levelPaste_eqOn_upper h f g hd heq))
    (hg.congr (levelPaste_eqOn_lower h f g hd heq)) ?_ hU hV
  ext x
  simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
  by_cases hx : -d < h x
  · exact Or.inl hx
  · exact Or.inr (lt_of_le_of_lt (le_of_not_gt hx) (by linarith))

theorem levelPaste_mfderiv_injective (h : X → ℝ) (hh : Continuous h) (f g : X → Y)
    {d : ℝ} (hd : 0 < d) (heq : ∀ x, |h x| < d → f x = g x)
    (hf : ∀ x, -d < h x → Function.Injective (mfderiv I J f x))
    (hg : ∀ x, h x < d → Function.Injective (mfderiv I J g x)) :
    ∀ x, Function.Injective (mfderiv I J (levelPaste h f g) x) := by
  intro x
  by_cases hx : -d < h x
  · have hnear : levelPaste h f g =ᶠ[𝓝 x] f :=
      Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const hh).mem_nhds hx)
        (levelPaste_eqOn_upper h f g hd heq)
    rw [hnear.mfderiv_eq]
    exact hf x hx
  · have hxV : h x < d := lt_of_le_of_lt (le_of_not_gt hx) (by linarith)
    have hnear : levelPaste h f g =ᶠ[𝓝 x] g :=
      Filter.eventuallyEq_of_mem ((isOpen_lt hh continuous_const).mem_nhds hxV)
        (levelPaste_eqOn_lower h f g hd heq)
    rw [hnear.mfderiv_eq]
    exact hg x hxV

omit [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace K Y] in

theorem levelPaste_range (h : X → ℝ) (f g : X → Y)
    (heq : ∀ x, h x = 0 → f x = g x) :
    range (levelPaste h f g) = f '' {x | 0 ≤ h x} ∪ g '' {x | h x ≤ 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : 0 ≤ h x
    · exact Or.inl ⟨x, hx, (levelPaste_of_nonneg h f g hx).symm⟩
    · exact Or.inr ⟨x, (lt_of_not_ge hx).le,
        (levelPaste_of_neg h f g (lt_of_not_ge hx)).symm⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, levelPaste_of_nonneg h f g hx⟩
    · by_cases hp : 0 ≤ h x
      · exact ⟨x, (levelPaste_of_nonneg h f g hp).trans (heq x (le_antisymm hx hp))⟩
      · exact ⟨x, levelPaste_of_neg h f g (lt_of_not_ge hp)⟩

omit [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace K Y] in

theorem levelPaste_injective (h : X → ℝ) (f g : X → Y)
    (hf : InjOn f {x | 0 ≤ h x}) (hg : InjOn g {x | h x ≤ 0})
    (hcross : ∀ x, 0 ≤ h x → ∀ y, h y ≤ 0 → f x = g y → x = y) :
    Function.Injective (levelPaste h f g) := by
  intro x y hxy
  by_cases hx : 0 ≤ h x <;> by_cases hy : 0 ≤ h y
  · rw [levelPaste_of_nonneg h f g hx, levelPaste_of_nonneg h f g hy] at hxy
    exact hf hx hy hxy
  · rw [levelPaste_of_nonneg h f g hx, levelPaste_of_neg h f g (lt_of_not_ge hy)] at hxy
    exact hcross x hx y (lt_of_not_ge hy).le hxy
  · rw [levelPaste_of_neg h f g (lt_of_not_ge hx), levelPaste_of_nonneg h f g hy] at hxy
    exact (hcross y hy x (lt_of_not_ge hx).le hxy.symm).symm
  · rw [levelPaste_of_neg h f g (lt_of_not_ge hx),
      levelPaste_of_neg h f g (lt_of_not_ge hy)] at hxy
    exact hg (lt_of_not_ge hx).le (lt_of_not_ge hy).le hxy

end PoincareConjecture.M25.Topology3D
