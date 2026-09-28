import PoincareConjecture.Definitions.Ch06.LGeometry
import Mathlib.Geometry.Manifold.ContMDiff.Basic








set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_smooth_fin_gluing (m : ℕ) (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (γ : ℝ → M) (f : Fin m → ℝ → M)
    (hf : ∀ i, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (f i))
    (hleft : ∀ i s, s ≤ t i.castSucc → f i s = γ (t i.castSucc))
    (hright : ∀ i s, t i.succ ≤ s → f i s = γ (t i.succ))
    (hleftgerm : ∀ i, f i =ᶠ[𝓝 (t i.castSucc)] fun _ ↦ γ (t i.castSucc))
    (hrightgerm : ∀ i, f i =ᶠ[𝓝 (t i.succ)] fun _ ↦ γ (t i.succ)) :
    ∃ g : ℝ → M, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ g ∧
      (∀ i, EqOn g (f i) (Icc (t i.castSucc) (t i.succ))) ∧
      (∀ s, s ≤ t 0 → g s = γ (t 0)) ∧
      (∀ s, t (Fin.last m) ≤ s → g s = γ (t (Fin.last m))) ∧
      (g =ᶠ[𝓝 (t 0)] fun _ ↦ γ (t 0)) ∧
      (g =ᶠ[𝓝 (t (Fin.last m))] fun _ ↦ γ (t (Fin.last m))) := by
  classical
  induction m with
  | zero =>
    refine ⟨fun _ ↦ γ (t 0), contMDiff_const, ?_, fun _ _ ↦ rfl,
      fun _ _ ↦ rfl, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
    intro i
    exact Fin.elim0 i
  | succ m ih =>
    let t₀ : Fin (m + 1) → ℝ := fun i ↦ t i.castSucc
    let f₀ : Fin m → ℝ → M := fun i ↦ f i.castSucc
    have ht₀ : Monotone t₀ := fun _ _ hij ↦ ht hij
    obtain ⟨g₀, hg₀, hpieces₀, hleft₀, hright₀, hlg₀, hrg₀⟩ :=
      ih t₀ ht₀ f₀ (fun i ↦ hf i.castSucc)
        (fun i ↦ hleft i.castSucc) (fun i ↦ hright i.castSucc)
        (fun i ↦ hleftgerm i.castSucc) (fun i ↦ hrightgerm i.castSucc)
    let c := t (Fin.last m).castSucc
    let d := t (Fin.last (m + 1))
    let f₁ := f (Fin.last m)
    let g := (Iic c).piecewise g₀ f₁
    have hac : t 0 ≤ c := ht (Fin.zero_le _)
    have hcd : c ≤ d := ht (Fin.castSucc_le_succ (Fin.last m))
    have hfg : g₀ =ᶠ[𝓝 c] f₁ := hrg₀.trans (hleftgerm (Fin.last m)).symm
    have hg : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ g :=
      hg₀.piecewise_Iic (hf (Fin.last m)) hfg
    have heqleft (s : ℝ) (hs : s ≤ c) : g s = g₀ s :=
      piecewise_eq_of_mem (Iic c) g₀ f₁ hs
    have heqright (s : ℝ) (hs : c ≤ s) : g s = f₁ s := by
      by_cases hsc : s ≤ c
      · have hsc' : s = c := le_antisymm hsc hs
        rw [hsc', heqleft c le_rfl, hright₀ c le_rfl]
        exact (hleft (Fin.last m) c le_rfl).symm
      · exact piecewise_eq_of_notMem (Iic c) g₀ f₁ hsc
    have hgc : g =ᶠ[𝓝 c] fun _ ↦ γ c := by
      filter_upwards [hrg₀, hleftgerm (Fin.last m)] with s h₀ h₁
      simp only [g, piecewise]
      split_ifs <;> assumption
    refine ⟨g, hg, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · intro s hs
        exact heqright s hs.1
      · intro s hs
        have hs' : s ≤ c := hs.2.trans (ht (show j.castSucc.succ ≤
          (Fin.last m).castSucc from by simp only [Fin.succ_castSucc]; exact
          Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j.succ)))
        rw [heqleft s hs']
        exact hpieces₀ j hs
    · intro s hs
      exact (heqleft s (hs.trans hac)).trans (hleft₀ s hs)
    · intro s hs
      exact (heqright s (hcd.trans hs)).trans (hright (Fin.last m) s hs)
    · rcases hac.lt_or_eq with hac | hac
      · filter_upwards [hlg₀, Iio_mem_nhds hac] with s hs hsc
        exact (heqleft s hsc.le).trans hs
      · simpa only [hac] using hgc
    · rcases hcd.lt_or_eq with hcd | hcd
      · filter_upwards [hrightgerm (Fin.last m), Ioi_mem_nhds hcd] with s hs hsc
        exact (heqright s hsc.le).trans hs
      · simpa only [hcd] using hgc

theorem mem_fin_partition {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    {s : ℝ} (hs : s ∈ Icc (t 0) (t (Fin.last m))) :
    s = t 0 ∨ ∃ i : Fin m, s ∈ Icc (t i.castSucc) (t i.succ) := by
  induction m with
  | zero => exact Or.inl (le_antisymm hs.2 hs.1)
  | succ m ih =>
    by_cases hsc : s ≤ t (Fin.last m).castSucc
    · rcases ih (fun i ↦ t i.castSucc) (fun _ _ hij ↦ ht hij) ⟨hs.1, hsc⟩ with h | ⟨i, hi⟩
      · exact Or.inl h
      · exact Or.inr ⟨i.castSucc, hi⟩
    · exact Or.inr ⟨Fin.last m, le_of_not_ge hsc, hs.2⟩

open MeasureTheory
open scoped intervalIntegral

theorem integrable_sum_fin_partition {m : ℕ} (t : Fin (m + 1) → ℝ) (f : ℝ → ℝ)
    (hf : ∀ i : Fin m, IntervalIntegrable f volume (t i.castSucc) (t i.succ)) :
    IntervalIntegrable f volume (t 0) (t (Fin.last m)) ∧
      (∑ i : Fin m, ∫ s in t i.castSucc..t i.succ, f s) =
        ∫ s in t 0..t (Fin.last m), f s := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hint, heq⟩ := ih (fun i ↦ t i.castSucc) (fun i ↦ hf i.castSucc)
    refine ⟨hint.trans (hf (Fin.last m)), ?_⟩
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin m, ∫ s in t i.castSucc.castSucc..t i.castSucc.succ, f s) =
      ∫ s in t 0..t (Fin.last m).castSucc, f s at heq
    rw [heq]
    exact intervalIntegral.integral_add_adjacent_intervals hint (hf (Fin.last m))

end PoincareConjecture.M08
