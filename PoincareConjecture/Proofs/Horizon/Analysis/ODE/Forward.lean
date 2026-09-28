import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Uniqueness.Open
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section

namespace Poincare.ODE

open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_gluing_of_solutions
    {U : Set E} (hU : IsOpen U) {F : E → E} (hF : ContDiffOn ℝ ∞ F U)
    {J₁ J₂ : Set ℝ} (hJ₁ : IsOpen J₁) (hJ₂ : IsOpen J₂)
    (hc₁ : Convex ℝ J₁) (hc₂ : Convex ℝ J₂) {α β : ℝ → E}
    (hα : ∀ t ∈ J₁, α t ∈ U ∧ HasDerivAt α (F (α t)) t)
    (hβ : ∀ t ∈ J₂, β t ∈ U ∧ HasDerivAt β (F (β t)) t)
    {a : ℝ} (ha : a ∈ J₁ ∩ J₂) (hjoin : α a = β a) :
    ∃ γ : ℝ → E, EqOn γ α J₁ ∧ EqOn γ β J₂ ∧
      ∀ t ∈ J₁ ∪ J₂, γ t ∈ U ∧ HasDerivAt γ (F (γ t)) t := by
  classical
  have hagree := eqOn_of_hasDerivAt hU hF (hJ₁.inter hJ₂)
    (hc₁.inter hc₂).isPreconnected (fun t ht => hα t ht.1)
    (fun t ht => hβ t ht.2) ha hjoin
  let γ : ℝ → E := fun t => if t ∈ J₁ then α t else β t
  have heq₁ : EqOn γ α J₁ := fun t ht => if_pos ht
  have heq₂ : EqOn γ β J₂ := by
    intro t ht
    by_cases ht₁ : t ∈ J₁
    · exact (if_pos ht₁).trans (hagree ⟨ht₁, ht⟩)
    · exact if_neg ht₁
  refine ⟨γ, heq₁, heq₂, ?_⟩
  intro t ht
  rcases ht with ht | ht
  · have he : γ =ᶠ[𝓝 t] α :=
      Filter.Eventually.mono (hJ₁.mem_nhds ht) fun _ hs => heq₁ hs
    rw [heq₁ ht]
    exact ⟨(hα t ht).1, (hα t ht).2.congr_of_eventuallyEq he⟩
  · have he : γ =ᶠ[𝓝 t] β :=
      Filter.Eventually.mono (hJ₂.mem_nhds ht) fun _ hs => heq₂ hs
    rw [heq₂ ht]
    exact ⟨(hβ t ht).1, (hβ t ht).2.congr_of_eventuallyEq he⟩

theorem exists_forward_solution_of_finite_solutions
    {U K : Set E} (hU : IsOpen U) {F : E → E} (hF : ContDiffOn ℝ ∞ F U)
    {x : E}
    (hfinite : ∀ k : ℕ, ∃ δ > 0, ∃ α : ℝ → E, α 0 = x ∧
      (∀ t ∈ Ioo (-δ) ((k : ℝ) + 1 + δ), α t ∈ U ∧ HasDerivAt α (F (α t)) t) ∧
      ∀ t ∈ Icc 0 ((k : ℝ) + 1), α t ∈ K) :
    ∃ δ > 0, ∃ γ : ℝ → E, γ 0 = x ∧
      (∀ t ∈ Ioi (-δ), γ t ∈ U ∧ HasDerivAt γ (F (γ t)) t) ∧
      ∀ t : ℝ, 0 ≤ t → γ t ∈ K := by
  choose δ hδ α hinit hα hK using hfinite
  have hagree (i j : ℕ) : EqOn (α i) (α j)
      (Ioo (-min (δ i) (δ j)) (min ((i : ℝ) + 1) ((j : ℝ) + 1))) := by
    apply eqOn_of_hasDerivAt hU hF isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (fun t ht => hα i t ⟨by linarith [min_le_left (δ i) (δ j), ht.1],
        by linarith [min_le_left ((i : ℝ) + 1) ((j : ℝ) + 1), ht.2, hδ i]⟩)
      (fun t ht => hα j t ⟨by linarith [min_le_right (δ i) (δ j), ht.1],
        by linarith [min_le_right ((i : ℝ) + 1) ((j : ℝ) + 1), ht.2, hδ j]⟩)
      (a := 0)
    · exact ⟨neg_neg_of_pos (lt_min (hδ i) (hδ j)),
        lt_min (by positivity) (by positivity)⟩
    · rw [hinit i, hinit j]
  let γ : ℝ → E := fun t => if t < 0 then α 0 t else α ⌈t⌉₊ t
  have heq (k : ℕ) : EqOn γ (α k)
      (Ioo (-min (δ 0) (δ k)) ((k : ℝ) + 1)) := by
    intro t ht
    dsimp [γ]
    split_ifs with ht0
    · exact hagree 0 k ⟨ht.1, lt_min (by simpa using ht0.trans (by norm_num : (0 : ℝ) < 1)) ht.2⟩
    · have ht0' : 0 ≤ t := le_of_not_gt ht0
      exact hagree ⌈t⌉₊ k ⟨by linarith [lt_min (hδ ⌈t⌉₊) (hδ k)],
        lt_min (by linarith [Nat.le_ceil t]) ht.2⟩
  refine ⟨δ 0, hδ 0, γ, ?_, ?_, ?_⟩
  · simp [γ, hinit]
  · intro t ht
    by_cases ht0 : t < 0
    · have hnear : γ =ᶠ[𝓝 t] α 0 := by
        filter_upwards [isOpen_Iio.mem_nhds ht0] with s hs
        exact if_pos hs
      have hd := hα 0 t ⟨ht, by simpa using ht0.trans (by linarith [hδ 0] : (0 : ℝ) < 1 + δ 0)⟩
      rw [hnear.self_of_nhds]
      exact ⟨hd.1, hd.2.congr_of_eventuallyEq hnear⟩
    · have ht0' : 0 ≤ t := le_of_not_gt ht0
      have htI : t ∈ Ioo (-min (δ 0) (δ ⌈t⌉₊)) ((⌈t⌉₊ : ℝ) + 1) :=
        ⟨by linarith [lt_min (hδ 0) (hδ ⌈t⌉₊)], by linarith [Nat.le_ceil t]⟩
      have hnear : γ =ᶠ[𝓝 t] α ⌈t⌉₊ :=
        Filter.Eventually.mono (isOpen_Ioo.mem_nhds htI) fun _ hs => heq _ hs
      have hd := hα ⌈t⌉₊ t ⟨by linarith [hδ ⌈t⌉₊], by linarith [htI.2, hδ ⌈t⌉₊]⟩
      rw [hnear.self_of_nhds]
      exact ⟨hd.1, hd.2.congr_of_eventuallyEq hnear⟩
  · intro t ht
    rw [show γ t = α ⌈t⌉₊ t from if_neg (not_lt.mpr ht)]
    exact hK _ t ⟨ht, by linarith [Nat.le_ceil t]⟩

end Poincare.ODE
