import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.Uniqueness
import Mathlib.Algebra.Order.Floor.Ring



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_forward_integralCurve_of_finite_integralCurves
    {X : (x : M) → TangentSpace (𝓡 n) x} {U K : Set M} (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) U) {x : M}
    (hfinite : ∀ k : ℕ, ∃ a b : ℝ, a < 0 ∧ (k : ℝ) + 1 < b ∧
      ∃ α : ℝ → M, α 0 = x ∧ (∀ t ∈ Ioo a b, α t ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) α X (Ioo a b) ∧
        ∀ t ∈ Icc 0 ((k : ℝ) + 1), α t ∈ K) :
    ∃ a < 0, ∃ γ : ℝ → M, γ 0 = x ∧ (∀ t ∈ Ioi a, γ t ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ X (Ioi a) ∧
      ∀ t : ℝ, 0 ≤ t → γ t ∈ K := by
  choose a b ha hb α hinit hαU hα hK using hfinite
  have hagree (i j : ℕ) : EqOn (α i) (α j)
      (Ioo (max (a i) (a j)) (min ((i : ℝ) + 1) ((j : ℝ) + 1))) := by
    have hi : Ioo (max (a i) (a j)) (min ((i : ℝ) + 1) ((j : ℝ) + 1)) ⊆
        Ioo (a i) (b i) := Ioo_subset_Ioo (le_max_left _ _)
      ((min_le_left _ _).trans (hb i).le)
    have hj : Ioo (max (a i) (a j)) (min ((i : ℝ) + 1) ((j : ℝ) + 1)) ⊆
        Ioo (a j) (b j) := Ioo_subset_Ioo (le_max_right _ _)
      ((min_le_right _ _).trans (hb j).le)
    exact eqOn_of_isMIntegralCurveOn hU hX isOpen_Ioo isPreconnected_Ioo
      (show 0 ∈ Ioo (max (a i) (a j)) (min ((i : ℝ) + 1) ((j : ℝ) + 1)) from
        ⟨max_lt (ha i) (ha j), lt_min (by positivity) (by positivity)⟩)
      (fun t ht => hαU i t (hi ht)) ((hα i).mono hi) ((hα j).mono hj)
      ((hinit i).trans (hinit j).symm)
  let γ : ℝ → M := fun t => if t < 0 then α 0 t else α ⌈t⌉₊ t
  have heq (k : ℕ) : EqOn γ (α k) (Ioo (max (a 0) (a k)) ((k : ℝ) + 1)) := by
    intro t ht
    dsimp only [γ]
    split_ifs with ht0
    · exact hagree 0 k ⟨ht.1, lt_min (by simpa using ht0.trans zero_lt_one) ht.2⟩
    · exact hagree ⌈t⌉₊ k ⟨(max_lt (ha _) (ha _)).trans_le (le_of_not_gt ht0),
        lt_min (by linarith [Nat.le_ceil t]) ht.2⟩
  have hnear (t : ℝ) (ht : t ∈ Ioi (a 0)) :
      ∃ k : ℕ, t ∈ Ioo (a k) (b k) ∧ γ =ᶠ[𝓝 t] α k := by
    by_cases ht0 : t < 0
    · refine ⟨0, ⟨ht, ht0.trans (by linarith [hb 0] : 0 < b 0)⟩, ?_⟩
      filter_upwards [isOpen_Iio.mem_nhds ht0] with s hs
      exact if_pos hs
    · have ht0' := le_of_not_gt ht0
      have htI : t ∈ Ioo (max (a 0) (a ⌈t⌉₊)) ((⌈t⌉₊ : ℝ) + 1) :=
        ⟨(max_lt (ha _) (ha _)).trans_le ht0', by linarith [Nat.le_ceil t]⟩
      refine ⟨⌈t⌉₊, ⟨(ha _).trans_le ht0', htI.2.trans (hb _)⟩, ?_⟩
      exact Filter.Eventually.mono (isOpen_Ioo.mem_nhds htI) fun _ hs => heq _ hs
  refine ⟨a 0, ha 0, γ, ?_, ?_, ?_, ?_⟩
  · simp [γ, hinit]
  · intro t ht
    obtain ⟨k, hk, he⟩ := hnear t ht
    rw [he.self_of_nhds]
    exact hαU k t hk
  · intro t ht
    obtain ⟨k, hk, he⟩ := hnear t ht
    have hd := (((hα k).isMIntegralCurveAt (isOpen_Ioo.mem_nhds hk)).hasMFDerivAt.congr_of_eventuallyEq
      he).hasMFDerivWithinAt (s := Ioi (a 0))
    convert hd using 1
    rw [he.self_of_nhds]
  · intro t ht
    rw [show γ t = α ⌈t⌉₊ t from if_neg (not_lt.mpr ht)]
    exact hK _ t ⟨ht, by linarith [Nat.le_ceil t]⟩

end Poincare.Manifold
