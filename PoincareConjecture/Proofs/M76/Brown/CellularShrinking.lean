import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Compact

set_option autoImplicit false

open Set Filter Metric
open scoped Topology BoundedContinuousFunction

namespace Homeomorph

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_collapse_of_nested_shrinking
    (K : ℕ → Set X) (hclosed : ∀ n, IsClosed (K n)) (hnested : Antitone K)
    (H : ℕ → X ≃ₜ X)
    (hstep : ∀ n, EqOn (H (n + 1)) (H n) (K n)ᶜ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hsmall : ∀ n x, x ∈ K n → ∀ y, y ∈ K n →
      dist (H n x) (H n y) ≤ ε n) :
    ∃ f : C(X, X),
      TendstoUniformly (fun n x => H n x) f atTop ∧ Function.Surjective f ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ ⋂ n, K n) ∧ (y ∈ ⋂ n, K n)) ∧
      ∀ x, (∀ n, H n x = x) → f x = x := by
  have houtside (n m : ℕ) (hnm : n ≤ m) : EqOn (H m) (H n) (K n)ᶜ := by
    induction m, hnm using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ m hnm ih =>
        intro x hx
        calc
          H (m + 1) x = H m x := hstep m (fun hxm => hx (hnested hnm hxm))
          _ = H n x := ih hx
  have himage (n m : ℕ) (hnm : n ≤ m) : H m '' K n = H n '' K n := by
    apply compl_injective
    rw [← (H m).image_compl, ← (H n).image_compl]
    exact image_congr (houtside n m hnm)
  have htail (n m : ℕ) (hnm : n ≤ m) (x : X) :
      dist (H n x) (H m x) ≤ ε n := by
    by_cases hx : x ∈ K n
    · have hm : H m x ∈ H n '' K n := by
        rw [← himage n m hnm]
        exact mem_image_of_mem (H m) hx
      obtain ⟨y, hy, he⟩ := hm
      rw [← he]
      exact hsmall n x hx y hy
    · rw [houtside n m hnm hx, dist_self]
      exact hε n
  let F : ℕ → X →ᵇ X := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨H n, (H n).continuous⟩
  have hF : CauchySeq F := by
    apply cauchySeq_of_le_tendsto_0' ε _ hε0
    intro n m hnm
    exact (BoundedContinuousFunction.dist_le (hε n)).mpr (htail n m hnm)
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hF
  have huniform : TendstoUniformly (fun n x => H n x) f atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hf
  have hpoint (x : X) : Tendsto (fun n => H n x) atTop (𝓝 (f x)) :=
    huniform.tendsto_at x
  have hfixed (x : X) (hx : ∀ n, H n x = x) : f x = x := by
    exact tendsto_nhds_unique (hpoint x)
      (tendsto_const_nhds.congr (fun n => (hx n).symm))
  have hvalue (n : ℕ) (x : X) (hx : x ∉ K n) : f x = H n x := by
    apply tendsto_nhds_unique (hpoint x)
    apply tendsto_const_nhds.congr'
    exact eventually_atTop.mpr ⟨n, fun m hnm => (houtside n m hnm hx).symm⟩
  have hmem (n : ℕ) (x : X) (hx : x ∈ ⋂ j, K j) : f x ∈ H n '' K n := by
    apply ((hclosed n).isCompact.image (H n).continuous).isClosed.mem_of_tendsto (hpoint x)
    refine eventually_atTop.mpr ⟨n, fun m hnm => ?_⟩
    rw [← himage n m hnm]
    exact mem_image_of_mem (H m) (mem_iInter.mp hx n)
  have hseparate (x y : X) (hx : x ∉ ⋂ n, K n) (hy : y ∈ ⋂ n, K n) :
      f x ≠ f y := by
    obtain ⟨n, hn⟩ : ∃ n, x ∉ K n := by
      simpa only [mem_iInter, not_forall] using hx
    intro he
    have hximage : H n x ∈ H n '' K n := by
      rw [← hvalue n x hn, he]
      exact hmem n y hy
    obtain ⟨z, hz, hzx⟩ := hximage
    exact hn ((H n).injective hzx ▸ hz)
  have hsurj : Function.Surjective f := by
    intro y
    by_contra hy
    have hyrange : y ∉ range f := by simpa only [mem_range] using hy
    have hclosedrange : IsClosed (range f) := (isCompact_range f.continuous).isClosed
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hclosedrange.isOpen_compl y hyrange
    obtain ⟨n, hn⟩ := ((Metric.tendstoUniformly_iff.mp huniform) r hr).exists
    obtain ⟨x, hx⟩ := (H n).surjective y
    have hfball : f x ∈ ball y r := by
      rw [mem_ball, ← hx]
      exact hn x
    exact (hball hfball) (mem_range_self x)
  refine ⟨f.toContinuousMap, huniform, hsurj, ?_, hfixed⟩
  intro x y
  constructor
  · intro he
    by_cases hx : x ∈ ⋂ n, K n
    · by_cases hy : y ∈ ⋂ n, K n
      · exact Or.inr ⟨hx, hy⟩
      · exact False.elim (hseparate y x hy hx he.symm)
    · by_cases hy : y ∈ ⋂ n, K n
      · exact False.elim (hseparate x y hx hy he)
      · obtain ⟨n, hn⟩ : ∃ n, x ∉ K n := by
          simpa only [mem_iInter, not_forall] using hx
        obtain ⟨m, hm⟩ : ∃ m, y ∉ K m := by
          simpa only [mem_iInter, not_forall] using hy
        have hxn : x ∉ K (max n m) := fun h => hn (hnested (le_max_left n m) h)
        have hym : y ∉ K (max n m) := fun h => hm (hnested (le_max_right n m) h)
        exact Or.inl ((H (max n m)).injective
          ((hvalue (max n m) x hxn).symm.trans (he.trans (hvalue (max n m) y hym))))
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · apply eq_of_dist_eq_zero
      apply le_antisymm _ dist_nonneg
      exact le_of_tendsto_of_tendsto ((hpoint x).dist (hpoint y)) hε0
        (Eventually.of_forall (fun n => hsmall n x (mem_iInter.mp hx n)
          y (mem_iInter.mp hy n)))

end Homeomorph
