import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Prolongation
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds.Bootstrap

variable {D E V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def EventuallyBoundedJet {α : Type*} (l : Filter α) (S : α → Set D)
    (f : α → D → E) (m : ℕ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ a in l, ∀ x ∈ S a, ‖iteratedFDeriv ℝ m (f a) x‖ ≤ B

theorem EventuallyBoundedJet.bound_all {α : Type*} {l : Filter α} {S : α → Set D}
    {f : α → D → E} {m : ℕ} (h : ∀ j ≤ m, EventuallyBoundedJet l S f j) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ a in l, ∀ j ≤ m, ∀ x ∈ S a,
      ‖iteratedFDeriv ℝ j (f a) x‖ ≤ B := by
  classical
  choose B hB hbound using fun j : Fin (m + 1) => h j (by omega)
  refine ⟨∑ j, B j, Finset.sum_nonneg (fun j _ => hB j), ?_⟩
  filter_upwards [eventually_all.mpr hbound] with a ha j hj x hx
  let i : Fin (m + 1) := ⟨j, by omega⟩
  exact (ha i x hx).trans (Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i))

theorem EventuallyBoundedJet.comp {α : Type*} {l : Filter α} {S : α → Set D}
    {f : α → D → E} {g : E → V} {Ω K : Set E} {m : ℕ}
    (hΩ : IsOpen Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hf : ∀ a x, x ∈ S a → ContDiffAt ℝ ∞ (f a) x)
    (hrange : ∀ᶠ a in l, MapsTo (f a) (S a) K)
    (hbound : ∀ j ≤ m, EventuallyBoundedJet l S f j) :
    EventuallyBoundedJet l S (fun a => g ∘ f a) m := by
  classical
  have hout (j : Fin (m + 1)) : ∃ A : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ (j : ℕ) g x‖ ≤ A :=
    hK.exists_bound_of_continuousOn (fun x hx =>
      ((hg.contDiffAt (hΩ.mem_nhds (hKΩ hx))).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top)).continuousWithinAt)
  choose A hA using hout
  let C : ℝ := ∑ j, max (A j) 0
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  obtain ⟨B, hB, hb⟩ := EventuallyBoundedJet.bound_all hbound
  refine ⟨m.factorial * C * (max B 1) ^ m, by positivity, ?_⟩
  filter_upwards [hrange, hb] with a ha hba x hx
  apply Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_le_of_contDiffAt
    (hf a x hx) (hg.contDiffAt (hΩ.mem_nhds (hKΩ (ha hx)))) m
  · intro j hj
    let i : Fin (m + 1) := ⟨j, by omega⟩
    exact (hA i _ (ha hx)).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun k _ => le_max_right (A k) 0) (Finset.mem_univ i)))
  · intro j hj hjm
    exact (hba j hjm x hx).trans ((le_max_left _ _).trans
      (le_self_pow₀ (le_max_right B 1) (Nat.ne_of_gt hj)))

theorem norm_iteratedFDeriv_pi_le {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {f : D → (i : ι) → F i} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i, ‖iteratedFDeriv ℝ m (fun y => f y i) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m f x‖ ≤ B := by
  apply ContinuousMultilinearMap.opNorm_le_bound hB
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have heq := congrArg (fun T => T v)
    ((ContinuousLinearMap.proj i).iteratedFDeriv_comp_left hf
      (i := m) (by exact_mod_cast le_top))
  change ‖(iteratedFDeriv ℝ m f x) v i‖ ≤ _
  change (iteratedFDeriv ℝ m (fun y => f y i) x) v =
    (iteratedFDeriv ℝ m f x) v i at heq
  rw [← heq]
  exact ((iteratedFDeriv ℝ m (fun y => f y i) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hbound i) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem EventuallyBoundedJet.pi {α ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {l : Filter α} {S : α → Set D} {f : α → D → (i : ι) → F i} {m : ℕ}
    (hf : ∀ a x, x ∈ S a → ContDiffAt ℝ ∞ (f a) x)
    (hbound : ∀ i, EventuallyBoundedJet l S (fun a x => f a x i) m) :
    EventuallyBoundedJet l S f m := by
  classical
  choose B hB hb using hbound
  refine ⟨∑ i, B i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  filter_upwards [eventually_all.mpr hb] with a ha x hx
  apply norm_iteratedFDeriv_pi_le (hf a x hx) m (Finset.sum_nonneg (fun i _ => hB i))
  intro i
  exact (ha i x hx).trans (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i))

end PoincareConjecture.SpacetimeBounds.Bootstrap
