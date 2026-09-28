import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Basic










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {ι E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]


def HasUniformJetBounds (n : ℕ) (f : ι → E → F) : Prop :=
  ∀ m : ℕ, m ≤ n → ∃ C : ℝ, ∀ i x, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C


def HasUniformJetBoundsOn (n : ℕ) (s : Set E) (f : ι → E → F) : Prop :=
  ∀ m : ℕ, m ≤ n → ∃ C : ℝ, ∀ i x, x ∈ s →
    ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C

theorem HasUniformJetBoundsOn.mono {n : ℕ} {s t : Set E} {f : ι → E → F} (hst : s ⊆ t)
    (h : HasUniformJetBoundsOn n t f) : HasUniformJetBoundsOn n s f := by
  intro m hm
  obtain ⟨C, hC⟩ := h m hm
  exact ⟨C, fun i x hx => hC i x (hst hx)⟩

theorem HasUniformJetBoundsOn.mono_order {m n : ℕ} {s : Set E} {f : ι → E → F}
    (hmn : m ≤ n) (h : HasUniformJetBoundsOn n s f) : HasUniformJetBoundsOn m s f := by
  intro j hj
  exact h j (hj.trans hmn)

theorem HasUniformJetBounds.on_univ {n : ℕ} {f : ι → E → F} (h : HasUniformJetBounds n f) :
    HasUniformJetBoundsOn n Set.univ f := by
  intro m hm
  obtain ⟨C, hC⟩ := h m hm
  exact ⟨C, fun i x _ => hC i x⟩

theorem HasUniformJetBoundsOn.bound_nonneg {n : ℕ} {s : Set E} {f : ι → E → F}
    (h : HasUniformJetBoundsOn n s f)
    {m : ℕ} (hm : m ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ s →
      ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := h m hm
  refine ⟨max C 0, le_max_right _ _, fun i x hx => (hC i x hx).trans (le_max_left _ _)⟩

theorem HasUniformJetBounds.bound_nonneg {n : ℕ} {f : ι → E → F}
    (h : HasUniformJetBounds n f)
    {m : ℕ} (hm : m ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := h.on_univ.bound_nonneg hm
  exact ⟨C, hC, fun i x => h i x (mem_univ x)⟩

private theorem HasUniformJetBoundsOn.bound_all {n : ℕ} {s : Set E} {f : ι → E → F}
    (h : HasUniformJetBoundsOn n s f) {m : ℕ} (hm : m ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, j ≤ m → ∀ i x, x ∈ s →
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C := by
  classical
  choose c hc using fun j : Finset.range (m + 1) => h j.1
    (Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.1 j.2)) hm)
  let C : ℝ := ∑ j : Finset.range (m + 1), max (c j) 0
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  refine ⟨C, hC, fun j hj i x hx => ?_⟩
  have hj' : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hs : max (c ⟨j, hj'⟩) 0 ≤ C :=
    Finset.single_le_sum (fun k _ => le_max_right _ _) (Finset.mem_univ _)
  exact (hc ⟨j, hj'⟩ i x hx).trans ((le_max_left _ _).trans hs)

private theorem HasUniformJetBounds.bound_all {n : ℕ} {f : ι → E → F}
    (h : HasUniformJetBounds n f) {m : ℕ} (hm : m ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, j ≤ m → ∀ i x,
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C := by
  classical
  choose c hc using fun j : Finset.range (m + 1) => h j.1
    (Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.1 j.2)) hm)
  let C : ℝ := ∑ j : Finset.range (m + 1), max (c j) 0
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  refine ⟨C, hC, fun j hj i x => ?_⟩
  have hj' : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hsingle : max (c ⟨j, hj'⟩) 0 ≤ C :=
    Finset.single_le_sum (fun k _ => le_max_right _ _) (Finset.mem_univ _)
  exact (hc ⟨j, hj'⟩ i x).trans ((le_max_left _ _).trans hsingle)

theorem HasUniformJetBounds.prodMk {n : ℕ} {f : ι → E → F} {g : ι → E → G}
    (hf : HasUniformJetBounds n f) (hg : HasUniformJetBounds n g)
    (hcf : ∀ i, ContDiff ℝ (n : ℕ∞) (f i))
    (hcg : ∀ i, ContDiff ℝ (n : ℕ∞) (g i)) :
    HasUniformJetBounds n (fun i x => (f i x, g i x)) := by
  intro m hm
  obtain ⟨Cf, hCf0, hCf⟩ := hf.bound_nonneg hm
  obtain ⟨Cg, hCg0, hCg⟩ := hg.bound_nonneg hm
  refine ⟨max Cf Cg, fun i x => ?_⟩
  rw [iteratedFDeriv_prodMk (hcf i).contDiffAt (hcg i).contDiffAt (by exact_mod_cast hm)]
  rw [ContinuousMultilinearMap.opNorm_prod]
  exact max_le ((hCf i x).trans (le_max_left _ _)) (hCg i x |>.trans (le_max_right _ _))

theorem HasUniformJetBoundsOn.prodMk {n : ℕ} {s : Set E} {f : ι → E → F} {g : ι → E → G}
    (hs : IsOpen s) (hf : HasUniformJetBoundsOn n s f) (hg : HasUniformJetBoundsOn n s g)
    (hcf : ∀ i, ContDiffOn ℝ (n : ℕ∞) (f i) s)
    (hcg : ∀ i, ContDiffOn ℝ (n : ℕ∞) (g i) s) :
    HasUniformJetBoundsOn n s (fun i x => (f i x, g i x)) := by
  intro m hm
  obtain ⟨Cf, hCf, hCf'⟩ := hf.bound_nonneg hm
  obtain ⟨Cg, hCg, hCg'⟩ := hg.bound_nonneg hm
  refine ⟨max Cf Cg, fun i x hx => ?_⟩
  rw [iteratedFDeriv_prodMk ((hcf i).contDiffAt (hs.mem_nhds hx))
    ((hcg i).contDiffAt (hs.mem_nhds hx)) (by exact_mod_cast hm)]
  rw [ContinuousMultilinearMap.opNorm_prod]
  exact max_le ((hCf' i x hx).trans (le_max_left _ _)) (hCg' i x hx |>.trans (le_max_right _ _))

private lemma le_pow_of_le_max_one {A D : ℝ} (hD : D = max A 1)
    {m : ℕ} (hm : 1 ≤ m) : A ≤ D ^ m := by
  have hAD : A ≤ D := by rw [hD]; exact le_max_left _ _
  have hD1 : 1 ≤ D := by rw [hD]; exact le_max_right _ _
  exact hAD.trans (le_self_pow₀ hD1 (Nat.ne_of_gt hm))

theorem HasUniformJetBounds.comp {n : ℕ} {f : ι → E → F} {g : ι → F → G}
    (hf : HasUniformJetBounds n f) (hg : HasUniformJetBounds n g)
    (hcf : ∀ i, ContDiff ℝ (n : ℕ∞) (f i))
    (hcg : ∀ i, ContDiff ℝ (n : ℕ∞) (g i)) :
    HasUniformJetBounds n (fun i => g i ∘ f i) := by
  intro m hm
  obtain ⟨Af, hAf, hAf'⟩ := hf.bound_all hm
  obtain ⟨Ag, hAg, hAg'⟩ := hg.bound_all hm
  let D : ℝ := max Af 1
  refine ⟨Nat.factorial m * Ag * D ^ m, fun i x => ?_⟩
  apply norm_iteratedFDeriv_comp_le (hcg i) (hcf i) (by exact_mod_cast hm) x
  · intro j hj
    exact hAg' j hj i (f i x)
  · intro j hj₁ hj
    exact (hAf' j hj i x).trans (le_pow_of_le_max_one rfl hj₁)



theorem HasUniformJetBounds.comp_fixed {n : ℕ} {f : ι → E → F} {g : F → G}
    {K : Set F} (hf : HasUniformJetBounds n f)
    (hg : HasUniformJetBoundsOn n K (fun _ : Unit => g))
    (hcf : ∀ i, ContDiff ℝ (n : ℕ∞) (f i)) (hcg : ContDiff ℝ (n : ℕ∞) g)
    (hK : ∀ i, Set.range (f i) ⊆ K) :
    HasUniformJetBounds n (fun i => g ∘ f i) := by
  intro m hm
  obtain ⟨Af, hAf, hAf'⟩ := hf.bound_all hm
  classical
  choose c hc using fun j : Finset.range (m + 1) => hg j.1
    (Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.1 j.2)) hm)
  let Ag : ℝ := ∑ j : Finset.range (m + 1), max (c j) 0
  have hAg : 0 ≤ Ag := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  have hAg' : ∀ j, j ≤ m → ∀ x, x ∈ K → ‖iteratedFDeriv ℝ j g x‖ ≤ Ag := by
    intro j hj x hx
    have hj' : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have hs : max (c ⟨j, hj'⟩) 0 ≤ Ag :=
      Finset.single_le_sum (fun k _ => le_max_right _ _) (Finset.mem_univ _)
    exact (hc ⟨j, hj'⟩ () x hx).trans ((le_max_left _ _).trans hs)
  let D : ℝ := max Af 1
  refine ⟨Nat.factorial m * Ag * D ^ m, fun i x => ?_⟩
  apply norm_iteratedFDeriv_comp_le hcg (hcf i) (by exact_mod_cast hm) x
  · intro j hj
    exact hAg' j hj (f i x) (hK i ⟨x, rfl⟩)
  · intro j hj₁ hj
    exact (hAf' j hj i x).trans (le_pow_of_le_max_one rfl hj₁)

theorem HasUniformJetBoundsOn.comp {n : ℕ} {U : Set E} {V : Set F} {f : ι → E → F}
    {g : ι → F → G} (hU : IsOpen U) (hV : IsOpen V)
    (hf : HasUniformJetBoundsOn n U f) (hg : HasUniformJetBoundsOn n V g)
    (hcf : ∀ i, ContDiffOn ℝ (n : ℕ∞) (f i) U)
    (hcg : ∀ i, ContDiffOn ℝ (n : ℕ∞) (g i) V)
    (hmap : ∀ i, MapsTo (f i) U V) :
    HasUniformJetBoundsOn n U (fun i => g i ∘ f i) := by
  intro m hm
  obtain ⟨Af, hAf, hAf'⟩ := HasUniformJetBoundsOn.bound_all hf hm
  obtain ⟨Ag, hAg, hAg'⟩ := HasUniformJetBoundsOn.bound_all hg hm
  let D : ℝ := max Af 1
  refine ⟨Nat.factorial m * Ag * D ^ m, fun i x hx => ?_⟩
  have H := norm_iteratedFDerivWithin_comp_le (hcg i) (hcf i)
    (by exact_mod_cast hm) hV.uniqueDiffOn hU.uniqueDiffOn (hmap i) hx
    (C := Ag) (D := D) ?_ ?_
  · simpa only [iteratedFDerivWithin_of_isOpen m hU hx] using H
  · intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hV (hmap i hx)]
    exact hAg' j hj i (f i x) (hmap i hx)
  · intro j hj₁ hj
    rw [iteratedFDerivWithin_of_isOpen j hU hx]
    exact (hAf' j hj i x hx).trans (le_pow_of_le_max_one rfl hj₁)



theorem HasUniformJetBoundsOn.comp_fixed_on {n : ℕ} {U : Set E} {V K : Set F}
    {f : ι → E → F} {g : F → G} (hU : IsOpen U) (hV : IsOpen V)
    (hf : HasUniformJetBoundsOn n U f)
    (hg : HasUniformJetBoundsOn n K (fun _ : Unit => g))
    (hcf : ∀ i, ContDiffOn ℝ (n : ℕ∞) (f i) U)
    (hcg : ContDiffOn ℝ (n : ℕ∞) g V)
    (hK : ∀ i, MapsTo (f i) U K) (hKV : K ⊆ V) :
    HasUniformJetBoundsOn n U (fun i => g ∘ f i) := by
  intro m hm
  obtain ⟨Af, hAf, hAf'⟩ := HasUniformJetBoundsOn.bound_all hf hm
  obtain ⟨Ag, hAg, hAg'⟩ := HasUniformJetBoundsOn.bound_all hg hm
  let D : ℝ := max Af 1
  refine ⟨Nat.factorial m * Ag * D ^ m, fun i x hx => ?_⟩
  have H := norm_iteratedFDerivWithin_comp_le hcg (hcf i)
    (by exact_mod_cast hm) hV.uniqueDiffOn hU.uniqueDiffOn
    (fun y hy => hKV (hK i hy)) hx (C := Ag) (D := D) ?_ ?_
  · simpa only [iteratedFDerivWithin_of_isOpen m hU hx] using H
  · intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hV (hKV (hK i hx))]
    exact hAg' j hj () (f i x) (hK i hx)
  · intro j hj₁ hj
    rw [iteratedFDerivWithin_of_isOpen j hU hx]
    exact (hAf' j hj i x hx).trans (le_pow_of_le_max_one rfl hj₁)



theorem norm_iteratedFDeriv_comp_le_of_contDiffAt {n : ℕ} {f : E → F}
    {g : F → G} {x : E} {C D : ℝ}
    (hg : ContDiffAt ℝ n g (f x)) (hf : ContDiffAt ℝ n f x)
    (hC : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (hD : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f x‖ ≤ D ^ j) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ Nat.factorial n * C * D ^ n := by
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨V, hVt, hV, hfxV⟩ := mem_nhds_iff.mp ht
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := n) le_rfl (by simp)
  have hsV : s ∩ f ⁻¹' V ∈ 𝓝 x :=
    inter_mem hs (hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hfxV))
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.mp hsV
  have hUV : MapsTo f U V := fun y hy => (hUs hy).2
  have H := norm_iteratedFDerivWithin_comp_le (hgt.mono hVt)
    (hfs.mono (hUs.trans inter_subset_left)) (le_refl (n : ℕ∞ω))
    hV.uniqueDiffOn hU.uniqueDiffOn hUV hxU (C := C) (D := D) ?_ ?_
  · rwa [iteratedFDerivWithin_of_isOpen n hU hxU] at H
  · intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hV hfxV]
    exact hC j hj
  · intro j hj₁ hj
    rw [iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hD j hj₁ hj



theorem HasUniformJetBoundsOn.comp_fixed_at {n : ℕ} {U : Set E} {K : Set F}
    {f : ι → E → F} {g : F → G} (hU : IsOpen U)
    (hf : HasUniformJetBoundsOn n U f) (hK : IsCompact K)
    (hcf : ∀ i, ContDiffOn ℝ n (f i) U)
    (hcg : ∀ y ∈ K, ContDiffAt ℝ n g y)
    (hmap : ∀ i, MapsTo (f i) U K) :
    HasUniformJetBoundsOn n U (fun i => g ∘ f i) := by
  have hg : HasUniformJetBoundsOn n K (fun _ : Unit => g) := by
    intro j hj
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (fun y hy => ((hcg y hy).continuousAt_iteratedFDeriv
        (by exact_mod_cast hj)).continuousWithinAt)
    exact ⟨C, fun _ y hy => hC y hy⟩
  intro m hm
  obtain ⟨Af, hAf, hAf'⟩ := HasUniformJetBoundsOn.bound_all hf hm
  obtain ⟨Ag, hAg, hAg'⟩ := HasUniformJetBoundsOn.bound_all hg hm
  refine ⟨Nat.factorial m * Ag * (max Af 1) ^ m, fun i x hx => ?_⟩
  apply norm_iteratedFDeriv_comp_le_of_contDiffAt
    ((hcg (f i x) (hmap i hx)).of_le (by exact_mod_cast hm))
    (((hcf i).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hm))
  · intro j hj
    exact hAg' j hj () (f i x) (hmap i hx)
  · intro j hj₁ hj
    exact (hAf' j hj i x hx).trans (le_pow_of_le_max_one rfl hj₁)

theorem HasUniformJetBoundsOn.congr_of_eventuallyEq {n : ℕ} {s : Set E}
    {f g : ι → E → F} (hs : IsOpen s) (hfg : ∀ i x, x ∈ s → f i x = g i x) :
    HasUniformJetBoundsOn n s f ↔ HasUniformJetBoundsOn n s g := by
  constructor <;> intro h m hm <;> obtain ⟨C, hC⟩ := h m hm <;> refine ⟨C, fun i x hx => ?_⟩
  · have heq : f i =ᶠ[𝓝 x] g i := Filter.Eventually.mono (hs.mem_nhds hx) (fun y hy => hfg i y hy)
    rw [← (heq.iteratedFDeriv ℝ m).self_of_nhds]
    exact hC i x hx
  · have heq : g i =ᶠ[𝓝 x] f i := Filter.Eventually.mono (hs.mem_nhds hx) (fun y hy => (hfg i y hy).symm)
    rw [← (heq.iteratedFDeriv ℝ m).self_of_nhds]
    exact hC i x hx

theorem HasUniformJetBounds.succ_of_fderiv {n : ℕ} {f : ι → E → F}
    (h0 : ∃ C : ℝ, ∀ i x, ‖f i x‖ ≤ C)
    (h : HasUniformJetBounds n (fun i => fderiv ℝ (f i))) :
    HasUniformJetBounds (n + 1) f := by
  intro m hm
  rcases m with _ | m
  · obtain ⟨C, hC⟩ := h0
    exact ⟨C, fun i x => by rw [norm_iteratedFDeriv_zero]; exact hC i x⟩
  · obtain ⟨C, hC⟩ := h m (Nat.le_of_succ_le_succ hm)
    refine ⟨C, fun i x => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv]
    exact hC i x

theorem HasUniformJetBoundsOn.succ_of_fderiv {n : ℕ} {s : Set E} {f : ι → E → F}
    (h0 : ∃ C : ℝ, ∀ i x, x ∈ s → ‖f i x‖ ≤ C)
    (h : HasUniformJetBoundsOn n s (fun i => fderiv ℝ (f i))) :
    HasUniformJetBoundsOn (n + 1) s f := by
  intro m hm
  rcases m with _ | m
  · obtain ⟨C, hC⟩ := h0
    exact ⟨C, fun i x hx => by rw [norm_iteratedFDeriv_zero]; exact hC i x hx⟩
  · obtain ⟨C, hC⟩ := h m (Nat.le_of_succ_le_succ hm)
    refine ⟨C, fun i x hx => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv]
    exact hC i x hx



theorem HasUniformJetBoundsOn.fderiv {n : ℕ} {s : Set E} {f : ι → E → F}
    (h : HasUniformJetBoundsOn (n + 1) s f) :
    HasUniformJetBoundsOn n s (fun i => fderiv ℝ (f i)) := by
  intro m hm
  obtain ⟨C, hC⟩ := h (m + 1) (Nat.add_le_add_right hm 1)
  refine ⟨C, fun i x hx => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact hC i x hx

end PoincareConjecture.CoordinateTransition
