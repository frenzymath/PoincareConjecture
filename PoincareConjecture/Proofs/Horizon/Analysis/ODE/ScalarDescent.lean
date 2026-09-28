import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Filter
open scoped Topology
namespace Poincare.ODE

theorem exists_late_small_decay {q a : ℝ → ℝ} {B : ℝ}
    (hder : ∀ t, 0 ≤ t → HasDerivAt q (-a t) t)
    (hbelow : ∀ t, 0 ≤ t → B ≤ q t)
    {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) :
    ∃ t, T ≤ t ∧ a t < δ := by
  by_contra hn
  have hlarge : ∀ t, T ≤ t → δ ≤ a t := by
    intro t ht
    by_contra ha
    exact hn ⟨t, ht, lt_of_not_ge ha⟩
  let b := T + (q T - B + 1) / δ
  have hb : T < b := by
    dsimp [b]
    have := hbelow T hT
    have : 0 < (q T - B + 1) / δ := div_pos (by linarith) hδ
    linarith
  have hbound := (convex_Ici T).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hder t (hT.trans ht)).continuousAt.continuousWithinAt)
    (fun t ht => (hder t (hT.trans (interior_subset ht))).differentiableAt.differentiableWithinAt)
    (C := -δ) (fun t ht => by
      rw [(hder t (hT.trans (interior_subset ht))).deriv]
      exact neg_le_neg (hlarge t (interior_subset ht)))
    T (show T ≤ T from le_rfl) b (show T ≤ b from hb.le) hb.le
  have hbb := hbelow b (hT.trans hb.le)
  have heq : -δ * (b - T) = -(q T - B + 1) := by
    dsimp [b]
    field_simp [ne_of_gt hδ]
    ring
  rw [heq] at hbound
  linarith

theorem tendsto_of_strict_min_accumulation
    {X : Type*} [TopologicalSpace X] [RegularSpace X]
    {K : Set X} (hK : IsCompact K)
    {f : X → ℝ} (hf : ContinuousOn f K) {p : X} (hpK : p ∈ K)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Ici 0))
    (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hanti : AntitoneOn (f ∘ γ) (Ici 0))
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop)
    (hlim : Tendsto (γ ∘ τ) atTop (𝓝 p))
    (hmin : ∀ᶠ y in 𝓝 p, y ≠ p → f p < f y) :
    Tendsto γ atTop (𝓝 p) := by
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨V, hVp, hVc, hVU⟩ := exists_mem_nhds_isClosed_subset (inter_mem hU hmin)
  have hpV : p ∈ interior V := mem_interior_iff_mem_nhds.mpr hVp
  let Z := K ∩ frontier V
  have hZ : IsCompact Z := hK.inter_right isClosed_frontier
  have hbarrier : ∃ c : ℝ, f p < c ∧ ∀ y ∈ Z, c ≤ f y := by
    by_cases hne : Z.Nonempty
    · obtain ⟨z, hz, hzmin⟩ := hZ.exists_isMinOn hne (hf.mono inter_subset_left)
      refine ⟨f z, ?_, fun y hy => hzmin hy⟩
      exact (hVU (hVc.frontier_subset hz.2)).2
        (by intro heq; exact hz.2.2 (heq ▸ hpV))
    · exact ⟨f p + 1, by linarith, fun y hy => (hne ⟨y, hy⟩).elim⟩
  obtain ⟨c, hpc, hc⟩ := hbarrier
  have hτK : ∀ᶠ i in atTop, (γ ∘ τ) i ∈ K :=
    (hτ.eventually (eventually_ge_atTop 0)).mono fun i hi => hγK _ hi
  have hflim : Tendsto (f ∘ γ ∘ τ) atTop (𝓝 (f p)) :=
    (hf p hpK).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, hτK⟩)
  obtain ⟨i, hi0, hiV, hic⟩ :=
    ((hτ.eventually (eventually_ge_atTop 0)).and
      ((hlim.eventually (isOpen_interior.mem_nhds hpV)).and
        (hflim.eventually (eventually_lt_nhds hpc)))).exists
  apply (eventually_ge_atTop (τ i)).mono
  intro t ht
  have hpath := isPreconnected_Icc.image γ
    (hγ.mono (show Icc (τ i) t ⊆ Ici 0 from fun u hu => hi0.trans hu.1))
  have hpathV : γ '' Icc (τ i) t ⊆ interior V := by
    apply hpath.subset_of_closure_inter_subset isOpen_interior
      ⟨γ (τ i), mem_image_of_mem _ ⟨le_rfl, ht⟩, hiV⟩
    rintro z ⟨hzcl, u, hu, rfl⟩
    by_contra hzV
    have hz : γ u ∈ Z := ⟨hγK u (hi0.trans hu.1),
      ⟨closure_mono interior_subset hzcl, hzV⟩⟩
    have huc := hc _ hz
    have hum := hanti hi0 (hi0.trans hu.1) hu.1
    exact (not_le_of_gt hic) (huc.trans hum)
  exact (hVU (interior_subset (hpathV (mem_image_of_mem _ ⟨ht, le_rfl⟩)))).1

theorem eventually_eq_of_strict_max_accumulation
    {X : Type*} [TopologicalSpace X] [T3Space X] {K : Set X}
    {f : X → ℝ} (hf : ContinuousOn f K) {p : X} (hpK : p ∈ K)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Ici 0))
    (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hanti : AntitoneOn (f ∘ γ) (Ici 0))
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop)
    (hlim : Tendsto (γ ∘ τ) atTop (𝓝 p))
    (hmax : ∀ᶠ y in 𝓝 p, y ≠ p → f y < f p) :
    ∀ᶠ t in atTop, γ t = p := by
  have hτK : ∀ᶠ i in atTop, (γ ∘ τ) i ∈ K :=
    (hτ.eventually (eventually_ge_atTop 0)).mono fun i hi => hγK _ hi
  have hflim : Tendsto (f ∘ γ ∘ τ) atTop (𝓝 (f p)) :=
    (hf p hpK).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, hτK⟩)
  have hbelow (t : ℝ) (ht : 0 ≤ t) : f p ≤ f (γ t) := by
    apply le_of_tendsto hflim
    exact (hτ.eventually (eventually_ge_atTop t)).mono
      (fun i hi => hanti ht (ht.trans hi) hi)
  obtain ⟨i, hi0, himax⟩ :=
    ((hτ.eventually (eventually_ge_atTop 0)).and (hlim.eventually hmax)).exists
  have hi : γ (τ i) = p := by
    by_contra hn
    exact (not_lt_of_ge (hbelow _ hi0)) (himax hn)
  refine (eventually_ge_atTop (τ i)).mono fun t ht => ?_
  by_contra hn
  have hne : {γ t}ᶜ ∈ 𝓝 p := isOpen_compl_singleton.mem_nhds (by simpa using Ne.symm hn)
  obtain ⟨V, hVp, hVc, hVsub⟩ := exists_mem_nhds_isClosed_subset (inter_mem hmax hne)
  have hpV : p ∈ interior V := mem_interior_iff_mem_nhds.mpr hVp
  have hpath := isPreconnected_Icc.image γ
    (hγ.mono (show Icc (τ i) t ⊆ Ici 0 from fun u hu => hi0.trans hu.1))
  have hpathV : γ '' Icc (τ i) t ⊆ interior V := by
    apply hpath.subset_of_closure_inter_subset isOpen_interior
      ⟨γ (τ i), mem_image_of_mem _ ⟨le_rfl, ht⟩, by simpa only [hi] using hpV⟩
    rintro z ⟨hzcl, u, hu, rfl⟩
    by_contra hzV
    have huV : γ u ∈ V := hVc.closure_subset (closure_mono interior_subset hzcl)
    have hup : γ u ≠ p := fun heq => hzV (heq ▸ hpV)
    exact (not_lt_of_ge (hbelow u (hi0.trans hu.1))) ((hVsub huV).1 hup)
  exact (hVsub (interior_subset (hpathV (mem_image_of_mem _ ⟨ht, le_rfl⟩)))).2 rfl

end Poincare.ODE
