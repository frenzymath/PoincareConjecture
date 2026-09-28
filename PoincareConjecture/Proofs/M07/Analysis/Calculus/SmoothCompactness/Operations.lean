import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness
import PoincareConjecture.Proofs.M07.Analysis.Calculus.Diffeomorphism.Perturbation
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem exists_compact_target_of_tendstoUniformlyOn
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [LocallyCompactSpace Y]
    {K : Set X} (hK : IsCompact K) {U : Set Y} (hU : IsOpen U)
    {g : X → Y} (hg : ContinuousOn g K) (hgU : MapsTo g K U)
    {gseq : ℕ → X → Y} (hconv : TendstoUniformlyOn gseq g atTop K) :
    ∃ T : Set Y, IsCompact T ∧ T ⊆ U ∧ ∀ᶠ k in atTop, MapsTo (gseq k) K T := by
  obtain ⟨T, hT, _, hgT, hTU⟩ := exists_compact_closed_between
    (hK.image_of_continuousOn hg) hU (image_subset_iff.mpr hgU)
  obtain ⟨ε, hε, hεT⟩ := (hK.image_of_continuousOn hg).exists_thickening_subset_open
    isOpen_interior hgT
  refine ⟨T, hT, hTU, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ε hε] with k hk x hx
  apply interior_subset (hεT (Metric.mem_thickening_iff.mpr ?_))
  exact ⟨g x, mem_image_of_mem g hx, by simpa only [dist_comm] using hk x hx⟩

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_comp_le_of_contDiffAt
    {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (m : ℕ) {A B : ℝ}
    (hA : ∀ l, l ≤ m → ‖iteratedFDeriv ℝ l g (f x)‖ ≤ A)
    (hB : ∀ l, 1 ≤ l → l ≤ m → ‖iteratedFDeriv ℝ l f x‖ ≤ B ^ l) :
    ‖iteratedFDeriv ℝ m (g ∘ f) x‖ ≤ m.factorial * A * B ^ m := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨s', hs's, hs'o, hxs'⟩ := mem_nhds_iff.mp hs
  obtain ⟨t', ht't, ht'o, hft'⟩ := mem_nhds_iff.mp ht
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp
    (inter_mem (hs'o.mem_nhds hxs') (hf.continuousAt.preimage_mem_nhds (ht'o.mem_nhds hft')))
  have hmap : MapsTo f v t' := fun _ hx => (hv hx).2
  have hb := norm_iteratedFDerivWithin_comp_le (hgt.mono ht't)
    (hfs.mono (fun _ hy => hs's (hv hy).1)) (le_refl (m : ℕ∞ω))
    ht'o.uniqueDiffOn hvo.uniqueDiffOn hmap hxv
    (C := A) (D := B) (fun l hl => ?_) (fun l hl hlm => ?_)
  · simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using hb
  · simpa only [iteratedFDerivWithin_of_isOpen _ ht'o hft'] using hA l hl
  · simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using hB l hl hlm

theorem norm_iteratedFDeriv_smul_le_of_contDiffAt
    {f : E → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y • g y) x‖ ≤
      ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (m - l) g x‖ := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (inter_mem hs ht)
  have h := norm_iteratedFDerivWithin_smul_le
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (m : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using h

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

theorem locallyEventuallyBoundedDerivatives_const
    (hΩ : IsOpen Ω) {f : EuclideanSpace ℝ (Fin d) → F}
    (hf : ContDiffOn ℝ ∞ f Ω) :
    LocallyEventuallyBoundedDerivatives Ω (fun _ : ℕ => f) := by
  intro K hK hKΩ m
  have hc : ContinuousOn (iteratedFDeriv ℝ m f) K := fun x hx =>
    ((hf.contDiffAt (hΩ.mem_nhds (hKΩ hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top)).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨B, Eventually.of_forall (fun _ => hB)⟩

theorem LocallyEventuallyBoundedDerivatives.bound_all
    {f : ℕ → EuclideanSpace ℝ (Fin d) → F}
    (hf : LocallyEventuallyBoundedDerivatives Ω f)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ l, l ≤ m → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ l (f k) x‖ ≤ B := by
  classical
  choose C hC using fun l : Fin (m + 1) => hf K hK hKΩ l
  let B := ∑ l, max (C l) 0
  refine ⟨B, Finset.sum_nonneg (fun l _ => le_max_right _ _), ?_⟩
  filter_upwards [eventually_all.mpr hC] with k hk l hl x hx
  let j : Fin (m + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
  exact (hk j x hx).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun q _ => le_max_right (C q) 0) (Finset.mem_univ j)))

theorem LocallyEventuallyBoundedDerivatives.comp_fixed
    {V : Set (EuclideanSpace ℝ (Fin d))} (hV : IsOpen V)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : LocallyEventuallyBoundedDerivatives Ω f) (hg : ContDiffOn ℝ ∞ g V)
    (hgΩ : MapsTo g V Ω)
    (hlocal : ∀ x ∈ Ω, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W) :
    LocallyEventuallyBoundedDerivatives V (fun k => f k ∘ g) := by
  intro K hK hKV m
  have hKg := hK.image_of_continuousOn (hg.continuousOn.mono hKV)
  have hKgΩ : g '' K ⊆ Ω := image_subset_iff.mpr (fun _ hx => hgΩ (hKV hx))
  obtain ⟨A, _, hA⟩ := hf.bound_all hKg hKgΩ m
  obtain ⟨B, _, hB⟩ := (locallyEventuallyBoundedDerivatives_const hV hg).bound_all hK hKV m
  refine ⟨m.factorial * A * (max B 1) ^ m, ?_⟩
  filter_upwards [hA, hB,
    eventually_contDiffAt_on_compact_of_locally_eventually_smooth hKg hKgΩ hlocal]
    with k hkA hkB hks x hx
  apply norm_iteratedFDeriv_comp_le_of_contDiffAt
    (hg.contDiffAt (hV.mem_nhds (hKV hx))) (hks _ (mem_image_of_mem g hx)) m
    (fun l hl => hkA l hl _ (mem_image_of_mem g hx))
  intro l hl hlm
  exact (hkB l hlm x hx).trans ((le_max_left _ _).trans
    (le_self_pow₀ (le_max_right B 1) (Nat.ne_of_gt hl)))

theorem LocallyEventuallyBoundedDerivatives.comp_univ
    {f : ℕ → EuclideanSpace ℝ (Fin d) → F}
    {g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : LocallyEventuallyBoundedDerivatives univ f)
    (hg : LocallyEventuallyBoundedDerivatives univ g)
    (hsf : ∀ᶠ k in atTop, ContDiff ℝ ∞ (f k))
    (hsg : ∀ᶠ k in atTop, ContDiff ℝ ∞ (g k)) :
    LocallyEventuallyBoundedDerivatives univ (fun k => f k ∘ g k) := by
  intro K hK _ m
  obtain ⟨B, hB0, hB⟩ := hg.bound_all hK (subset_univ K) m
  let C := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B
  obtain ⟨A, _, hA⟩ := hf.bound_all (isCompact_closedBall _ B) (subset_univ C) m
  refine ⟨m.factorial * A * (max B 1) ^ m, ?_⟩
  filter_upwards [hA, hB, hsf, hsg] with k hkA hkB hksf hksg x hx
  have hxC : g k x ∈ C := by
    simpa only [C, Metric.mem_closedBall, dist_zero_right, norm_iteratedFDeriv_zero]
      using hkB 0 (Nat.zero_le m) x hx
  apply norm_iteratedFDeriv_comp_le_of_contDiffAt hksg.contDiffAt hksf.contDiffAt m
    (fun l hl => hkA l hl _ hxC)
  intro l hl hlm
  exact (hkB l hlm x hx).trans ((le_max_left _ _).trans
    (le_self_pow₀ (le_max_right B 1) (Nat.ne_of_gt hl)))

theorem LocallyEventuallyBoundedDerivatives.cutoff_perturbation
    {f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : LocallyEventuallyBoundedDerivatives Ω f)
    (hlocal : ∀ x ∈ Ω, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    LocallyEventuallyBoundedDerivatives univ (fun k x => x + χ x • (f k x - x)) := by
  intro K hK _ m
  let S := K ∩ tsupport χ
  have hS : IsCompact S := hK.inter_right isClosed_closure
  have hSΩ : S ⊆ Ω := fun _ hx => hχΩ hx.2
  obtain ⟨A, hA0, hA⟩ := hf.bound_all hS hSΩ m
  obtain ⟨B, hB0, hB⟩ :=
    (locallyEventuallyBoundedDerivatives_const isOpen_univ
      (contDiff_id.contDiffOn (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) (n := ∞))).bound_all
      hK (subset_univ K) m
  obtain ⟨C, hC0, hC⟩ :=
    (locallyEventuallyBoundedDerivatives_const isOpen_univ hχ.contDiffOn).bound_all
      hS (subset_univ S) m
  let Q := ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) * C * (A + B)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun l _ => by positivity)
  refine ⟨B + Q, ?_⟩
  filter_upwards [hA, hB, hC,
    eventually_contDiffAt_on_compact_of_locally_eventually_smooth hS hSΩ hlocal]
    with k hkA hkB hkC hks x hx
  by_cases hxs : x ∈ tsupport χ
  · have hxS : x ∈ S := ⟨hx, hxs⟩
    have hdiff := hks x hxS
    have hsub (l : ℕ) (hl : l ≤ m) :
        ‖iteratedFDeriv ℝ l (fun y => f k y - y) x‖ ≤ A + B := by
      change ‖iteratedFDeriv ℝ l (f k - id) x‖ ≤ A + B
      rw [iteratedFDeriv_sub_apply (hdiff.of_le (by exact_mod_cast le_top))
        (contDiffAt_id : ContDiffAt ℝ (l : ℕ∞ω) id x)]
      exact (norm_sub_le _ _).trans (add_le_add (hkA l hl x hxS) (hkB l hl x hx))
    have hsmul := norm_iteratedFDeriv_smul_le_of_contDiffAt hχ.contDiffAt
      (hdiff.sub contDiffAt_id) m
    have hsmulQ : ‖iteratedFDeriv ℝ m (fun y => χ y • (f k y - y)) x‖ ≤ Q := by
      refine hsmul.trans (Finset.sum_le_sum fun l hl => ?_)
      have hlm := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hkC l hlm x hxS) (by positivity))
        (hsub (m - l) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    change ‖iteratedFDeriv ℝ m (id + (fun y => χ y • (f k y - y))) x‖ ≤ B + Q
    rw [iteratedFDeriv_add_apply (i := m) (f := id) (g := fun y => χ y • (f k y - y)) contDiffAt_id
      ((hχ.contDiffAt.smul (hdiff.sub contDiffAt_id)).of_le (by exact_mod_cast le_top))]
    exact (norm_add_le _ _).trans (add_le_add (hkB m le_rfl x hx) hsmulQ)
  · have heq : (fun y => y + χ y • (f k y - y)) =ᶠ[𝓝 x] id := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
      simp only [Pi.zero_apply] at hy
      simp [hy]
    rw [(heq.iteratedFDeriv ℝ m).self_of_nhds]
    exact (hkB m le_rfl x hx).trans (le_add_of_nonneg_right hQ)

theorem locally_eventually_smooth_comp_fixed
    {V : Set (EuclideanSpace ℝ (Fin d))} (hV : IsOpen V)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hg : ContDiffOn ℝ ∞ g V) (hgΩ : MapsTo g V Ω)
    (hlocal : ∀ x ∈ Ω, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W) :
    ∀ x ∈ V, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ g) W := by
  intro x hx
  obtain ⟨W, hW, hgxW, hfs⟩ := hlocal (g x) (hgΩ hx)
  have hn := inter_mem (hV.mem_nhds hx)
    ((hg.contDiffAt (hV.mem_nhds hx)).continuousAt.preimage_mem_nhds (hW.mem_nhds hgxW))
  obtain ⟨W', hW', hW'o, hxW'⟩ := mem_nhds_iff.mp hn
  exact ⟨W', hW'o, hxW', hfs.mono fun _ hk =>
    hk.comp (hg.mono (fun _ hy => (hW' hy).1)) (fun _ hy => (hW' hy).2)⟩

theorem LocallyEventuallyBoundedDerivatives.comp
    {V : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {f g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : LocallyEventuallyBoundedDerivatives Ω f)
    (hg : LocallyEventuallyBoundedDerivatives V g)
    (hG : ContinuousOn G V) (hGΩ : MapsTo G V Ω)
    (hconv : ∀ K, IsCompact K → K ⊆ V → TendstoUniformlyOn g G atTop K)
    (hflocal : ∀ x ∈ Ω, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hglocal : ∀ x ∈ V, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (g k) W) :
    LocallyEventuallyBoundedDerivatives V (fun k => f k ∘ g k) := by
  intro K hK hKV m
  obtain ⟨T, hT, hTΩ, hmap⟩ := exists_compact_target_of_tendstoUniformlyOn hK hΩ
    (hG.mono hKV) (hGΩ.mono_left hKV) (hconv K hK hKV)
  obtain ⟨A, _, hA⟩ := hf.bound_all hT hTΩ m
  obtain ⟨B, _, hB⟩ := hg.bound_all hK hKV m
  refine ⟨m.factorial * A * (max B 1) ^ m, ?_⟩
  filter_upwards [hmap, hA, hB,
    eventually_contDiffAt_on_compact_of_locally_eventually_smooth hT hTΩ hflocal,
    eventually_contDiffAt_on_compact_of_locally_eventually_smooth hK hKV hglocal]
    with k hkmap hkA hkB hkf hkg x hx
  apply norm_iteratedFDeriv_comp_le_of_contDiffAt (hkg x hx) (hkf _ (hkmap hx)) m
    (fun l hl => hkA l hl _ (hkmap hx))
  intro l hl hlm
  exact (hkB l hlm x hx).trans ((le_max_left _ _).trans
    (le_self_pow₀ (le_max_right B 1) (Nat.ne_of_gt hl)))

theorem locally_eventually_smooth_comp
    {V : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) (hV : IsOpen V)
    {f g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hG : ContinuousOn G V) (hGΩ : MapsTo G V Ω)
    (hconv : ∀ K, IsCompact K → K ⊆ V → TendstoUniformlyOn g G atTop K)
    (hflocal : ∀ x ∈ Ω, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hglocal : ∀ x ∈ V, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (g k) W) :
    ∀ x ∈ V, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ g k) W := by
  intro x hx
  obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_between isCompact_singleton hV
    (singleton_subset_iff.mpr hx)
  obtain ⟨T, hT, hTΩ, hmap⟩ := exists_compact_target_of_tendstoUniformlyOn hK hΩ
    (hG.mono hKV) (hGΩ.mono_left hKV) (hconv K hK hKV)
  refine ⟨interior K, isOpen_interior, hxK (mem_singleton x), interior_subset.trans hKV, ?_⟩
  filter_upwards [hmap,
    eventually_contDiffAt_on_compact_of_locally_eventually_smooth hT hTΩ hflocal,
    eventually_contDiffAt_on_compact_of_locally_eventually_smooth hK hKV hglocal]
    with k hkmap hkf hkg y hy
  exact ((hkf _ (hkmap (interior_subset hy))).comp y
    (hkg y (interior_subset hy))).contDiffWithinAt

theorem locallyEventuallyBoundedDerivatives_of_tendsto_jets
    (hΩ : IsOpen Ω) {f : ℕ → EuclideanSpace ℝ (Fin d) → F}
    {F₀ : EuclideanSpace ℝ (Fin d) → F} (hF : ContDiffOn ℝ ∞ F₀ Ω)
    (hjet : ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m F₀) atTop K) :
    LocallyEventuallyBoundedDerivatives Ω f := by
  intro K hK hKΩ m
  have hc : ContinuousOn (iteratedFDeriv ℝ m F₀) K := fun x hx =>
    ((hF.contDiffAt (hΩ.mem_nhds (hKΩ hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top)).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨1 + B, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hjet m K hK hKΩ) 1 zero_lt_one]
    with k hk x hx
  have hn : ‖iteratedFDeriv ℝ m (f k) x - iteratedFDeriv ℝ m F₀ x‖ ≤ 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hk x hx).le
  calc
    _ = ‖iteratedFDeriv ℝ m (f k) x - iteratedFDeriv ℝ m F₀ x +
        iteratedFDeriv ℝ m F₀ x‖ := by rw [sub_add_cancel]
    _ ≤ ‖iteratedFDeriv ℝ m (f k) x - iteratedFDeriv ℝ m F₀ x‖ +
        ‖iteratedFDeriv ℝ m F₀ x‖ := norm_add_le _ _
    _ ≤ 1 + B := add_le_add hn (hB x hx)

end Poincare.Analysis.Calculus
