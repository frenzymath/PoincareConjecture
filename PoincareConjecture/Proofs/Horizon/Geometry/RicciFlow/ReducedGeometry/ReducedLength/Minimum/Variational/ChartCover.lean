import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

open Set Filter Topology

namespace PoincareConjecture.ReducedLengthMinimum

theorem uniform_composition_on_compact_core {X Y : Type*} [MetricSpace X] [UniformSpace Y]
    {a b : ℝ} {K : Set X} (hK : IsCompact K) (B : ℝ × X → Y)
    (hB : ContinuousOn B (Icc a b ×ˢ K))
    (α : ℕ → ℝ → X) (γ : ℝ → X)
    (hαK : ∀ᶠ k in atTop, MapsTo (α k) (Icc a b) K)
    (hγK : MapsTo γ (Icc a b) K)
    (hlim : TendstoUniformlyOn α γ atTop (Icc a b)) :
    TendstoUniformlyOn (fun k s ↦ B (s, α k s)) (fun s ↦ B (s, γ s)) atTop
      (Icc a b) := by
  have hpair : TendstoUniformlyOn (fun k s ↦ (s, α k s)) (fun s ↦ (s, γ s))
      atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim ε hε] with k hk
    intro s hs
    simpa only [dist_prod_same_left] using hk s hs
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually
    (F := fun k s ↦ (s, α k s)) (f := fun s ↦ (s, γ s)) (g := B)
    (t := Icc a b) (s := Icc a b ×ˢ K)
    (hαK.mono (fun k hk s hs ↦ ⟨hs, hk hs⟩))
    (fun s hs ↦ ⟨hs, hγK hs⟩)
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hB) hpair

theorem exists_compact_partition_of_uniform_limit {X ι : Type*}
    [MetricSpace X] [LocallyCompactSpace X] (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {a b : ℝ} (hab : a ≤ b) (γ : ℝ → X) (hγ : Continuous γ)
    (α : ℕ → ℝ → X) (hlim : TendstoUniformlyOn α γ atTop (Icc a b)) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (c : Fin m → ι) (K : Fin m → Set X) (N : ℕ),
      Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      (∀ i, IsCompact (K i) ∧
        γ '' Icc (t i.castSucc) (t i.succ) ⊆ interior (K i) ∧ K i ⊆ U (c i)) ∧
      ∀ k ≥ N, ∀ i, MapsTo (α k) (Icc (t i.castSucc) (t i.succ)) (K i) := by
  classical
  let V : ι → Set (Icc a b) := fun i ↦ (fun s : Icc a b ↦ γ s) ⁻¹' U i
  have hV : ∀ i, IsOpen (V i) := fun i ↦
    (hU i).preimage (hγ.comp continuous_subtype_val)
  have hVcover : univ ⊆ ⋃ i, V i := by
    intro s _
    obtain ⟨i, hi⟩ := hcover (γ s)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨u, hua, humono, ⟨m, hum⟩, hpieces⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab hV hVcover
  let t : Fin (m + 1) → ℝ := fun i ↦ u i
  have htm : Monotone t := fun i j hij ↦ humono hij
  have hta : t 0 = a := hua
  have htb : t (Fin.last m) = b := hum m le_rfl
  choose c hc using fun i : Fin m ↦ hpieces i.1
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc a b := by
    intro s hs
    exact ⟨(u i.1).2.1.trans hs.1, hs.2.trans (u (i.1 + 1)).2.2⟩
  have hsrc (i : Fin m) : γ '' Icc (t i.castSucc) (t i.succ) ⊆ U (c i) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hc i (show (⟨s, hsub i hs⟩ : Icc a b) ∈ Icc (u i.1) (u (i.1 + 1)) from hs)
  have hcompact (i : Fin m) : IsCompact (γ '' Icc (t i.castSucc) (t i.succ)) :=
    isCompact_Icc.image hγ
  choose K hK hγK hKU using fun i ↦ exists_compact_between (hcompact i) (hU (c i)) (hsrc i)
  have htail (i : Fin m) : ∀ᶠ k in atTop,
      MapsTo (α k) (Icc (t i.castSucc) (t i.succ)) (K i) := by
    obtain ⟨δ, hδ, hmargin⟩ := (hcompact i).exists_cthickening_subset_open
      isOpen_interior (hγK i)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with k hk
    intro s hs
    apply interior_subset (hmargin ?_)
    exact Metric.mem_cthickening_of_dist_le _ (γ s) _ _
      (mem_image_of_mem γ hs) (by simpa only [dist_comm] using (hk s (hsub i hs)).le)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Filter.eventually_all.mpr htail)
  exact ⟨m, t, c, K, N, htm, hta, htb, fun i ↦ ⟨hK i, hγK i, hKU i⟩, hN⟩

end PoincareConjecture.ReducedLengthMinimum
