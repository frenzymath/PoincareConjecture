import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter Function
open scoped Topology

namespace PoincareConjecture

theorem exists_extend_lift_of_localHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) {c : ℝ → Y} (hc : Continuous c)
    {T : ℝ} (hT : 0 ≤ T) {l : ℝ → X} (hl : ContinuousOn l (Icc 0 T))
    (hproj : EqOn (f ∘ l) c (Icc 0 T)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l' : ℝ → X,
      ContinuousOn l' (Icc 0 (T + δ)) ∧ EqOn l' l (Icc 0 T) ∧
      EqOn (f ∘ l') c (Icc 0 (T + δ)) := by
  classical
  obtain ⟨e, hs, he⟩ := hf (l T)
  have ht : c T ∈ e.target := by
    rw [← hproj ⟨hT, le_rfl⟩, comp_apply, he]
    exact e.map_source hs
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp
    (hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds ht))
  let δ : ℝ := η / 2
  have hδ : 0 < δ := half_pos hη
  have hmaps : MapsTo c (Icc T (T + δ)) e.target := by
    intro t ht'
    apply hsub
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht'.1)]
    dsimp [δ] at ht'
    linarith [ht'.2]
  let l₂ : ℝ → X := e.symm ∘ c
  have hl₂ : ContinuousOn l₂ (Icc T (T + δ)) :=
    e.continuousOn_symm.comp hc.continuousOn hmaps
  have hjoin : l₂ T = l T := by
    change e.symm (c T) = l T
    rw [← hproj ⟨hT, le_rfl⟩, comp_apply, he]
    exact e.left_inv hs
  refine ⟨δ, hδ, (Iic T).piecewise l l₂, ?_, ?_, ?_⟩
  · apply ContinuousOn.piecewise
    · intro t ht'
      have : t = T := by simpa only [frontier_Iic, mem_singleton_iff] using ht'.2
      subst t
      exact hjoin.symm
    · exact hl.mono fun t ht' => ⟨ht'.1.1, by simpa using ht'.2⟩
    · exact hl₂.mono fun t ht' =>
        ⟨by simpa only [compl_Iic, closure_Ioi, mem_Ici] using ht'.2, ht'.1.2⟩
  · intro t ht'
    exact piecewise_eq_of_mem _ _ _ ht'.2
  · intro t ht'
    by_cases htT : t ∈ Iic T
    · simpa only [comp_apply, piecewise_eq_of_mem _ _ _ htT] using hproj ⟨ht'.1, htT⟩
    · simp only [comp_apply, piecewise_eq_of_notMem _ _ _ htT, l₂]
      rw [he]
      exact e.right_inv (hmaps ⟨(lt_of_not_ge htT).le, ht'.2⟩)

theorem exists_lift_of_compact_prefixes
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) {c : ℝ → Y} (hc : Continuous c)
    {q : X} (hq : f q = c 0) {K : Set X} (hK : IsCompact K)
    (htrap : ∀ t ∈ Icc (0 : ℝ) 1, ∀ l : ℝ → X,
      ContinuousOn l (Icc 0 t) → l 0 = q → EqOn (f ∘ l) c (Icc 0 t) → l t ∈ K) :
    ∃ l : ℝ → X, ContinuousOn l (Icc 0 1) ∧ l 0 = q ∧ EqOn (f ∘ l) c (Icc 0 1) := by
  classical
  let A : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧
    ∃ l : ℝ → X, ContinuousOn l (Icc 0 t) ∧ l 0 = q ∧ EqOn (f ∘ l) c (Icc 0 t)}
  have hmono : ∀ t' ∈ A, ∀ t, 0 ≤ t → t ≤ t' → t ∈ A := by
    rintro t' ⟨ht', l, hl, h0, hproj⟩ t ht0 htt'
    exact ⟨⟨ht0, htt'.trans ht'.2⟩, l, hl.mono (Icc_subset_Icc le_rfl htt'), h0,
      hproj.mono (Icc_subset_Icc le_rfl htt')⟩
  have h0A : (0 : ℝ) ∈ A := by
    refine ⟨⟨le_rfl, zero_le_one⟩, fun _ => q, continuousOn_const, rfl, ?_⟩
    intro t ht
    have : t = 0 := le_antisymm ht.2 ht.1
    simpa only [this, comp_apply] using hq
  have hne : A.Nonempty := ⟨0, h0A⟩
  have hbdd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
  let T : ℝ := sSup A
  have hT0 : 0 ≤ T := le_csSup hbdd h0A
  have hT1 : T ≤ 1 := csSup_le hne (fun t ht => ht.1.2)
  have hbefore : ∀ t, 0 ≤ t → t < T → t ∈ A := by
    intro t ht0 htT
    obtain ⟨t', ht'A, htt'⟩ := exists_lt_of_lt_csSup hne htT
    exact hmono t' ht'A t ht0 htt'.le
  have hTA : T ∈ A := by
    rcases eq_or_lt_of_le hT0 with hz | hpos
    · rwa [← hz]
    have hev : ∀ᶠ t in 𝓝[<] T, t ∈ Ico (0 : ℝ) T := by
      filter_upwards [Ioo_mem_nhdsLT hpos] with t ht using ⟨ht.1.le, ht.2⟩
    let x : ℝ → X := fun t =>
      if ht : t ∈ Ico (0 : ℝ) T then (hbefore t ht.1 ht.2).2.choose t else q
    have hx (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
        x t = (hbefore t ht.1 ht.2).2.choose t := dif_pos ht
    have hxproj (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) : f (x t) = c t := by
      rw [hx t ht]
      exact (hbefore t ht.1 ht.2).2.choose_spec.2.2 ⟨ht.1, le_rfl⟩
    have hxK (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) : x t ∈ K := by
      rw [hx t ht]
      have hs := (hbefore t ht.1 ht.2).2.choose_spec
      exact htrap t ⟨ht.1, ht.2.le.trans hT1⟩ _ hs.1 hs.2.1 hs.2.2
    have hmapK : map x (𝓝[<] T) ≤ principal K := by
      rw [le_principal_iff, mem_map]
      filter_upwards [hev] with t ht using hxK t ht
    obtain ⟨r, _, hcl⟩ := hK.exists_clusterPt hmapK
    have hprojlim : Tendsto (fun t => f (x t)) (𝓝[<] T) (𝓝 (c T)) := by
      apply ((hc.tendsto T).mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [hev] with t ht using (hxproj t ht).symm
    have hclmap : ClusterPt (f r) (𝓝 (c T)) :=
      hcl.map hf.continuous.continuousAt (tendsto_map'_iff.mpr hprojlim)
    have hfr : f r = c T := by
      by_contra hne'
      exact hclmap.ne' (disjoint_iff.mp (disjoint_nhds_nhds.mpr hne'))
    obtain ⟨e, hr, he⟩ := hf r
    have htarget : c T ∈ e.target := by rw [← hfr, he]; exact e.map_source hr
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp
      (hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds htarget))
    have hfreq : ∃ᶠ t in 𝓝[<] T, x t ∈ e.source := by
      have h := hcl.frequently (e.open_source.mem_nhds hr)
      exact frequently_map.mp h
    have hclose : ∀ᶠ t in 𝓝[<] T, T - t < η := by
      filter_upwards [Ioo_mem_nhdsLT (show T - η < T by linarith)] with t ht
      linarith [ht.1]
    obtain ⟨t', hsrc, ht', hdist⟩ := (hfreq.and_eventually (hev.and hclose)).exists
    let l₁ : ℝ → X := (hbefore t' ht'.1 ht'.2).2.choose
    have hs₁ := (hbefore t' ht'.1 ht'.2).2.choose_spec
    let l₂ : ℝ → X := e.symm ∘ c
    have hmaps : MapsTo c (Icc t' T) e.target := by
      intro u hu
      apply hηsub
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hu.2)]
      linarith [hu.1]
    have hl₂ : ContinuousOn l₂ (Icc t' T) := e.continuousOn_symm.comp hc.continuousOn hmaps
    have hproj₂ : EqOn (f ∘ l₂) c (Icc t' T) := by
      intro u hu
      change f (e.symm (c u)) = c u
      rw [he]
      exact e.right_inv (hmaps hu)
    have hjoin : l₂ t' = l₁ t' := by
      change e.symm (c t') = l₁ t'
      calc
        e.symm (c t') = x t' := by
          rw [← hxproj t' ht', he]
          exact e.left_inv hsrc
        _ = l₁ t' := hx t' ht'
    refine ⟨⟨hT0, hT1⟩, (Iic t').piecewise l₁ l₂, ?_, ?_, ?_⟩
    · apply ContinuousOn.piecewise
      · intro u hu
        have hut : u = t' := by simpa only [frontier_Iic, mem_singleton_iff] using hu.2
        subst u
        exact hjoin.symm
      · exact hs₁.1.mono fun u hu => ⟨hu.1.1, by simpa only [closure_Iic, mem_Iic] using hu.2⟩
      · exact hl₂.mono fun u hu =>
          ⟨by simpa only [compl_Iic, closure_Ioi, mem_Ici] using hu.2, hu.1.2⟩
    · rw [piecewise_eq_of_mem _ _ _ (show (0 : ℝ) ∈ Iic t' from ht'.1)]
      exact hs₁.2.1
    · intro u hu
      by_cases hut : u ∈ Iic t'
      · simp only [comp_apply, piecewise_eq_of_mem _ _ _ hut]
        exact hs₁.2.2 ⟨hu.1, hut⟩
      · simp only [comp_apply, piecewise_eq_of_notMem _ _ _ hut]
        exact hproj₂ ⟨(lt_of_not_ge hut).le, hu.2⟩
  have hT : T = 1 := by
    rcases eq_or_lt_of_le hT1 with h | h
    · exact h
    exfalso
    obtain ⟨_, l, hl, h0, hproj⟩ := hTA
    obtain ⟨δ, hδ, l', hl', heq, hproj'⟩ :=
      exists_extend_lift_of_localHomeomorph hf hc hT0 hl hproj
    have hnext : T < min (T + δ) 1 := lt_min (by linarith) h
    have hnextA : min (T + δ) 1 ∈ A := by
      refine ⟨⟨hT0.trans hnext.le, min_le_right _ _⟩, l',
        hl'.mono (Icc_subset_Icc le_rfl (min_le_left _ _)), ?_, ?_⟩
      · exact (heq ⟨le_rfl, hT0⟩).trans h0
      · intro t ht
        exact hproj' ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
    exact (not_lt_of_ge (le_csSup hbdd hnextA)) hnext
  obtain ⟨_, l, hl, h0, hproj⟩ := hTA
  rw [hT] at hl hproj
  exact ⟨l, hl, h0, hproj⟩

end PoincareConjecture
