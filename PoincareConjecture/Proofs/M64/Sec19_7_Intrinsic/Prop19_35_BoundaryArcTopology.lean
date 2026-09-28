import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanRegion
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_arc_open_in_real_boundary
    {X : Type*} [TopologicalSpace X]
    (hcharts : ∀ x : X, ∃ C : OpenPartialHomeomorph ℝ X, x ∈ C.target)
    {f : ℝ → X} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hinj : InjOn f (Icc a b)) : IsOpen (f '' Ioo a b) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨C, hC⟩ := hcharts (f t)
  have hft : ContinuousAt f t :=
    (hf t (Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hnear : Ioo a b ∩ f ⁻¹' C.target ∈ 𝓝 t :=
    inter_mem (Ioo_mem_nhds ht.1 ht.2) (hft.preimage_mem_nhds (C.open_target.mem_nhds hC))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let u := t - r / 2
  let v := t + r / 2
  have hut : u < t := by dsimp only [u]; linarith
  have htv : t < v := by dsimp only [v]; linarith
  have huv : u < v := hut.trans htv
  have hlocal : Icc u v ⊆ Ioo a b ∩ f ⁻¹' C.target := by
    intro s hs
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp only [u, v] at hs
    constructor <;> linarith [hs.1, hs.2]
  let g : ℝ → ℝ := C.symm ∘ f
  have hg : ContinuousOn g (Icc u v) := C.continuousOn_symm.comp
    (hf.mono (fun s hs => Ioo_subset_Icc_self (hlocal hs).1)) (fun s hs => (hlocal hs).2)
  have hginj : InjOn g (Icc u v) := by
    intro s hs w hw hsw
    apply hinj (Ioo_subset_Icc_self (hlocal hs).1) (Ioo_subset_Icc_self (hlocal hw).1)
    exact C.symm.injOn (hlocal hs).2 (hlocal hw).2 hsw
  have hopen : IsOpen (g '' Ioo u v) := by
    rcases hg.strictMonoOn_of_injOn_Icc' huv.le hginj with hm | hm
    · rw [hg.image_Ioo_of_strictMonoOn huv.le hm]
      exact isOpen_Ioo
    · rw [hg.image_Ioo_of_strictAntiOn huv.le hm]
      exact isOpen_Ioo
  have hsource : g '' Ioo u v ⊆ C.source := by
    rintro _ ⟨s, hs, rfl⟩
    exact C.map_target (hlocal (Ioo_subset_Icc_self hs)).2
  have hneighborhood := (C.isOpen_image_of_subset_source hopen hsource).mem_nhds
    (show f t ∈ C '' (g '' Ioo u v) from
      ⟨g t, ⟨t, ⟨hut, htv⟩, rfl⟩, C.right_inv hC⟩)
  apply mem_of_superset hneighborhood
  rintro _ ⟨z, ⟨s, hs, rfl⟩, rfl⟩
  exact ⟨s, (hlocal (Ioo_subset_Icc_self hs)).1,
    (C.right_inv (hlocal (Ioo_subset_Icc_self hs)).2).symm⟩

theorem m64Intrinsic_arc_regular_closed_in_real_boundary
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (hcharts : ∀ x : X, ∃ C : OpenPartialHomeomorph ℝ X, x ∈ C.target)
    {f : ℝ → X} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hinj : InjOn f (Icc a b)) :
    IsClosed (f '' Icc a b) ∧ closure (interior (f '' Icc a b)) = f '' Icc a b ∧
      frontier (f '' Icc a b) ⊆ {f a, f b} := by
  have hclosed := (isCompact_Icc.image_of_continuousOn hf).isClosed
  have hopen := m64Intrinsic_arc_open_in_real_boundary hcharts hf hinj
  have hdense : closure (f '' Ioo a b) = f '' Icc a b := by
    apply Subset.antisymm (closure_minimal (image_mono Ioo_subset_Icc_self) hclosed)
    have h := (show ContinuousOn f (closure (Ioo a b)) by rwa [closure_Ioo hab.ne]).image_closure
    rwa [closure_Ioo hab.ne] at h
  have hint : f '' Ioo a b ⊆ interior (f '' Icc a b) :=
    interior_maximal (image_mono Ioo_subset_Icc_self) hopen
  refine ⟨hclosed, Subset.antisymm hclosed.closure_interior_subset ?_, ?_⟩
  · simpa only [hdense] using closure_mono hint
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hclosed.frontier_subset hx
    rcases eq_or_lt_of_le ht.1 with h | ha
    · exact Or.inl (congrArg f h.symm)
    rcases eq_or_lt_of_le ht.2 with h | hb
    · exact Or.inr (congrArg f h)
    exact False.elim (hx.2 (hint ⟨t, ⟨ha, hb⟩, rfl⟩))

theorem m64Intrinsic_arc_initial_endpoint_not_interior
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (hcharts : ∀ x : X, ∃ C : OpenPartialHomeomorph ℝ X, x ∈ C.target)
    {f : ℝ → X} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hinj : InjOn f (Icc a b)) :
    f a ∉ interior (f '' Icc a b) := by
  intro haint
  obtain ⟨C, hC⟩ := hcharts (f a)
  have hnear : f ⁻¹' C.target ∈ 𝓝[Icc a b] a :=
    (hf a ⟨le_rfl, hab.le⟩).preimage_mem_nhdsWithin (C.open_target.mem_nhds hC)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  let d := min r (b - a) / 2
  let u := a + d
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdr : d < r := by dsimp only [d]; linarith [min_le_left r (b - a)]
  have hdb : d < b - a := by dsimp only [d]; linarith [min_le_right r (b - a)]
  have hau : a < u := by dsimp only [u]; linarith
  have hub : u < b := by dsimp only [u]; linarith
  have hlocal : Icc a u ⊆ f ⁻¹' C.target := by
    intro t ht
    apply hball
    refine ⟨?_, ht.1, ht.2.trans hub.le⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp only [u] at ht
    constructor <;> linarith [ht.1, ht.2]
  let g : ℝ → ℝ := C.symm ∘ f
  have hg : ContinuousOn g (Icc a u) := C.continuousOn_symm.comp
    (hf.mono (Icc_subset_Icc le_rfl hub.le)) hlocal
  have hginj : InjOn g (Icc a u) := by
    intro s hs t ht hst
    apply hinj (Icc_subset_Icc le_rfl hub.le hs) (Icc_subset_Icc le_rfl hub.le ht)
    exact C.symm.injOn (hlocal hs) (hlocal ht) hst
  have hfar := (isCompact_Icc.image_of_continuousOn
    (hf.mono (Icc_subset_Icc hau.le le_rfl))).isClosed
  have hnotfar : f a ∉ f '' Icc u b := by
    rintro ⟨t, ht, hta⟩
    have heq := hinj ⟨hau.le.trans ht.1, ht.2⟩ ⟨le_rfl, hab.le⟩ hta
    subst t
    exact hau.not_ge ht.1
  let O := interior (f '' Icc a b) ∩ C.target ∩ (f '' Icc u b)ᶜ
  have hO : IsOpen O := (isOpen_interior.inter C.open_target).inter hfar.isOpen_compl
  have haO : f a ∈ O := ⟨⟨haint, hC⟩, hnotfar⟩
  have hsource : O ⊆ C.target := fun _ hx => hx.1.2
  have hopen := C.isOpen_image_symm_of_subset_target hO hsource
  have hgO : g a ∈ C.symm '' O := ⟨f a, haO, rfl⟩
  have hpoints : ∀ z ∈ C.symm '' O, ∃ t ∈ Icc a u, g t = z := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := interior_subset hx.1.1
    have htu : t < u := by
      by_contra! h
      exact hx.2 ⟨t, ⟨h, ht.2⟩, rfl⟩
    exact ⟨t, ⟨ht.1, htu.le⟩, rfl⟩
  rcases hg.strictMonoOn_of_injOn_Icc' hau.le hginj with hm | hm
  · have hsubset : C.symm '' O ⊆ Ici (g a) := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := hpoints z hz
      exact hm.monotoneOn ⟨le_rfl, hau.le⟩ ht ht.1
    have h := interior_mono hsubset (hopen.interior_eq.symm ▸ hgO)
    simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at h
  · have hsubset : C.symm '' O ⊆ Iic (g a) := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := hpoints z hz
      exact hm.antitoneOn ⟨le_rfl, hau.le⟩ ht ht.1
    have h := interior_mono hsubset (hopen.interior_eq.symm ▸ hgO)
    simp only [interior_Iic, mem_Iio, lt_self_iff_false] at h

theorem m64Intrinsic_arc_frontier_eq_endpoints
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (hcharts : ∀ x : X, ∃ C : OpenPartialHomeomorph ℝ X, x ∈ C.target)
    {f : ℝ → X} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hinj : InjOn f (Icc a b)) :
    frontier (f '' Icc a b) = {f a, f b} := by
  have hreg := m64Intrinsic_arc_regular_closed_in_real_boundary hcharts hab hf hinj
  apply Subset.antisymm hreg.2.2
  have ha := m64Intrinsic_arc_initial_endpoint_not_interior hcharts hab hf hinj
  have hreverse : (fun t : ℝ => f (-t)) '' Icc (-b) (-a) = f '' Icc a b := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp only [neg_neg]⟩
  have hmaps : MapsTo (fun t : ℝ => -t) (Icc (-b) (-a)) (Icc a b) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hb := m64Intrinsic_arc_initial_endpoint_not_interior hcharts (neg_lt_neg hab)
    (hf.comp continuous_neg.continuousOn hmaps)
    (hinj.comp neg_injective.injOn hmaps)
  change f (-(-b)) ∉ interior ((fun t : ℝ => f (-t)) '' Icc (-b) (-a)) at hb
  rw [neg_neg, hreverse] at hb
  rintro x (rfl | rfl)
  · exact ⟨subset_closure ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩, ha⟩
  · exact ⟨subset_closure ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, hb⟩

theorem m64Intrinsic_arc_interior_eq_open_side
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (hcharts : ∀ x : X, ∃ C : OpenPartialHomeomorph ℝ X, x ∈ C.target)
    {f : ℝ → X} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hinj : InjOn f (Icc a b)) :
    interior (f '' Icc a b) = f '' Ioo a b := by
  have hfront := m64Intrinsic_arc_frontier_eq_endpoints hcharts hab hf hinj
  apply Subset.antisymm
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := interior_subset hx
    have hta : t ≠ a := by
      intro heq
      have h : f t ∈ frontier (f '' Icc a b) := hfront.symm ▸ Or.inl (congrArg f heq)
      exact h.2 hx
    have htb : t ≠ b := by
      intro heq
      have h : f t ∈ frontier (f '' Icc a b) := hfront.symm ▸ Or.inr (congrArg f heq)
      exact h.2 hx
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩, rfl⟩
  · exact interior_maximal (image_mono Ioo_subset_Icc_self)
      (m64Intrinsic_arc_open_in_real_boundary hcharts hf hinj)

end PoincareConjecture
