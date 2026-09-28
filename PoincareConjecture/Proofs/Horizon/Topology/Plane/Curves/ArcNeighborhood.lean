import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.LocalStraightening
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

theorem exists_two_sided_arc_neighborhood_with_boundary
    {f : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hinj : InjOn f (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hsmooth : ContDiffAt ℝ ∞ f t) (hregular : deriv f t ≠ 0)
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : s ∈ 𝓝 (f t)) :
    ∃ W U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen W ∧ f t ∈ W ∧ W ⊆ s ∧
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Disjoint U V ∧ W \ (f '' Icc (0 : ℝ) 1) = U ∪ V ∧
      f t ∈ closure U ∩ closure V ∧
      ∀ q ∈ W, q ∈ f '' Icc (0 : ℝ) 1 → q ∈ closure U ∩ closure V := by
  obtain ⟨w, _, _, F, hsource, hformula, _, _⟩ :=
    exists_local_straightening hsmooth hregular
  have haxis (u : ℝ) : F (u, 0) = f u := by simp [hformula]
  let J := (fun u : ℝ => (u, (0 : ℝ))) ⁻¹' F.source ∩ Ioo (0 : ℝ) 1
  have hJopen : IsOpen J :=
    (F.open_source.preimage (continuous_id.prodMk continuous_const)).inter isOpen_Ioo
  have htJ : t ∈ J := ⟨hsource, ht⟩
  let K := f '' (Icc (0 : ℝ) 1 \ J)
  have hKcompact : IsCompact K :=
    (isCompact_Icc.diff hJopen).image_of_continuousOn (hf.mono sdiff_subset)
  have hnotK : f t ∉ K := by
    rintro ⟨u, hu, heq⟩
    have hut : u = t := hinj hu.1 ⟨ht.1.le, ht.2.le⟩ heq
    exact hu.2 (hut ▸ htJ)
  have hnbhd : (F.source ∩ F ⁻¹' (Kᶜ ∩ s)) ∩
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∈ 𝓝 (t, (0 : ℝ)) := by
    refine Filter.inter_mem (Filter.inter_mem (F.open_source.mem_nhds hsource) ?_) ?_
    · apply (F.continuousAt hsource).preimage_mem_nhds
      rw [haxis]
      exact Filter.inter_mem (hKcompact.isClosed.isOpen_compl.mem_nhds hnotK) hs
    · exact (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hnbhd
  obtain ⟨a, b, hab, ha⟩ := mem_nhds_iff_exists_Ioo_subset.mp hA
  obtain ⟨c, d, hcd, hc⟩ := mem_nhds_iff_exists_Ioo_subset.mp hB
  let box := Ioo a b ×ˢ Ioo c d
  have hbox (q : ℝ × ℝ) (hq : q ∈ box) := hAB ⟨ha hq.1, hc hq.2⟩
  have hbox_source : box ⊆ F.source := fun q hq => (hbox q hq).1.1
  have hbox_ambient : F '' box ⊆ s := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hbox q hq).1.2.2

  have harc (q : ℝ × ℝ) (hq : q ∈ box) :
      F q ∈ f '' Icc (0 : ℝ) 1 ↔ q.2 = 0 := by
    constructor
    · rintro ⟨u, hu, heq⟩
      have huJ : u ∈ J := by
        by_contra h
        exact (hbox q hq).1.2.1 ⟨u, ⟨hu, h⟩, heq⟩
      have hqu : q = (u, 0) :=
        F.injOn (hbox_source hq) huJ.1 (by rw [haxis]; exact heq.symm)
      exact congrArg Prod.snd hqu
    · intro hzero
      refine ⟨q.1, ⟨(hbox q hq).2.1.1.le, (hbox q hq).2.1.2.le⟩, ?_⟩
      simp [hformula, hzero]
  let lower := Ioo a b ×ˢ Ioo c 0
  let upper := Ioo a b ×ˢ Ioo 0 d
  have hlower : lower ⊆ box := by
    intro q hq
    exact ⟨hq.1, hq.2.1, lt_trans hq.2.2 hcd.2⟩
  have hupper : upper ⊆ box := by
    intro q hq
    exact ⟨hq.1, lt_trans hcd.1 hq.2.1, hq.2.2⟩
  have hlower_path : IsPathConnected lower :=
    ((convex_Ioo a b).prod (convex_Ioo c 0)).isPathConnected
      ⟨(t, c / 2), hab, by constructor <;> linarith [hcd.1]⟩
  have hupper_path : IsPathConnected upper :=
    ((convex_Ioo a b).prod (convex_Ioo 0 d)).isPathConnected
      ⟨(t, d / 2), hab, by constructor <;> linarith [hcd.2]⟩
  have hdisjoint : Disjoint (F '' lower) (F '' upper) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
    have hpq := F.injOn (hbox_source (hlower hp)) (hbox_source (hupper hq)) heq.symm
    have hsnd := congrArg Prod.snd hpq
    linarith [hp.2.2, hq.2.1]
  have hpartition : (F '' box) \ (f '' Icc (0 : ℝ) 1) =
      (F '' lower) ∪ (F '' upper) := by
    ext y
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hnot⟩
      have hne : q.2 ≠ 0 := (harc q hq).not.mp hnot
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact Or.inl ⟨q, ⟨hq.1, hq.2.1, hneg⟩, rfl⟩
      · exact Or.inr ⟨q, ⟨hq.1, hpos, hq.2.2⟩, rfl⟩
    · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · refine ⟨⟨q, hlower hq, rfl⟩, ?_⟩
        exact fun h => (ne_of_lt hq.2.2) ((harc q (hlower hq)).mp h)
      · refine ⟨⟨q, hupper hq, rfl⟩, ?_⟩
        exact fun h => (ne_of_gt hq.2.1) ((harc q (hupper hq)).mp h)
  have hboundary (q : ℝ × ℝ) (hq : q ∈ box) (hzero : q.2 = 0) :
      F q ∈ closure (F '' lower) ∩ closure (F '' upper) := by
    have hclosure_lower : q ∈ closure lower := by
      rw [closure_prod_eq, closure_Ioo (lt_trans hab.1 hab.2).ne, closure_Ioo hcd.1.ne]
      refine ⟨⟨hq.1.1.le, hq.1.2.le⟩, ?_⟩
      rw [hzero]
      exact ⟨hcd.1.le, le_rfl⟩
    have hclosure_upper : q ∈ closure upper := by
      rw [closure_prod_eq, closure_Ioo (lt_trans hab.1 hab.2).ne, closure_Ioo hcd.2.ne]
      refine ⟨⟨hq.1.1.le, hq.1.2.le⟩, ?_⟩
      rw [hzero]
      exact ⟨le_rfl, hcd.2.le⟩
    exact ⟨(F.continuousAt (hbox_source hq)).continuousWithinAt.mem_closure_image
        hclosure_lower,
      (F.continuousAt (hbox_source hq)).continuousWithinAt.mem_closure_image
        hclosure_upper⟩
  refine ⟨F '' box, F '' lower, F '' upper,
    F.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hbox_source,
    ⟨(t, 0), ⟨hab, hcd⟩, haxis t⟩, hbox_ambient,
    F.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) (hlower.trans hbox_source),
    F.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) (hupper.trans hbox_source),
    hlower_path.image' (F.continuousOn.mono (hlower.trans hbox_source)),
    hupper_path.image' (F.continuousOn.mono (hupper.trans hbox_source)),
    hdisjoint, hpartition, ?_, ?_⟩
  · simpa only [haxis] using hboundary (t, 0) ⟨hab, hcd⟩ rfl
  · rintro z ⟨q, hq, rfl⟩ hz
    exact hboundary q hq ((harc q hq).mp hz)

theorem exists_two_sided_arc_neighborhood
    {f : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hinj : InjOn f (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hsmooth : ContDiffAt ℝ ∞ f t) (hregular : deriv f t ≠ 0)
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : s ∈ 𝓝 (f t)) :
    ∃ W U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen W ∧ f t ∈ W ∧ W ⊆ s ∧
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Disjoint U V ∧ W \ (f '' Icc (0 : ℝ) 1) = U ∪ V ∧
      f t ∈ closure U ∩ closure V := by
  obtain ⟨W, U, V, hW, htW, hWs, hU, hV, hUpath, hVpath, hdisj, hcover, htUV, _⟩ :=
    exists_two_sided_arc_neighborhood_with_boundary hf hinj ht hsmooth hregular hs
  exact ⟨W, U, V, hW, htW, hWs, hU, hV, hUpath, hVpath, hdisj, hcover, htUV⟩

end Poincare.Topology.Plane.Curves
