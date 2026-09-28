import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic










set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M38



theorem cylinder_separator_height_upper_bound
    {S A : Type*} [TopologicalSpace S] [ConnectedSpace S] [TopologicalSpace A]
    (T D : (S × ℝ) ≃ₜ A) (h : A → ℝ) (hproper : IsProperMap h)
    (hT : ∀ p, h (T p) = p.2)
    {l r : ℝ} (hbound : ∀ z, h (D (z, 0)) ∈ Icc l r)
    {C : Set A} (hC : IsPreconnected C)
    (havoid : Disjoint C (range (fun z : S => D (z, 0))))
    {a : A} (ha : a ∈ C) (hal : h a < l) : ∀ b ∈ C, h b ≤ r := by
  classical
  intro b hb
  by_contra hbr
  have hbr' : r < h b := lt_of_not_ge hbr
  let L := T '' (univ ×ˢ Iio l)
  let R := T '' (univ ×ˢ Ioi r)
  have hL : IsPreconnected L :=
    (isPreconnected_univ.prod isPreconnected_Iio).image T T.continuous.continuousOn
  have hR : IsPreconnected R :=
    (isPreconnected_univ.prod isPreconnected_Ioi).image T T.continuous.continuousOn
  have hheight (x : A) : (T.symm x).2 = h x := by
    rw [← hT (T.symm x), T.apply_symm_apply]
  have hmemL (x : A) (hx : h x < l) : x ∈ L :=
    ⟨T.symm x, ⟨mem_univ _, (hheight x).trans_lt hx⟩, T.apply_symm_apply x⟩
  have hmemR (x : A) (hx : r < h x) : x ∈ R :=
    ⟨T.symm x, ⟨mem_univ _, hx.trans_eq (hheight x).symm⟩, T.apply_symm_apply x⟩
  let W := (C ∪ L) ∪ R
  have hW : IsPreconnected W :=
    (hC.union a ha (hmemL a hal) hL).union b (Or.inl hb) (hmemR b hbr') hR
  have hWavoid : Disjoint W (range (fun z : S => D (z, 0))) := by
    apply disjoint_left.mpr
    rintro x ((hx | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) ⟨z, hz⟩
    · exact disjoint_left.mp havoid hx ⟨z, hz⟩
    · have hh : h (T p) < l := (hT p).trans_lt hp.2
      rw [← hz] at hh
      exact hh.not_ge (hbound z).1
    · have hh : r < h (T p) := hp.2.trans_eq (hT p).symm
      rw [← hz] at hh
      exact hh.not_ge (hbound z).2
  let u : A → ℝ := fun x => (D.symm x).2
  have hu : Continuous u := continuous_snd.comp D.symm.continuous
  have hune (x : A) (hx : x ∈ W) : u x ≠ 0 := by
    intro hz
    apply disjoint_left.mp hWavoid hx
    refine ⟨(D.symm x).1, ?_⟩
    have hp : ((D.symm x).1, (0 : ℝ)) = D.symm x := Prod.ext rfl hz.symm
    exact (congrArg D hp).trans (D.apply_symm_apply x)
  have hsign : (∀ x ∈ W, u x < 0) ∨ (∀ x ∈ W, 0 < u x) := by
    have hc := hW.image u hu.continuousOn
    have hs : u '' W ⊆ Iio 0 ∪ Ioi 0 := by
      rintro _ ⟨x, hx, rfl⟩
      exact lt_or_gt_of_ne (hune x hx)
    rcases hc.subset_or_subset isOpen_Iio isOpen_Ioi
        (disjoint_left.mpr fun _ hl hr => lt_asymm hl hr) hs with hn | hp
    · exact Or.inl fun x hx => hn (mem_image_of_mem u hx)
    · exact Or.inr fun x hx => hp (mem_image_of_mem u hx)
  let K := h ⁻¹' Icc l r
  have hK : IsCompact K := hproper.isCompact_preimage isCompact_Icc
  have hout (x : A) (hx : x ∉ W) : x ∈ K := by
    constructor
    · by_contra hh
      exact hx (Or.inl (Or.inr (hmemL x (lt_of_not_ge hh))))
    · by_contra hh
      exact hx (Or.inr (hmemR x (lt_of_not_ge hh)))
  let z : S := Classical.choice inferInstance
  rcases hsign with hn | hp
  · obtain ⟨m, hm⟩ := (hK.image hu).bddAbove
    let x := D (z, max m 0 + 1)
    have hux : u x = max m 0 + 1 := congrArg Prod.snd (D.symm_apply_apply _)
    have hx : x ∉ W := by
      intro hx
      have hh := hn x hx
      rw [hux] at hh
      linarith [le_max_right m 0]
    have hh := hm (mem_image_of_mem u (hout x hx))
    rw [hux] at hh
    linarith [le_max_left m 0]
  · obtain ⟨m, hm⟩ := (hK.image hu).bddBelow
    let x := D (z, min m 0 - 1)
    have hux : u x = min m 0 - 1 := congrArg Prod.snd (D.symm_apply_apply _)
    have hx : x ∉ W := by
      intro hx
      have hh := hp x hx
      rw [hux] at hh
      linarith [min_le_right m 0]
    have hh := hm (mem_image_of_mem u (hout x hx))
    rw [hux] at hh
    linarith [min_le_left m 0]




theorem cylindrical_translates_complement_precompact
    {S A : Type*} [TopologicalSpace S] [ConnectedSpace S] [CompactSpace S]
    [TopologicalSpace A]
    (T D : (S × ℝ) ≃ₜ A) (h : A → ℝ) (hproper : IsProperMap h)
    (hT : ∀ p, h (T p) = p.2)
    (τ : ℤ → A ≃ₜ A) (hτ : ∀ n x, h (τ n x) = h x + n)
    {C : Set A} (hC : IsPreconnected C)
    (havoid : ∀ n, Disjoint C (range (fun z : S => τ n (D (z, 0))))) :
    IsCompact (closure C) := by
  classical
  rcases C.eq_empty_or_nonempty with he | ⟨a, ha⟩
  · simpa only [he, closure_empty] using isCompact_empty
  have hk : IsCompact (range (fun z : S => h (D (z, 0)))) :=
    isCompact_range (hproper.continuous.comp
      (D.continuous.comp (continuous_id.prodMk continuous_const)))
  obtain ⟨l, hl⟩ := hk.bddBelow
  obtain ⟨r, hr⟩ := hk.bddAbove
  have hbound (n : ℤ) (z : S) : h ((D.trans (τ n)) (z, 0)) ∈ Icc (l + n) (r + n) := by
    change h (τ n (D (z, 0))) ∈ Icc (l + n) (r + n)
    rw [hτ]
    constructor <;> linarith [hl (mem_range_self z), hr (mem_range_self z)]
  obtain ⟨n, hn⟩ := exists_int_gt (h a - l)
  obtain ⟨m, hm⟩ := exists_int_lt (h a - r)
  have hupper : ∀ b ∈ C, h b ≤ r + n :=
    cylinder_separator_height_upper_bound T (D.trans (τ n)) h hproper hT
      (hbound n) hC (havoid n) ha (by linarith)
  have hlower : ∀ b ∈ C, l + m ≤ h b := by
    intro b hb
    by_contra hbl
    have hh := cylinder_separator_height_upper_bound T (D.trans (τ m)) h hproper hT
      (hbound m) hC (havoid m) hb (lt_of_not_ge hbl) a ha
    linarith
  have hsub : C ⊆ h ⁻¹' Icc (l + m) (r + n) :=
    fun b hb => ⟨hlower b hb, hupper b hb⟩
  exact (hproper.isCompact_preimage isCompact_Icc).of_isClosed_subset isClosed_closure
    (closure_minimal hsub (isClosed_Icc.preimage hproper.continuous))

end PoincareConjecture.M38
