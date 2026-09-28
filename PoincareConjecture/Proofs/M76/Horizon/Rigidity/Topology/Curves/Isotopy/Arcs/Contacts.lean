import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.Lift
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPaths
import Mathlib.Topology.Order.Compact









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_finite_interval_level_contacts {f : ℝ → ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc 0 1)) (c : ℝ) :
    ∃ J : Finset (ℝ × ℝ),
      (∀ p ∈ J, p.1 ≤ p.2 ∧ Icc p.1 p.2 ⊆ Icc 0 1) ∧
      Icc 0 1 ∩ {t | f t = c} = ⋃ p ∈ J, Icc p.1 p.2 := by
  classical
  obtain ⟨n, t, ht, ht0, ht1, hformula⟩ := hf.exists_interval_partition_four
  choose A hA using hformula
  let D : Fin (n + 3) → Set ℝ := fun i =>
    Icc (t i.castSucc) (t i.succ) ∩ (A i) ⁻¹' {c}
  have hDcompact (i : Fin (n + 3)) : IsCompact (D i) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage (A i).continuous)
  have hDconvex (i : Fin (n + 3)) : Convex ℝ (D i) :=
    (convex_Icc _ _).inter ((convex_singleton c).affine_preimage (A i).toAffineMap)
  let nonempty : Finset (Fin (n + 3)) := Finset.univ.filter fun i => (D i).Nonempty
  let ends : Fin (n + 3) → ℝ × ℝ := fun i => (sInf (D i), sSup (D i))
  have hDinterval (i : Fin (n + 3)) (hi : i ∈ nonempty) :
      D i = Icc (ends i).1 (ends i).2 :=
    eq_Icc_of_connected_compact
      ⟨(Finset.mem_filter.mp hi).2, (hDconvex i).isPreconnected⟩ (hDcompact i)
  have htmem (i : Fin (n + 4)) : t i ∈ Icc 0 1 := by
    constructor
    · rw [← ht0]
      exact ht.monotone (Fin.zero_le i)
    · rw [← ht1]
      exact ht.monotone (Fin.le_last i)
  refine ⟨nonempty.image ends, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hi).2
      exact (hDinterval i hi ▸ hx).1.trans (hDinterval i hi ▸ hx).2
    · rw [← hDinterval i hi]
      exact fun x hx => ⟨(htmem _).1.trans hx.1.1, hx.1.2.trans (htmem _).2⟩
  · apply Subset.antisymm
    · intro x hx
      have hx' : x ∈ Icc (t 0) (t (Fin.last (n + 3))) := by simpa [ht0, ht1] using hx.1
      obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc hx'
      have hxD : x ∈ D i := ⟨hi, (hA i hi).symm.trans hx.2⟩
      have hin : i ∈ nonempty := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxD⟩⟩
      exact mem_iUnion.mpr ⟨ends i, mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨i, hin, rfl⟩, (hDinterval i hin).subset hxD⟩⟩
    · intro x hx
      obtain ⟨p, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hp, hx⟩ := mem_iUnion.mp hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      have hxD := (hDinterval i hi).symm.subset hx
      exact ⟨⟨(htmem _).1.trans hxD.1.1, hxD.1.2.trans (htmem _).2⟩,
        (hA i hxD.1).trans hxD.2⟩

theorem exists_finite_annular_axis_contact_intervals {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (k : ℤ) :
    ∃ J : Finset (ℝ × ℝ),
      (∀ p ∈ J, p.1 ≤ p.2 ∧ Icc p.1 p.2 ⊆ Icc 0 1) ∧
      Icc 0 1 ∩ {t | (r t).1 = 32 * (k : ℝ)} = ⋃ p ∈ J, Icc p.1 p.2 :=
  exists_finite_interval_level_contacts
    (hr.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap) _

theorem finite_annular_axes_met {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) :
    {k : ℤ | ∃ t ∈ Icc (0 : ℝ) 1, (r t).1 = 32 * (k : ℝ)}.Finite := by
  have hcont : ContinuousOn (fun t => (r t).1) (Icc 0 1) :=
    continuous_fst.comp_continuousOn hr.continuousOn
  have hc := isCompact_Icc.image_of_continuousOn hcont
  obtain ⟨lo, hlo⟩ := hc.bddBelow
  obtain ⟨hi, hhi⟩ := hc.bddAbove
  apply (finite_Icc (⌊lo / 32⌋ : ℤ) (⌈hi / 32⌉ : ℤ)).subset
  rintro k ⟨t, ht, htk⟩
  have hl := hlo (mem_image_of_mem (fun t => (r t).1) ht)
  have hu := hhi (mem_image_of_mem (fun t => (r t).1) ht)
  rw [htk] at hl hu
  have hl' := Int.floor_le (lo / 32)
  have hu' := Int.le_ceil (hi / 32)
  constructor
  · have h : ((⌊lo / 32⌋ : ℤ) : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast h
  · have h : (k : ℝ) ≤ ((⌈hi / 32⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast h

theorem exists_finite_annular_axis_contacts {r : ℝ → ℝ × ℝ}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) :
    ∃ (K : Finset ℤ) (J : ℤ → Finset (ℝ × ℝ)),
      (∀ k, k ∈ K ↔ ∃ t ∈ Icc (0 : ℝ) 1, (r t).1 = 32 * (k : ℝ)) ∧
      (∀ k p, p ∈ J k → p.1 ≤ p.2 ∧ Icc p.1 p.2 ⊆ Icc 0 1) ∧
      (∀ k : ℤ, Icc 0 1 ∩ {t | (r t).1 = 32 * (k : ℝ)} = ⋃ p ∈ J k, Icc p.1 p.2) ∧
      ∀ k, k ∉ K → J k = ∅ := by
  classical
  choose J hJ hcontacts using exists_finite_annular_axis_contact_intervals hr
  let K := (finite_annular_axes_met hr).toFinset
  refine ⟨K, J, fun k => (finite_annular_axes_met hr).mem_toFinset,
    hJ, hcontacts, ?_⟩
  intro k hk
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hpl := hJ k p hp
  have hpcontact : p.1 ∈ Icc 0 1 ∩ {t | (r t).1 = 32 * (k : ℝ)} := by
    rw [hcontacts]
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, ⟨le_rfl, hpl.1⟩⟩⟩
  exact hk ((finite_annular_axes_met hr).mem_toFinset.mpr ⟨p.1, hpcontact.1, hpcontact.2⟩)

end PoincareConjecture.M76.Dehn
