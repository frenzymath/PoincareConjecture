import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith













set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Manifold.Schoenflies.Plane



theorem exists_interval_margin {a b : ℝ} (hab : a ≤ b)
    {U : Set ℝ} (hU : IsOpen U) (hK : Icc a b ⊆ U) :
    ∃ m : ℝ, 0 < m ∧ Ioo (a - m) (b + m) ⊆ U := by
  obtain ⟨la, ua, ha, hIa⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds (hK ⟨le_rfl, hab⟩))
  obtain ⟨lb, ub, hb, hIb⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds (hK ⟨hab, le_rfl⟩))
  refine ⟨min (a - la) (ub - b), lt_min (sub_pos.mpr ha.1) (sub_pos.mpr hb.2), ?_⟩
  intro x hx
  have hleft := min_le_left (a - la) (ub - b)
  have hright := min_le_right (a - la) (ub - b)
  by_cases hxa : x < a
  · exact hIa ⟨by linarith [hx.1], hxa.trans ha.2⟩
  · by_cases hbx : b < x
    · exact hIb ⟨hb.1.trans hbx, by linarith [hx.2]⟩
    · exact hK ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]




theorem exists_uniform_zero_section_tube {a b : ℝ} (hab : a ≤ b)
    {U : Set ((ℝ × X) × ℝ)} (hU : IsOpen U)
    (hK : (Icc a b ×ˢ (univ : Set X)) ×ˢ ({0} : Set ℝ) ⊆ U) :
    ∃ m : ℝ, 0 < m ∧ ∃ w : ℝ, 0 < w ∧
      (Ioo (a - m) (b + m) ×ˢ (univ : Set X)) ×ˢ Ioo (-w) w ⊆ U := by
  obtain ⟨A, B, hA, hB, hKA, h0B, hAB⟩ :=
    generalized_tube_lemma (isCompact_Icc.prod isCompact_univ) isCompact_singleton hU hK
  obtain ⟨C, D, hC, _, hIC, hUD, hCD⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_univ hA hKA
  obtain ⟨m, hm, hmC⟩ := exists_interval_margin hab hC hIC
  obtain ⟨w, hw, hwB⟩ := exists_interval_margin (a := 0) (b := 0) le_rfl hB
    (by simpa using h0B)
  refine ⟨m, hm, w, hw, ?_⟩
  rintro ⟨⟨z, q⟩, r⟩ ⟨⟨hz, _⟩, hr⟩
  exact hAB ⟨hCD ⟨hmC hz, hUD trivial⟩, hwB (by simpa using hr)⟩

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]




theorem exists_uniform_injective_family_tube {a b : ℝ} (hab : a ≤ b)
    (F : (ℝ × X) × ℝ → Y)
    (hc : ∀ z ∈ Icc a b, ∀ q : X, ContinuousAt F ((z, q), 0))
    (hi : ∀ z ∈ Icc a b, Function.Injective (fun q : X => F ((z, q), 0)))
    (hloc : ∀ z ∈ Icc a b, ∀ q : X, ∃ W ∈ 𝓝 ((z, q), (0 : ℝ)),
      InjOn (fun p : (ℝ × X) × ℝ => (p.1.1, F p)) W)
    {U : Set ((ℝ × X) × ℝ)} (hU : IsOpen U)
    (hK : (Icc a b ×ˢ (univ : Set X)) ×ˢ ({0} : Set ℝ) ⊆ U) :
    ∃ m : ℝ, 0 < m ∧ ∃ w : ℝ, 0 < w ∧
      (Ioo (a - m) (b + m) ×ˢ (univ : Set X)) ×ˢ Ioo (-w) w ⊆ U ∧
      InjOn (fun p : (ℝ × X) × ℝ => (p.1.1, F p))
        ((Ioo (a - m) (b + m) ×ˢ (univ : Set X)) ×ˢ Ioo (-w) w) := by
  let K : Set ((ℝ × X) × ℝ) := (Icc a b ×ˢ univ) ×ˢ {0}
  let T : (ℝ × X) × ℝ → ℝ × Y := fun p => (p.1.1, F p)
  have hinj : InjOn T K := by
    rintro ⟨⟨z, q⟩, r⟩ ⟨⟨hz, _⟩, hr⟩ ⟨⟨z', q'⟩, r'⟩ ⟨⟨_, _⟩, hr'⟩ heq
    have hr0 : r = 0 := hr
    have hr0' : r' = 0 := hr'
    subst r
    subst r'
    have hzz : z = z' := congrArg Prod.fst heq
    subst z'
    have hqq : q = q' := hi z hz (congrArg Prod.snd heq)
    subst q'
    rfl
  have hcompact : IsCompact K :=
    (isCompact_Icc.prod isCompact_univ).prod isCompact_singleton
  have hcont : ∀ p ∈ K, ContinuousAt T p := by
    rintro ⟨⟨z, q⟩, r⟩ ⟨⟨hz, _⟩, hr⟩
    have hr0 : r = 0 := hr
    subst r
    exact continuous_fst.fst.continuousAt.prodMk (hc z hz q)
  have hlocal : ∀ p ∈ K, ∃ W ∈ 𝓝 p, InjOn T W := by
    rintro ⟨⟨z, q⟩, r⟩ ⟨⟨hz, _⟩, hr⟩
    have hr0 : r = 0 := hr
    subst r
    exact hloc z hz q
  obtain ⟨W, hW, hKW, hinjW⟩ := hinj.exists_isOpen_superset hcompact hcont hlocal
  obtain ⟨m, hm, w, hw, hV⟩ := exists_uniform_zero_section_tube hab (hU.inter hW)
    (subset_inter hK hKW)
  exact ⟨m, hm, w, hw, hV.trans inter_subset_left, hinjW.mono (hV.trans inter_subset_right)⟩

end Poincare.Manifold.Schoenflies.Plane
