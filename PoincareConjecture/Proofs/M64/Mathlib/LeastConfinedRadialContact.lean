import PoincareConjecture.Proofs.M64.Mathlib.CompactDistinctLiftFibers
import PoincareConjecture.Proofs.M64.Mathlib.CompactRadialConfinement
import PoincareConjecture.Proofs.M64.Mathlib.RadialEndpointUniqueness

set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace PoincareConjecture

theorem m64_exists_least_noncanonical_confined_ray
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [TopologicalSpace X] [T2Space X]
    {e : E → X} {R B : ℝ} (he : ContinuousOn e (closedBall 0 R))
    {P : Set X} (hP : IsClosed P) {theta : E} (htheta : ‖theta‖ = 1) (hBR : B ≤ R)
    (hlocal : ∀ s ∈ Icc 0 B, ∃ W ∈ 𝓝 (s • theta), InjOn e W)
    (hex : ∃ s ∈ Icc 0 B, ∃ v : E,
      (‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ P) ∧
        e v = e (s • theta) ∧ v ≠ s • theta) :
    ∃ s ∈ Icc 0 B, ∃ v : E,
      (‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ P) ∧
        e v = e (s • theta) ∧ v ≠ s • theta ∧
      ∀ u ∈ Icc 0 B, ∀ w : E,
        (‖w‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • w) ∈ P) →
          e w = e (u • theta) → w ≠ u • theta → s ≤ u := by
  let C : Set E := {v | ‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ P}
  have hC : IsCompact C := m64_isCompact_confined_radial_vectors he hP
  have heC : ContinuousOn e C := he.mono (fun v hv => by
    simpa only [mem_closedBall, dist_zero_right] using hv.1)
  have hc : ContinuousOn (fun s : ℝ => e (s • theta)) (Icc 0 B) := by
    apply he.comp (continuous_id.smul continuous_const).continuousOn
    intro s hs
    change s • theta ∈ closedBall 0 R
    simpa only [mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg hs.1, htheta, mul_one] using hs.2.trans hBR
  have hcompact := m64_isCompact_distinct_lift_fibers isCompact_Icc hC heC hc
    (continuous_id.smul continuous_const).continuousOn (fun _ _ => rfl) hlocal
  have hnonempty : {p : ℝ × E | p.1 ∈ Icc 0 B ∧ p.2 ∈ C ∧
      e p.2 = e (p.1 • theta) ∧ p.2 ≠ p.1 • theta}.Nonempty := by
    obtain ⟨s, hs, v, hv, heq, hne⟩ := hex
    exact ⟨(s, v), hs, hv, heq, hne⟩
  obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn hnonempty continuous_fst.continuousOn
  refine ⟨p.1, hp.1, p.2, hp.2.1, hp.2.2.1, hp.2.2.2, ?_⟩
  intro u hu w hw heq hne
  exact hmin (show (u, w) ∈ {p : ℝ × E | p.1 ∈ Icc 0 B ∧ p.2 ∈ C ∧
    e p.2 = e (p.1 • theta) ∧ p.2 ≠ p.1 • theta} from ⟨hu, hw, heq, hne⟩)

theorem m64_least_confined_contact_has_only_endpoint_contacts
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E → X) {R B s : ℝ} {P : Set X} {theta v : E}
    (hs : s ∈ Icc 0 B) (hv : ‖v‖ ≤ R)
    (hconf : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ P)
    (he : e v = e (s • theta)) (hne : v ≠ s • theta)
    (hi : InjOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 1))
    (hj : InjOn (fun t : ℝ => e (t • theta)) (Icc (0 : ℝ) B))
    (hmin : ∀ u ∈ Icc 0 B, ∀ w : E,
      (‖w‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • w) ∈ P) →
        e w = e (u • theta) → w ≠ u • theta → s ≤ u) :
    0 < s ∧ v ≠ 0 ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc 0 s,
      e (t • v) = e (u • theta) → (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = s) := by
  have hspos : 0 < s := by
    by_contra hn
    have hz : s = 0 := le_antisymm (le_of_not_gt hn) hs.1
    have h01 := hi ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
      (by simpa only [hz, zero_smul, one_smul] using he)
    exact one_ne_zero h01
  have hvne : v ≠ 0 := by
    intro hz
    have h0s := hj (show (0 : ℝ) ∈ Icc 0 B from ⟨le_rfl, hs.1.trans hs.2⟩) hs
      (by simpa only [hz, zero_smul] using he)
    exact hspos.ne' h0s.symm
  refine ⟨hspos, hvne, ?_⟩
  intro t ht u hu hmeet
  have huB : u ∈ Icc 0 B := ⟨hu.1, hu.2.trans hs.2⟩
  rcases hu.1.eq_or_lt with hu0 | hupos
  · have hu0' : u = 0 := hu0.symm
    have ht0 := hi ht ⟨le_rfl, zero_le_one⟩
      (by simpa only [hu0', zero_smul] using hmeet)
    exact Or.inl ⟨ht0, hu0'⟩
  have htpos : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
    have h0u := hj (show (0 : ℝ) ∈ Icc 0 B from ⟨le_rfl, hs.1.trans hs.2⟩) huB
      (by simpa only [ht0, zero_smul] using hmeet)
    exact hupos.ne' h0u.symm
  have hprefix : ‖t • v‖ ≤ R ∧
      ∀ a ∈ Icc (0 : ℝ) 1, e (a • t • v) ∈ P := by
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans (by simpa using hv)
    · intro a ha
      rw [smul_smul]
      exact hconf (a * t) ⟨mul_nonneg ha.1 ht.1, mul_le_one₀ ha.2 ht.1 ht.2⟩
  have hsu := hmin u huB (t • v) hprefix hmeet
    (m64_radial_noncanonical_prefix_ne e hs htpos hupos hi hj he hne)
  have hus : u = s := le_antisymm hu.2 hsu
  have ht1 := hi ht ⟨zero_le_one, le_rfl⟩ (by
    simpa only [one_smul] using hmeet.trans (by simpa only [hus] using he.symm))
  exact Or.inr ⟨ht1, hus⟩

end PoincareConjecture
