import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Atlas.Construction
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped Topology

universe u

namespace PoincareConjecture.ParabolicRescaling

theorem relative_time_open_iff (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (K L : SpacetimeInterval) :
    IsOpen {s : (parabolicInterval Q hQ a K).domain |
        s.val ∈ (parabolicInterval Q hQ a L).domain} ↔
      IsOpen {t : K.domain | t.val ∈ L.domain} := by
  rw [← (timeHomeomorph Q hQ a K).isOpen_preimage]
  change IsOpen {t : K.domain |
    parabolicTime Q a t.val ∈ (parabolicInterval Q hQ a L).domain} ↔ _
  simp only [parabolicTime_mem_parabolicInterval_iff]

theorem time_cover_iff (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (K : SpacetimeInterval) (B : Type u) (J : B → SpacetimeInterval) :
    (∀ s : (parabolicInterval Q hQ a K).domain,
      ∃ b : B, s.val ∈ (parabolicInterval Q hQ a (J b)).domain) ↔
      ∀ t : K.domain, ∃ b : B, t.val ∈ (J b).domain := by
  constructor
  · intro h t
    obtain ⟨b, hb⟩ := h (timeHomeomorph Q hQ a K t)
    exact ⟨b, (parabolicTime_mem_parabolicInterval_iff Q hQ a (J b) t.val).1 hb⟩
  · intro h s
    obtain ⟨b, hb⟩ := h ((timeHomeomorph Q hQ a K).symm s)
    exact ⟨b, (mem_parabolicInterval_iff Q hQ a (J b) s.val).2 hb⟩

theorem closed_time_iff (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (K : SpacetimeInterval) (b c : ℝ) :
    (parabolicInterval Q hQ a K).domain =
        Set.Icc (parabolicTime Q a b) (parabolicTime Q a c) ↔
      K.domain = Set.Icc b c := by
  change (parabolicTimeOrderIso Q hQ a) '' K.domain =
    Set.Icc ((parabolicTimeOrderIso Q hQ a) b) ((parabolicTimeOrderIso Q hQ a) c) ↔ _
  rw [← (parabolicTimeOrderIso Q hQ a).image_Icc b c]
  exact (Set.image_injective.mpr (parabolicTimeOrderIso Q hQ a).injective).eq_iff

theorem backward_parabolic_time_iff (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (K : SpacetimeInterval) (t r : ℝ) :
    (parabolicInterval Q hQ a K).domain =
        Set.Ioc (parabolicTime Q a t - (Real.sqrt Q * r) ^ 2) (parabolicTime Q a t) ↔
      K.domain = Set.Ioc (t - r ^ 2) t := by
  have hleft : parabolicTime Q a (t - r ^ 2) =
      parabolicTime Q a t - (Real.sqrt Q * r) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQ.le]
    simp only [parabolicTime]
    ring
  rw [← hleft]
  change (parabolicTimeOrderIso Q hQ a) '' K.domain =
    Set.Ioc ((parabolicTimeOrderIso Q hQ a) (t - r ^ 2))
      ((parabolicTimeOrderIso Q hQ a) t) ↔ _
  rw [← (parabolicTimeOrderIso Q hQ a).image_Ioc (t - r ^ 2) t]
  exact (Set.image_injective.mpr (parabolicTimeOrderIso Q hQ a).injective).eq_iff

end PoincareConjecture.ParabolicRescaling
