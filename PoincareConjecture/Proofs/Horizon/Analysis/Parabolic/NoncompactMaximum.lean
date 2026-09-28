import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.CompactMaximum










set_option autoImplicit false

open Set

namespace Poincare.Parabolic


lemma nonpos_of_deriv_le_mul_at_max_of_nonpos_outside_compact
    {X : Type*} [TopologicalSpace X]
    {F F' : X → ℝ → ℝ} {c a b : ℝ} {K : Set X} (hK : IsCompact K)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hderiv : ∀ q t, t ∈ Ioc a b →
      HasDerivWithinAt (F q) (F' q t) (Icc a b) t)
    (hmax : ∀ q t, t ∈ Ioc a b → 0 < F q t →
      (∀ p, F p t ≤ F q t) → F' q t ≤ c * F q t)
    (hinit : ∀ q, F q a ≤ 0)
    (houtside : ∀ q ∉ K, ∀ t ∈ Icc a b, F q t ≤ 0) :
    ∀ q t, t ∈ Icc a b → F q t ≤ 0 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hrestricted : ContinuousOn
      (fun p : K × ℝ => F p.1 p.2) (univ ×ˢ Icc a b) := by
    apply hF.comp
      (((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn)
    exact fun p hp => ⟨trivial, hp.2⟩
  have hcompare := nonpos_of_deriv_le_mul_at_max
    (F := fun (q : K) t => F q t) (F' := fun (q : K) t => F' q t) hrestricted
    (fun q t ht => hderiv q t ht) (K := c) (fun q t ht hpos hsp => ?_)
    (fun q => hinit q)
  · intro q t ht
    by_cases hq : q ∈ K
    · exact hcompare ⟨q, hq⟩ t ht
    · exact houtside q hq t ht
  · apply hmax q t ht hpos
    intro p
    by_cases hp : p ∈ K
    · exact hsp ⟨p, hp⟩
    · exact (houtside p hp t ⟨ht.1.le, ht.2⟩).trans hpos.le



lemma exists_compact_nonpos_outside_of_barrier
    {X I : Type*} [TopologicalSpace X]
    {h : X → ℝ} (hproper : ∀ r, IsCompact {x | h x ≤ r})
    {u φ : X → I → ℝ} {B ε : ℝ} (hε : 0 < ε)
    (hu : ∀ x t, u x t ≤ B) (hφ : ∀ x t, ε * h x ≤ φ x t) :
    ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, ∀ t, u x t - φ x t ≤ 0 := by
  refine ⟨{x | h x ≤ B / ε}, hproper _, ?_⟩
  intro x hx t
  have hh : B / ε < h x := lt_of_not_ge hx
  have hh' : B < ε * h x := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hh
  linarith [hu x t, hφ x t]

end Poincare.Parabolic
