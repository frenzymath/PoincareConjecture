import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.Normal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Localized

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)

private def intervalAxis (s : Real) : E2 := WithLp.toLp 2 ![s, 0]

private theorem continuous_intervalAxis : Continuous intervalAxis := by
  have h : ContDiff Real ∞ intervalAxis := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_id
    · exact contDiff_const
  exact h.continuous

theorem exists_ambient_isotopy_of_interval_isotopy_within
    {a b l u : Real} {U : Set E2} (hU : IsOpen U)
    (f : Real × Real -> E2) (hf : ContDiff Real ∞ f)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun s => f (t, s)) (Icc l u))
    (hder : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0)
    (htrace : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, f (t, s) ∈ U) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ U ∧
      ∃ Phi : Real -> Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
      (∀ t x, x ∉ K -> Phi t x = x) ∧
      ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, Phi t (f (a, s)) = f (t, s) := by
  let K := intervalAxis '' Icc l u
  have hK : IsCompact K := isCompact_Icc.image continuous_intervalAxis
  have heq (t s : Real) : intervalNormalThickening f (t, intervalAxis s) = f (t, s) := by
    simp [intervalNormalThickening, intervalAxis]
  have hGinj : ∀ t ∈ Icc a b, InjOn (fun x => intervalNormalThickening f (t, x)) K := by
    intro t ht
    rintro x ⟨s, hs, rfl⟩ y ⟨v, hv, rfl⟩ he
    simp only [heq] at he
    exact congrArg intervalAxis (hinj t ht hs hv he)
  have hGder : ∀ t ∈ Icc a b, ∀ x ∈ K,
      Function.Bijective (fderiv Real (fun y => intervalNormalThickening f (t, y)) x) := by
    intro t ht
    rintro x ⟨s, hs, rfl⟩
    exact bijective_fderiv_intervalNormalThickening_zero hf t (intervalAxis s) rfl
      (hder t ht s hs)
  obtain ⟨S, hS, hSU, Phi, hi, hs, hfix, hmotion⟩ :=
    exists_ambient_isotopy_of_codimZero_isotopy_within hK hU
      (intervalNormalThickening f) (contDiff_intervalNormalThickening hf) hGinj hGder (by
        intro t ht
        rintro x ⟨s, hs, rfl⟩
        rw [heq]
        exact htrace t ht s hs)
  refine ⟨S, hS, hSU, Phi, hi, hs, hfix, fun t ht s hs => ?_⟩
  simpa only [heq] using hmotion t ht (intervalAxis s) (mem_image_of_mem intervalAxis hs)

theorem exists_ambient_isotopy_of_interval_isotopy
    {a b l u : Real} (f : Real × Real -> E2) (hf : ContDiff Real ∞ f)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun s => f (t, s)) (Icc l u))
    (hder : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0) :
    ∃ Phi : Real -> Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
      (∃ K : Set E2, IsCompact K ∧ ∀ t x, x ∉ K -> Phi t x = x) ∧
      ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, Phi t (f (a, s)) = f (t, s) := by
  obtain ⟨K, hK, _, Phi, hi, hs, hfix, hmotion⟩ :=
    exists_ambient_isotopy_of_interval_isotopy_within isOpen_univ f hf hinj hder
      (fun _ _ _ _ => mem_univ _)
  exact ⟨Phi, hi, hs, ⟨K, hK, hfix⟩, hmotion⟩

end Poincare.Manifold.Schoenflies
