import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.LocalInverse
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Compact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

theorem exists_spacetime_neighborhood_of_codimZero_isotopy
    {a b : Real} {K : Set E} (hK : IsCompact K)
    (G : Real × E -> E) (hG : ContDiff Real ∞ G)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun x => G (t, x)) K)
    (hder : ∀ t ∈ Icc a b, ∀ x ∈ K,
      Function.Bijective (fderiv Real (fun y => G (t, y)) x)) :
    ∃ e : OpenPartialHomeomorph (Real × E) (Real × E),
      Icc a b ×ˢ K ⊆ e.source ∧
      EqOn e (fun z => (z.1, G z)) e.source ∧
      ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, Real × E) ∞ e e.source ∧
      ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, Real × E) ∞ e.symm e.target := by
  let H : Real × E -> Real × E := fun z => (z.1, G z)
  have hH : ContDiff Real ∞ H := contDiff_fst.prodMk hG
  have hHbij (t : Real) (ht : t ∈ Icc a b) (x : E) (hx : x ∈ K) :
      Function.Bijective (fderiv Real H (t, x)) := by
    have hderiv : fderiv Real H (t, x) =
        (ContinuousLinearMap.fst Real Real E).prod (fderiv Real G (t, x)) := by
      change fderiv Real (fun z : Real × E => (z.1, G z)) (t, x) = _
      have h := ((contDiff_fst (𝕜 := Real) (n := ∞)).differentiable (by simp)
        (t, x)).fderiv_prodMk (hG.differentiable (by simp) (t, x))
      rwa [fderiv_fst] at h
    have htime (u : Real × E) : (fderiv Real H (t, x) u).1 = u.1 := by
      rw [hderiv]
      rfl
    have hvertical (v : E) :
        (fderiv Real H (t, x) (0, v)).2 = fderiv Real (fun y => G (t, y)) x v := by
      have h := ((hG.differentiable (by simp) (t, x)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_right t x)).fderiv
      rw [hderiv]
      have hv := congrArg (fun L : E →L[Real] E => L v) h.symm
      change fderiv Real G (t, x) (0, v) = fderiv Real (fun y => G (t, y)) x v at hv
      simpa using hv
    have hi : Function.Injective (fderiv Real H (t, x)) := by
      intro u v huv
      have hfirst : u.1 = v.1 := by
        simpa only [htime] using congrArg Prod.fst huv
      have hzero : fderiv Real H (t, x) (0, u.2 - v.2) = 0 := by
        have he : (0, u.2 - v.2) = u - v := by ext <;> simp [hfirst]
        rw [he, map_sub, huv, sub_self]
      have hsecond : u.2 - v.2 = 0 := (hder t ht x hx).1 (by
        simpa only [hvertical, Prod.snd_zero, map_zero] using congrArg Prod.snd hzero)
      exact Prod.ext hfirst (sub_eq_zero.mp hsecond)
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  have hHinj : InjOn H (Icc a b ×ˢ K) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩ ⟨s, y⟩ ⟨_, hy⟩ heq
    have hts : t = s := congrArg Prod.fst heq
    subst s
    exact Prod.ext rfl (hinj t ht hx hy (congrArg Prod.snd heq))
  obtain ⟨e, he, _, heq, hes, hei⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact (isCompact_Icc.prod hK) hHinj
      (fun z hz => localDiffeomorphAt_of_smooth_bijective_derivative hH
        (hHbij z.1 hz.1 z.2 hz.2))
  exact ⟨e, he, heq, hes, hei⟩

theorem exists_ambient_isotopy_of_codimZero_isotopy
    {a b : Real} {K : Set E} (hK : IsCompact K)
    (G : Real × E -> E) (hG : ContDiff Real ∞ G)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun x => G (t, x)) K)
    (hder : ∀ t ∈ Icc a b, ∀ x ∈ K,
      Function.Bijective (fderiv Real (fun y => G (t, y)) x)) :
    ∃ Phi : Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff Real ∞ (fun p : Real × E => Phi p.1 p.2) ∧
      (∃ S : Set E, IsCompact S ∧ ∀ t x, x ∉ S -> Phi t x = x) ∧
      ∀ t ∈ Icc a b, ∀ x ∈ K, Phi t (G (a, x)) = G (t, x) := by
  obtain ⟨e, he, heq, _, hei⟩ :=
    exists_spacetime_neighborhood_of_codimZero_isotopy hK G hG hinj hder
  exact exists_ambient_isotopy_of_compact_isotopy hK G hG e he hei
    (fun t ht x hx => heq (he ⟨ht, hx⟩))

end Poincare.Manifold.Schoenflies
