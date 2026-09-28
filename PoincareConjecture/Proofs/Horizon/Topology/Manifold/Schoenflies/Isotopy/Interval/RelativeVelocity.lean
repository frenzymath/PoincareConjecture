import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)



theorem exists_velocity_extension_of_interval_isotopy
    {a b l u : Real} (f : Real × Real → E2) (hf : ContDiff Real ∞ f)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun s => f (t, s)) (Icc l u))
    (hder : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0) :
    ∃ W : Real × E2 → E2, ContDiff Real ∞ W ∧ HasCompactSupport W ∧
      ∀ t ∈ Icc a b, ∀ s ∈ Icc l u,
        W (t, f (t, s)) = deriv (fun y => f (y, s)) t := by
  let axis : Real → E2 := fun s => WithLp.toLp 2 ![s, 0]
  have haxis : Continuous axis := by
    have h : ContDiff Real ∞ axis := by
      apply (contDiff_piLp 2).mpr
      intro i
      fin_cases i
      · exact contDiff_id
      · exact contDiff_const
    exact h.continuous
  let K := axis '' Icc l u
  have hK : IsCompact K := isCompact_Icc.image haxis
  let G := intervalNormalThickening f
  have hG : ContDiff Real ∞ G := contDiff_intervalNormalThickening hf
  have heq (t s : Real) : G (t, axis s) = f (t, s) := by
    simp [G, intervalNormalThickening, axis]
  have hGinj : ∀ t ∈ Icc a b, InjOn (fun x => G (t, x)) K := by
    intro t ht
    rintro x ⟨s, hs, rfl⟩ y ⟨v, hv, rfl⟩ he
    simp only [heq] at he
    exact congrArg axis (hinj t ht hs hv he)
  have hGder : ∀ t ∈ Icc a b, ∀ x ∈ K,
      Function.Bijective (fderiv Real (fun y => G (t, y)) x) := by
    intro t ht
    rintro x ⟨s, hs, rfl⟩
    exact bijective_fderiv_intervalNormalThickening_zero hf t (axis s) rfl
      (hder t ht s hs)
  obtain ⟨e, he, heagree, _, hei⟩ :=
    exists_spacetime_neighborhood_of_codimZero_isotopy hK G hG hGinj hGder
  obtain ⟨W, hW, hWc, hWon⟩ := exists_velocity_extension_of_compact_isotopy
    hK G hG e he hei (fun t ht x hx => heagree (he ⟨ht, hx⟩))
  refine ⟨W, hW, hWc, fun t ht s hs => ?_⟩
  have hpath : HasDerivAt (fun y => G (y, axis s))
      (fderiv Real G (t, axis s) (1, 0)) t :=
    (hG.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (axis s)))
  simpa only [heq] using
    (hWon t ht (axis s) (mem_image_of_mem axis hs)).trans hpath.deriv.symm

end Poincare.Manifold.Schoenflies
