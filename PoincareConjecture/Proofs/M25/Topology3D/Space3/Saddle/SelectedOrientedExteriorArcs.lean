import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CircleAngularGeometry

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_selected_oriented_exterior_arcs
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (label : Fin 2 ≃ Fin 2) (a v : Fin 2 → ℝ)
    (ends : Fin 2 × Fin 2 ≃ Fin 4) (eta : ℝ)
    (p : Fin 4 → UnitTwoSphere) (Dc V La : Set UnitTwoSphere) :
    let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
      q (label k) (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
    (∀ k : Fin 2,
      0 < |v k| ∧ |v k| < 2 * Real.pi ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (alpha k) ∧
      (∀ t : ℝ, Function.Injective
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (alpha k) t)) ∧
      Set.InjOn (alpha k) (Icc (-eta) (1 + eta)) ∧
      alpha k 0 = p (ends (k, 0)) ∧
      alpha k 1 = p (ends (k, 1)) ∧
      Disjoint (alpha k '' Ioo (0 : ℝ) 1) Dc ∧
      (alpha k '' Icc (0 : ℝ) 1) ∩ Dc =
        {p (ends (k, 0)), p (ends (k, 1))} ∧
      (∀ s ∈ Ioo (-eta) (0 : ℝ), alpha k s ∈ V) ∧
      (∀ s ∈ Ioo (1 : ℝ) (1 + eta), alpha k s ∈ V)) →
    Disjoint (alpha 0 '' Icc (-eta) (1 + eta))
      (alpha 1 '' Icc (-eta) (1 + eta)) →
    La \ V = ⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1 →
    (∀ k : Fin 2,
      ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) =
        {finProdFinEquiv (k, (0 : Fin 2)), finProdFinEquiv (k, (1 : Fin 2))}) →
    ∃ (aNew vNew : Fin 2 → ℝ),
    let beta : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
      q (label k)
        (complexUnitCircleHomeomorph (Circle.exp (aNew k + vNew k * t)))
    (∀ k : Fin 2,
      aNew k = if ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2))
        then a k else a k + v k) ∧
    (∀ k : Fin 2,
      vNew k = if ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2))
        then v k else -v k) ∧
    (∀ (k : Fin 2) (t : ℝ),
      beta k t = if ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2))
        then alpha k t else alpha k (1 - t)) ∧
    (∀ k : Fin 2,
      beta k '' Icc (0 : ℝ) 1 = alpha k '' Icc (0 : ℝ) 1 ∧
      beta k '' Ioo (0 : ℝ) 1 = alpha k '' Ioo (0 : ℝ) 1 ∧
      beta k '' Icc (-eta) (1 + eta) = alpha k '' Icc (-eta) (1 + eta)) ∧
    (∀ k : Fin 2,
      0 < |vNew k| ∧ |vNew k| < 2 * Real.pi ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (beta k) ∧
      (∀ t : ℝ, Function.Injective
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (beta k) t)) ∧
      Set.InjOn (beta k) (Icc (-eta) (1 + eta)) ∧
      beta k 0 = p (finProdFinEquiv (k, (0 : Fin 2))) ∧
      beta k 1 = p (finProdFinEquiv (k, (1 : Fin 2))) ∧
      Disjoint (beta k '' Ioo (0 : ℝ) 1) Dc ∧
      (beta k '' Icc (0 : ℝ) 1) ∩ Dc =
        {p (finProdFinEquiv (k, (0 : Fin 2))),
          p (finProdFinEquiv (k, (1 : Fin 2)))} ∧
      (∀ s ∈ Ioo (-eta) (0 : ℝ), beta k s ∈ V) ∧
      (∀ s ∈ Ioo (1 : ℝ) (1 + eta), beta k s ∈ V)) ∧
    Disjoint (beta 0 '' Icc (-eta) (1 + eta))
      (beta 1 '' Icc (-eta) (1 + eta)) ∧
    La \ V = ⋃ k : Fin 2, beta k '' Icc (0 : ℝ) 1 := by
  classical
  intro alpha harcs hdis hcover hpairs
  let aNew : Fin 2 → ℝ := fun k =>
    if ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2)) then a k else a k + v k
  let vNew : Fin 2 → ℝ := fun k =>
    if ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2)) then v k else -v k
  refine ⟨aNew, vNew, ?_⟩
  intro beta
  let rev : ℝ → ℝ := fun t => 1 - t
  have hrevrev (t : ℝ) : rev (rev t) = t := by dsimp [rev]; ring
  have hrevInj : Injective rev := by
    intro t s h
    have := congrArg rev h
    simpa only [hrevrev] using this
  have hrevSmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ rev :=
    (contDiff_const.sub contDiff_id).contMDiff
  have hrevImm (t : ℝ) : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) rev t) := by
    have heq : rev ∘ rev = id := funext hrevrev
    have hchain := mfderiv_comp t
      (hrevSmooth.mdifferentiable (by simp) (rev t))
      (hrevSmooth.mdifferentiable (by simp) t)
    rw [heq, mfderiv_id] at hchain
    intro x y hxy
    have hx := congrArg (fun F : ℝ →L[ℝ] ℝ => F x) hchain
    have hy := congrArg (fun F : ℝ →L[ℝ] ℝ => F y) hchain
    change x = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) rev (rev t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) rev t x) at hx
    change y = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) rev (rev t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) rev t y) at hy
    exact hx.trans ((congrArg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) rev (rev t)) hxy).trans hy.symm)
  have hIcc (t : ℝ) : t ∈ Icc (0 : ℝ) 1 ↔ rev t ∈ Icc (0 : ℝ) 1 := by
    dsimp [rev]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
  have hIoo (t : ℝ) : t ∈ Ioo (0 : ℝ) 1 ↔ rev t ∈ Ioo (0 : ℝ) 1 := by
    dsimp [rev]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
  have hBuffer (t : ℝ) : t ∈ Icc (-eta) (1 + eta) ↔
      rev t ∈ Icc (-eta) (1 + eta) := by
    dsimp [rev]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
  have hrevImage (k : Fin 2) (A : Set ℝ) (hA : ∀ t, t ∈ A ↔ rev t ∈ A) :
      (alpha k ∘ rev) '' A = alpha k '' A := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨rev t, (hA t).mp ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨rev t, (hA t).mp ht, ?_⟩
      simp only [comp_apply, hrevrev]
  have hbeta (k : Fin 2) (t : ℝ) :
      beta k t = if ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2))
        then alpha k t else alpha k (1 - t) := by
    by_cases hk : ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2))
    · simp only [beta, aNew, vNew, hk, ite_true, alpha]
    · simp only [beta, aNew, vNew, hk, ite_false, alpha]
      congr 1
      congr 1
      congr 1
      ring
  have hsame (k : Fin 2) (hk : ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2))) :
      beta k = alpha k := by
    funext t
    simpa only [hk, ite_true] using hbeta k t
  have hreverse (k : Fin 2) (hk : ends (k, 0) ≠ finProdFinEquiv (k, (0 : Fin 2))) :
      beta k = alpha k ∘ rev := by
    funext t
    simpa only [hk, ite_false, comp_apply, rev] using hbeta k t
  have himages (k : Fin 2) :
      beta k '' Icc (0 : ℝ) 1 = alpha k '' Icc (0 : ℝ) 1 ∧
      beta k '' Ioo (0 : ℝ) 1 = alpha k '' Ioo (0 : ℝ) 1 ∧
      beta k '' Icc (-eta) (1 + eta) = alpha k '' Icc (-eta) (1 + eta) := by
    by_cases hk : ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2))
    · rw [hsame k hk]
      exact ⟨rfl, rfl, rfl⟩
    · rw [hreverse k hk]
      exact ⟨hrevImage k _ hIcc, hrevImage k _ hIoo, hrevImage k _ hBuffer⟩
  refine ⟨fun _ => rfl, fun _ => rfl, hbeta, himages, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : ends (k, 0) = finProdFinEquiv (k, (0 : Fin 2))
    · have hlast : ends (k, 1) = finProdFinEquiv (k, (1 : Fin 2)) := by
        rcases Set.pair_eq_pair_iff.mp (hpairs k) with h | h
        · exact h.2
        · have he := congrArg Prod.snd (finProdFinEquiv.injective (hk.symm.trans h.1))
          simp at he
      have hv : vNew k = v k := by simp only [vNew, hk, ite_true]
      rw [hv, hsame k hk]
      simpa only [hk, hlast] using harcs k
    · have he : ends (k, 0) = finProdFinEquiv (k, (1 : Fin 2)) ∧
          ends (k, 1) = finProdFinEquiv (k, (0 : Fin 2)) := by
        rcases Set.pair_eq_pair_iff.mp (hpairs k) with h | h
        · exact (hk h.1).elim
        · exact h
      rcases harcs k with ⟨hvp, hvl, hsmooth, himm, hinj, h0, h1, havoid,
        hmeet, hleft, hright⟩
      have hv : |vNew k| = |v k| := by simp only [vNew, hk, ite_false, abs_neg]
      refine ⟨by simpa only [hv] using hvp, by simpa only [hv] using hvl,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hreverse k hk]
        exact hsmooth.comp hrevSmooth
      · intro t
        rw [hreverse k hk, mfderiv_comp t
          (hsmooth.mdifferentiable (by simp) (rev t))
          (hrevSmooth.mdifferentiable (by simp) t)]
        exact (himm (rev t)).comp (hrevImm t)
      · intro t ht s hs hts
        apply hrevInj
        apply hinj ((hBuffer t).mp ht) ((hBuffer s).mp hs)
        simpa only [hreverse k hk, comp_apply] using hts
      · calc
          beta k 0 = alpha k 1 := by simp only [hreverse k hk, comp_apply, rev, sub_zero]
          _ = p (finProdFinEquiv (k, (0 : Fin 2))) := h1.trans (congrArg p he.2)
      · calc
          beta k 1 = alpha k 0 := by simp only [hreverse k hk, comp_apply, rev, sub_self]
          _ = p (finProdFinEquiv (k, (1 : Fin 2))) := h0.trans (congrArg p he.1)
      · rw [(himages k).2.1]
        exact havoid
      · rw [(himages k).1, hmeet, he.1, he.2, Set.pair_comm]
      · intro s hs
        have hmem : rev s ∈ Ioo (1 : ℝ) (1 + eta) := by
          dsimp [rev]
          constructor <;> linarith [hs.1, hs.2]
        simpa only [hreverse k hk, comp_apply] using hright (rev s) hmem
      · intro s hs
        have hmem : rev s ∈ Ioo (-eta) (0 : ℝ) := by
          dsimp [rev]
          constructor <;> linarith [hs.1, hs.2]
        simpa only [hreverse k hk, comp_apply] using hleft (rev s) hmem
  · rw [(himages 0).2.2, (himages 1).2.2]
    exact hdis
  · rw [hcover]
    exact iUnion_congr fun k => (himages k).1.symm

end PoincareConjecture.M25.Topology3D
