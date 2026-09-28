import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.RelativeVelocity







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)




theorem exists_relative_ambient_isotopy_of_interval_isotopy_within
    {a b l l₀ l₁ u₁ u₀ u : Real} (hab : a < b)
    (hll₀ : l ≤ l₀) (hl₀l₁ : l₀ < l₁) (hl₁u₁ : l₁ ≤ u₁)
    (hu₁u₀ : u₁ < u₀) (hu₀u : u₀ ≤ u)
    {U : Set E2} (hU : IsOpen U)
    (f : Real × Real → E2) (hf : ContDiff Real ∞ f)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun s => f (t, s)) (Icc l u))
    (hder : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0)
    (hstationary : ∀ t ∈ Icc a b, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u,
      f (t, s) = f (a, s))
    (htrace : ∀ t ∈ Icc a b, ∀ s ∈ Icc l₁ u₁, f (t, s) ∈ U) :
    ∃ K O : Set E2, IsCompact K ∧ K ⊆ U ∧ IsOpen O ∧
      (fun s => f (a, s)) '' (Icc l l₀ ∪ Icc u₀ u) ⊆ O ∧ Disjoint K O ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Phi a x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧
        (∀ t x, x ∈ O → Phi t x = x) ∧
        ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, Phi t (f (a, s)) = f (t, s) := by
  have hmid : Icc l₁ u₁ ⊆ Icc l u :=
    Icc_subset_Icc (hll₀.trans hl₀l₁.le) (hu₁u₀.le.trans hu₀u)
  have hend : Icc l l₀ ∪ Icc u₀ u ⊆ Icc l u := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨hs.1, hs.2.trans (hl₀l₁.le.trans (hl₁u₁.trans (hu₁u₀.le.trans hu₀u)))⟩
    · exact ⟨(hll₀.trans (hl₀l₁.le.trans (hl₁u₁.trans hu₁u₀.le))).trans hs.1, hs.2⟩
  have hendstationary : Icc l l₀ ∪ Icc u₀ u ⊆ Icc l l₁ ∪ Icc u₁ u := by
    intro s hs
    rcases hs with hs | hs
    · exact Or.inl ⟨hs.1, hs.2.trans hl₀l₁.le⟩
    · exact Or.inr ⟨hu₁u₀.le.trans hs.1, hs.2⟩
  let A := (fun s => f (a, s)) '' (Icc l l₀ ∪ Icc u₀ u)
  have hA : IsCompact A := (isCompact_Icc.union isCompact_Icc).image
    (hf.continuous.comp (continuous_const.prodMk continuous_id))
  let T := f '' (Icc a b ×ˢ Icc l₁ u₁)
  have hT : IsCompact T := (isCompact_Icc.prod isCompact_Icc).image hf.continuous
  have hTA : Disjoint T A := by
    apply disjoint_left.mpr
    rintro x ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩ ⟨v, hv, heq⟩
    have hsame : s = v := hinj t ht (hmid hs) (hend hv)
      (heq.symm.trans (hstationary t ht v (hendstationary hv)).symm)
    subst v
    rcases hv with hv | hv
    · exact (not_le_of_gt hl₀l₁) (hs.1.trans hv.2)
    · exact (not_le_of_gt hu₁u₀) (hv.1.trans hs.2)
  have hTU : T ⊆ U \ A := by
    rintro x hx
    refine ⟨?_, fun hxA => disjoint_left.mp hTA hx hxA⟩
    obtain ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩ := hx
    exact htrace t ht s hs
  obtain ⟨K, hK, hTK, hKU⟩ := exists_compact_between hT (hU.sdiff hA.isClosed) hTU
  obtain ⟨chi, hchi, hchi0, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓡 2) hT.isClosed hTK (n := ⊤)
  obtain ⟨W, hW, hWc, hWon⟩ := exists_velocity_extension_of_interval_isotopy f hf hinj hder
  let V : Real × E2 → E2 := fun p => chi p.2 • W p
  have hV : ContDiff Real ∞ V := (chi.contMDiff.contDiff.comp contDiff_snd).smul hW
  have hVc : HasCompactSupport V := hWc.smul_left (f := fun p : Real × E2 => chi p.2)
  have hzero (t : Real) (x : E2) (hx : x ∉ K) : V (t, x) = 0 := by
    simp only [V, hchi0 x hx, zero_smul]
  have hVon (t : Real) (ht : t ∈ Icc a b) (s : Real) (hs : s ∈ Icc l u) :
      V (t, f (t, s)) = deriv (fun y => f (y, s)) t := by
    change chi (f (t, s)) • W (t, f (t, s)) = _
    rw [hWon t ht s hs]
    by_cases hsmid : s ∈ Icc l₁ u₁
    · rw [hchi.self_of_nhdsSet _ (show f (t, s) ∈ T from ⟨(t, s), ⟨ht, hsmid⟩, rfl⟩),
        one_smul]
    · have hsend : s ∈ Icc l l₁ ∪ Icc u₁ u := by
        by_cases hleft : s ≤ l₁
        · exact Or.inl ⟨hs.1, hleft⟩
        · exact Or.inr ⟨le_of_not_ge (fun hright => hsmid ⟨(lt_of_not_ge hleft).le, hright⟩), hs.2⟩
      have hderzero : deriv (fun y => f (y, s)) t = 0 :=
        ((hasDerivWithinAt_const t (Icc a b) (f (a, s))).congr_of_mem
          (fun y hy => hstationary y hy s hsend) ht).deriv_eq_zero (uniqueDiffOn_Icc hab t ht)
      rw [hderzero, smul_zero]
  obtain ⟨Phi, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support V hV hK hzero
  refine ⟨K, Kᶜ, hK, fun x hx => (hKU hx).1, hK.isClosed.isOpen_compl,
    (fun x hxA hxK => (hKU hxK).2 hxA), disjoint_compl_right, Phi a,
    hi a, hs a, hfix a, (fun t x hx => hfix a t x hx), ?_⟩
  intro t ht s hs
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  have hLip (y : Real) : LipschitzWith L (fun x => V (y, x)) := by
    convert! hL.comp (LipschitzWith.prodMk_left y) using 1
    simp
  have hpath (y : Real) : HasDerivAt (fun z => f (z, s))
      (deriv (fun z => f (z, s)) y) y :=
    ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) y).hasDerivAt
  have heq := ODE_solution_unique hLip
    (HasDerivAt.continuousOn (fun y _ => ho a (f (a, s)) y))
    (fun y _ => (ho a (f (a, s)) y).hasDerivWithinAt)
    (hf.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun y hy => by
      change HasDerivWithinAt (fun z => f (z, s)) (V (y, f (y, s))) (Ici y) y
      rw [hVon y (Ico_subset_Icc_self hy) s hs]
      exact (hpath y).hasDerivWithinAt)
    (hi a (f (a, s)))
  exact heq ht

end Poincare.Manifold.Schoenflies
