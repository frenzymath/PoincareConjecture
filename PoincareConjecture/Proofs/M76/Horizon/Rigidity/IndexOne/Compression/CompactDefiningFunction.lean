import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalRelativeDefiningFunction

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)

variable {X α : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {e : α → OpenPartialHomeomorph X V3} {N : Set X}

theorem exists_compact_domain_signed_defining_function
    (he : PLDomain e N) (hN : IsCompact N) :
    ∃ f : X → ℝ, Continuous f ∧
      (∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target) ∧
      ∀ x, (x ∈ N ↔ 0 ≤ f x) ∧ (x ∈ frontier N ↔ f x = 0) ∧
        (x ∈ interior N ↔ 0 < f x) ∧ (x ∉ N ↔ f x < 0) := by
  obtain ⟨a, U, hU, hNU, hac, ha, _, haneg, hazero, hasign⟩ :=
    OpenPartialHomeomorph.exists_PL_defining_cut_near_compact_with_signs
      e he.compatible he.cover hN (Subset.rfl : N ⊆ N) he.halfspace
  obtain ⟨w, K, V, _, hKU, _, hNV, hwc, hwu, hwone, hwzero, hwPL⟩ :=
    OpenPartialHomeomorph.exists_compactly_supported_PL_core_cutoff
      e he.compatible he.cover hN hU hNU
  let f := fun x => a x + w x - 1
  have hfN (x : X) (hx : x ∈ N) : f x = a x := by simp [f, hwone (hNV hx)]
  have hfneg (x : X) (hx : x ∉ N) : f x < 0 := by
    by_cases hxU : x ∈ U
    · have han : a x < 0 := lt_of_not_ge (fun h => hx ((hasign x hxU).1.mpr h))
      dsimp [f]
      linarith [(hwu x).2]
    · have hw : w x = 0 := hwzero x (fun h => hxU (hKU h))
      dsimp [f]
      rw [hw]
      linarith [haneg x hx]
  refine ⟨f, (hac.add hwc).sub continuous_const, ?_, ?_⟩
  · intro i
    exact (((ha i).add (hwPL i)).add
      (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (-1 : ℝ))
        (e i).open_target)).congr (fun _ _ => (sub_eq_add_neg _ _).symm)
  · intro x
    by_cases hx : x ∈ N
    · rw [hfN x hx]
      obtain ⟨hmem, hfront, hint⟩ := hasign x (hNU hx)
      exact ⟨hmem, hfront, hint,
        iff_of_false (not_not.mpr hx) (not_lt_of_ge (hmem.mp hx))⟩
    · have hn := hfneg x hx
      exact ⟨iff_of_false hx (not_le_of_gt hn),
        iff_of_false (fun h => hx (he.closed.frontier_subset h)) hn.ne,
        iff_of_false (fun h => hx (interior_subset h)) (not_lt_of_ge hn.le),
        iff_of_true hx hn⟩

theorem exists_compact_domain_relative_defining_function
    (he : PLDomain e N) (hN : IsCompact N) {A U : Set X}
    (heA : PLDomain e A) (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    {f : X → ℝ} (hf : ContinuousOn f U)
    (hfPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U))
    (hpos : ∀ x ∈ A, x ∈ interior N ↔ 0 < f x)
    (hzero : ∀ x ∈ A, x ∈ frontier N ↔ f x = 0)
    {r : ℝ} (hr : 0 < r) (hbound : ∀ x ∈ A, |f x| ≤ r) :
    ∃ g : X → ℝ, Continuous g ∧
      (∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target) ∧
      EqOn g f A ∧ (∀ x, |g x| ≤ r) ∧
      ∀ x, (x ∈ frontier N ↔ g x = 0) ∧
        (x ∈ interior N ↔ 0 < g x) ∧ (x ∉ N ↔ g x < 0) := by
  obtain ⟨a, _, _, _, hac, ha, haf, habound, _⟩ :=
    OpenPartialHomeomorph.exists_supported_PL_scalar_extension e he.compatible he.cover
      hA hU hAU hf hfPL hr hbound
  obtain ⟨b, hbc, hb, hbsign⟩ := exists_compact_domain_signed_defining_function he hN
  obtain ⟨g, hgc, hg, hga, hgsign⟩ := heA.exists_bounded_same_signs_relative hA hbc hac hb ha
    (fun x hx => by rw [haf hx]; exact (hpos x hx).symm.trans (hbsign x).2.2.1)
    (fun x hx => by rw [haf hx]; exact (hzero x hx).symm.trans (hbsign x).2.1)
    hr (fun x _ => habound x)
  exact ⟨g, hgc, hg, hga.trans haf, fun x => (hgsign x).1, fun x =>
    ⟨(hbsign x).2.1.trans (hgsign x).2.2.1.symm,
      (hbsign x).2.2.1.trans (hgsign x).2.1.symm,
      (hbsign x).2.2.2.trans (hgsign x).2.2.2.symm⟩⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
