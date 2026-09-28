import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import Mathlib.Tactic.Linarith



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def collarNormalReflection : (P × ℝ) ≃L[ℝ] (P × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ P).prodCongr (ContinuousLinearEquiv.neg ℝ)

theorem collarNormalReflection_apply (z : P × ℝ) :
    collarNormalReflection z = (z.1, -z.2) := rfl

theorem collarNormalReflection_involutive :
    Function.Involutive (collarNormalReflection : P × ℝ → P × ℝ) := by
  intro z
  simp only [collarNormalReflection_apply, neg_neg]

noncomputable def doubleHalfspaceMap (f : P × ℝ → P × ℝ) (z : P × ℝ) : P × ℝ :=
  if 0 ≤ z.2 then f z else collarNormalReflection (f (collarNormalReflection z))

theorem doubleHalfspaceMap_positive (f : P × ℝ → P × ℝ) {z : P × ℝ} (hz : 0 ≤ z.2) :
    doubleHalfspaceMap f z = f z := if_pos hz

theorem doubleHalfspaceMap_negative {f : P × ℝ → P × ℝ} {A : Set P} {r : ℝ}
    (hfzero : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, (f z).2 = 0 ↔ z.2 = 0)
    {z : P × ℝ} (hz : z ∈ A ×ˢ Icc (-r) 0) :
    doubleHalfspaceMap f z = collarNormalReflection (f (collarNormalReflection z)) := by
  by_cases hn : 0 ≤ z.2
  · have ht : z.2 = 0 := le_antisymm hz.2.2 hn
    have hzpos : z ∈ A ×ˢ Icc (0 : ℝ) r := ⟨hz.1, hn, by linarith [hz.2.1]⟩
    have hft := (hfzero z hzpos).mpr ht
    rw [doubleHalfspaceMap_positive f hn]
    have hrefl : collarNormalReflection z = z := by
      exact Prod.ext rfl (by change -z.2 = z.2; rw [ht]; simp)
    rw [hrefl, collarNormalReflection_apply]
    exact Prod.ext rfl (by simp only [hft, neg_zero])
  · exact if_neg hn

theorem doubleHalfspaceMap_nonneg_iff {f : P × ℝ → P × ℝ} {A : Set P} {r : ℝ}
    (hfpos : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, 0 ≤ (f z).2)
    (hfzero : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, (f z).2 = 0 ↔ z.2 = 0)
    {z : P × ℝ} (hz : z ∈ A ×ˢ Icc (-r) r) :
    0 ≤ (doubleHalfspaceMap f z).2 ↔ 0 ≤ z.2 := by
  by_cases hn : 0 ≤ z.2
  · rw [doubleHalfspaceMap_positive f hn]
    exact iff_of_true (hfpos z ⟨hz.1, hn, hz.2.2⟩) hn
  · have hzref : collarNormalReflection z ∈ A ×ˢ Icc (0 : ℝ) r :=
      ⟨hz.1, by change 0 ≤ -z.2; linarith, by change -z.2 ≤ r; linarith [hz.2.1]⟩
    have hp := hfpos _ hzref
    have hne : (f (collarNormalReflection z)).2 ≠ 0 := by
      intro h
      have ht := (hfzero _ hzref).mp h
      change -z.2 = 0 at ht
      exact hn (by linarith)
    simp only [doubleHalfspaceMap, if_neg hn, collarNormalReflection_apply]
    change 0 ≤ -(f (z.1, -z.2)).2 ↔ 0 ≤ z.2
    exact iff_of_false (by
      change ¬0 ≤ -(f (collarNormalReflection z)).2
      intro h
      exact hne (le_antisymm (by linarith) hp)) hn

theorem doubleHalfspaceMap_injOn {f : P × ℝ → P × ℝ} {A : Set P} {r : ℝ}
    (hfi : InjOn f (A ×ˢ Icc (0 : ℝ) r))
    (hfpos : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, 0 ≤ (f z).2)
    (hfzero : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, (f z).2 = 0 ↔ z.2 = 0) :
    InjOn (doubleHalfspaceMap f) (A ×ˢ Icc (-r) r) := by
  intro z hz w hw heq
  have hsign : 0 ≤ z.2 ↔ 0 ≤ w.2 := by
    rw [← doubleHalfspaceMap_nonneg_iff hfpos hfzero hz,
      ← doubleHalfspaceMap_nonneg_iff hfpos hfzero hw, heq]
  by_cases hn : 0 ≤ z.2
  · have hm := hsign.mp hn
    rw [doubleHalfspaceMap_positive f hn, doubleHalfspaceMap_positive f hm] at heq
    exact hfi ⟨hz.1, hn, hz.2.2⟩ ⟨hw.1, hm, hw.2.2⟩ heq
  · have hm : ¬0 ≤ w.2 := fun h => hn (hsign.mpr h)
    simp only [doubleHalfspaceMap, if_neg hn, if_neg hm] at heq
    apply collarNormalReflection.injective
    apply hfi _ _ (collarNormalReflection.injective heq)
    · exact ⟨hz.1, by change 0 ≤ -z.2; linarith, by change -z.2 ≤ r; linarith [hz.2.1]⟩
    · exact ⟨hw.1, by change 0 ≤ -w.2; linarith, by change -w.2 ≤ r; linarith [hw.2.1]⟩

variable [FiniteDimensional ℝ P]

theorem finitePiecewiseAffineOn_doubleHalfspaceMap {f : P × ℝ → P × ℝ}
    {A : Set P} {r : ℝ}
    (hf : FinitePiecewiseAffineOn f (A ×ˢ Icc (0 : ℝ) r))
    (hfzero : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, (f z).2 = 0 ↔ z.2 = 0) :
    FinitePiecewiseAffineOn (doubleHalfspaceMap f) (A ×ˢ Icc (-r) r) := by
  let J : (P × ℝ) ≃ᴬ[ℝ] (P × ℝ) := collarNormalReflection.toContinuousAffineEquiv
  have hJimage : J.symm '' (A ×ˢ Icc (0 : ℝ) r) = A ×ˢ Icc (-r) 0 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw.1, by change -r ≤ -w.2; linarith [hw.2.2],
        by change -w.2 ≤ 0; linarith [hw.2.1]⟩
    · intro hz
      refine ⟨collarNormalReflection z, ⟨hz.1, ?_, ?_⟩, ?_⟩
      · change 0 ≤ -z.2; linarith [hz.2.2]
      · change -z.2 ≤ r; linarith [hz.2.1]
      · exact J.symm_apply_apply z
  have hneg : FinitePiecewiseAffineOn
      (fun z => collarNormalReflection (f (collarNormalReflection z))) (A ×ˢ Icc (-r) 0) := by
    exact hJimage ▸ (hf.precomp_affineEquiv J).postcomp J.toContinuousAffineMap
  have hp : FinitePiecewiseAffineOn (doubleHalfspaceMap f) (A ×ˢ Icc (0 : ℝ) r) :=
    hf.congr (fun _ hz => (doubleHalfspaceMap_positive f hz.2.1).symm)
  have hn : FinitePiecewiseAffineOn (doubleHalfspaceMap f) (A ×ˢ Icc (-r) 0) :=
    hneg.congr (fun _ hz => (doubleHalfspaceMap_negative hfzero hz).symm)
  have hcover : (A ×ˢ Icc (0 : ℝ) r) ∪ (A ×ˢ Icc (-r) 0) = A ×ˢ Icc (-r) r := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact ⟨hz.1, by linarith [hz.2.1, hz.2.2], hz.2.2⟩
      · exact ⟨hz.1, hz.2.1, by linarith [hz.2.1, hz.2.2]⟩
    · intro hz
      by_cases hn : 0 ≤ z.2
      · exact Or.inl ⟨hz.1, hn, hz.2.2⟩
      · exact Or.inr ⟨hz.1, hz.2.1, (lt_of_not_ge hn).le⟩
  exact hcover ▸ finitePiecewiseAffineOn_union hp hn

end PoincareConjecture.M76
