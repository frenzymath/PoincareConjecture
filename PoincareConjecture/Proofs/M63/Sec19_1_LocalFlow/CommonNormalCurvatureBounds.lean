import PoincareConjecture.Proofs.M63.Adapters
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.SmoothCurvatureBarrier
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.BoundedCurvatureFirstJet
import PoincareConjecture.Proofs.M62.Lemma0_4_CurveTheory











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem exists_common_normal_curvature_bounds
    (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (c : ℕ → ℝ → ℝ → M)
    (hc : ∀ j, M63SmoothShrinkingCurveOn F (c j) (Icc a T))
    {R0 : ℝ} (hR0 : 0 ≤ R0)
    (hinit : ∀ j x, m62CurvatureSquared F (c j) a x ≤ R0) :
    ∃ delta : ℝ, 0 < delta ∧ a + 2 * delta ≤ T ∧
      2 * delta ≤ 1 ∧ ∃ R J : ℝ, 0 ≤ R ∧ 0 ≤ J ∧
        (∀ j t, t ∈ Icc a (a + 2 * delta) → ∀ x,
          m62CurvatureSquared F (c j) t x ≤ R) ∧
        (∀ j t, t ∈ Ioc a (a + delta) → ∀ x,
          (F.metric t).tangentNorm (c j x t)
            (m63CurvatureJet F (c j) 1 t x) ≤ J / Real.sqrt (t - a)) := by
  obtain ⟨K0, K1, K2, ⟨h0, h1, h2⟩, hBounds⟩ := M62.exists_ambient_bounds F hcompact
  let Q := R0 + 1
  let A := 2 + m62C0 K0 K1 K2
  have hQ : 0 < Q := by dsimp only [Q]; linarith only [hR0]
  have hC : 0 ≤ m62C0 K0 K1 K2 := by unfold m62C0; positivity
  have hA : 0 < A := by dsimp only [A]; linarith only [hC]
  let delta := min ((T - a) / 2) (min (1 / 2) (1 / (4 * A * Q)))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (div_pos (sub_pos.mpr haT) (by norm_num))
      (lt_min (by norm_num) (one_div_pos.mpr (by positivity)))
  have hdeltaT : delta ≤ (T - a) / 2 := min_le_left _ _
  have hdeltaOne : delta ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaSmall : delta ≤ 1 / (4 * A * Q) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hT : a + 2 * delta ≤ T := by linarith only [hdeltaT]
  have hone : 2 * delta ≤ 1 := by linarith only [hdeltaOne]
  have hshort : A * Q * ((a + 2 * delta) - a) ≤ 1 / 2 := by
    have hmul := (le_div_iff₀ (show 0 < 4 * A * Q by positivity)).mp hdeltaSmall
    nlinarith only [hmul]
  have haD : a < a + 2 * delta := by linarith only [hdelta]
  have hsubT : Icc a (a + 2 * delta) ⊆ Icc a T := Icc_subset_Icc_right hT
  have hsubF : Icc a (a + 2 * delta) ⊆ Icc a b :=
    Icc_subset_Icc_right (hT.trans hTb)
  let F' := m63RestrictClosedFlow F a (a + 2 * delta) hsubF haD
  have hc' (j : ℕ) : M62ShrinkingCurve F' (c j) :=
    m63SmoothRestriction (hc j) a (a + 2 * delta) hsubT haD
  have hBounds' : CurveEvolutionAmbientBounds F' K0 K1 K2 :=
    m63RestrictAmbientBounds hBounds a (a + 2 * delta) hsubF haD
  have hcap (j : ℕ) (t : ℝ) (ht : t ∈ Icc a (a + 2 * delta)) (x : ℝ) :
      m62CurvatureSquared F (c j) t x ≤ 2 * Q := by
    have hE := M62.curve_estimates F' (c j) (hc' j) h0 h1 h2 hBounds'
    have hinitial (y : ℝ) : m62CurvatureSquared F' (c j) a y + 1 ≤ Q := by
      change m62CurvatureSquared F (c j) a y + 1 ≤ R0 + 1
      linarith only [hinit j y]
    have hbar := m63SmoothCurvatureSquared_shortTime F' (c j) (hc' j)
      h0 h1 h2 hE hQ hshort hinitial x t ht
    have hbound := hbar.1.trans hbar.2
    change m62CurvatureSquared F (c j) t x + 1 ≤ 2 * Q at hbound
    linarith only [hbound]
  have hR : 0 ≤ 2 * Q := by positivity
  obtain ⟨C0, hC0, hjet⟩ := m63Exists_boundedCurvature_firstJet_bound F' hcompact hR
  refine ⟨delta, hdelta, hT, hone, 2 * Q, Real.sqrt C0, hR,
    Real.sqrt_nonneg _, hcap, ?_⟩
  intro j t ht x
  have ht' : t ∈ Ioo a (a + 2 * delta) :=
    ⟨ht.1, by linarith only [ht.2, hdelta]⟩
  have htime : t - a ≤ 1 := by linarith only [ht.2, hone, hdelta]
  have hbound := hjet (c j) (hc' j)
    (fun s hs y => hcap j s (Ioo_subset_Icc_self hs) y) x t ht' htime
  change Real.sqrt (m63CurvatureJetSquared F' (c j) 1 t x) ≤
    Real.sqrt C0 / Real.sqrt (t - a)
  exact (Real.sqrt_le_sqrt hbound).trans_eq (Real.sqrt_div hC0 _)

end PoincareConjecture.M63
