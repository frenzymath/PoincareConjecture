import PoincareConjecture.Proofs.M65.Mathlib.GoodTimeParameters
import PoincareConjecture.Proofs.M65.Mathlib.GridPartition
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.ClosedCellJets
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.LengthNoncollapse

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

theorem m65Family_exists_fixed_good_grid (C : M63FamilyConclusion G Gamma zeta)
    (E : M64AppliedFamilyEstimates G C) (hab : a < b)
    {delta ell : ℝ} (hdelta : 0 < delta) (hell : 0 < ell) :
    ∃ B : ℝ, 1 < B ∧ ∃ T : ℝ, T ∈ Ioo a b ∧
      Real.exp (G.K2 * (b - T)) < 4 / 3 ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ≤ ell * Real.exp (-G.K2 * (b - a)) ∧
        r * B ≤ (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) ^ 2 ∧
        T + (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2 < b ∧
        ∃ n : ℕ, ∃ step : ℝ, 0 < step ∧ a + ((n : ℝ) + 2) * step = T ∧
          4 * step ≤
            (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2 ∧
          ∀ circumference : ℝ, ∀ h : 0 < circumference, circumference < 1 →
            ∀ z : LoopTwoSphere,
              (∀ t ∈ Icc T b, m62Length (G.product circumference h).flow
                ((C.solutions circumference h).curve z) t < ell) ∨
              ((∀ s ∈ Icc a T, ell * Real.exp (-G.K2 * (b - a)) ≤
                m62Length (G.product circumference h).flow
                  ((C.solutions circumference h).curve z) s) ∧
                ∃ good : Finset ℕ, good ⊆ Finset.range n ∧
                  (∀ j ∈ good, ∃ s : ℝ,
                    s ∈ Ioo (a + (j : ℝ) * step) (a + ((j : ℝ) + 1) * step) ∧
                    s ∈ Ioo a T ∧
                    r ≤ m62Length (G.product circumference h).flow
                      ((C.solutions circumference h).curve z) s ∧
                    m65FamilyEnergy C circumference h z s ≤ B ∧
                    (∀ t ∈ Icc (a + ((j : ℝ) + 2) * step)
                        (a + ((j : ℝ) + 3) * step), ∀ i x,
                      m63CurvatureJetSquared (G.product circumference h).flow
                        ((C.solutions circumference h).curve z) i t x ≤
                          C.derivative_estimates.constant i / step ^ (i + 1)) ∧
                    Icc (a + (j : ℝ) * step + 3 * step / 2)
                      (a + (j : ℝ) * step + 7 * step / 2) ⊆ Ioo a b ∧
                    (∀ t ∈ Icc (a + (j : ℝ) * step + 3 * step / 2)
                        (a + (j : ℝ) * step + 7 * step / 2), ∀ i x,
                      m63CurvatureJetSquared (G.product circumference h).flow
                        ((C.solutions circumference h).curve z) i t x ≤
                          C.derivative_estimates.constant i / (step / 2) ^ (i + 1))) ∧
                  (∑ i ∈ Finset.range (n + 3),
                    if i ∈ good.image (fun j => j + 2) then 0
                    else M65.delayedGridTime a b step n (i + 1) -
                      M65.delayedGridTime a b step n i) < delta) := by
  have hd : 0 < C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2 :=
    mul_pos C.derivative_estimates.delta0_positive
      (pow_pos C.derivative_estimates.radius0_positive _)
  obtain ⟨B, hB1, T, hT, hgrowth, r, hr, hr1, hrfloor, hscale, hwindow,
    n, step, hstep, hend, hwidth, hbudget⟩ :=
    M65.exists_goodTime_grid_parameters
      (C := (m63FamilyLengthSup (F.metric a) Gamma + 1) * Real.exp (G.K2 * (b - a)))
      hab hdelta hell hd G.nonnegative.2.2
  refine ⟨B, hB1, T, hT, hgrowth, r, hr, hr1, hrfloor, hscale, hwindow,
    n, step, hstep, hend, hwidth, ?_⟩
  intro circumference h hlt z
  rcases m65FamilyLength_short_or_earlier_lower_bound C E circumference h z
      ⟨hT.1.le, hT.2.le⟩ with hshort | hfloor
  · exact Or.inl hshort
  · apply Or.inr
    refine ⟨hfloor, ?_⟩
    have hB : 0 < B := by linarith
    have hgrid : a + (n : ℝ) * step ≤ b := by linarith [hT.2]
    obtain ⟨good, hgood, href, hbad⟩ := M65.exists_energy_good_grid n
      hab.le hstep hgrid (m65FamilyEnergy_nonneg C circumference h z)
      (m64FamilyEnergyIntegrable C E circumference h z)
      (m64FamilyEnergyBound C E circumference h hlt z) hB
    refine ⟨good, hgood, ?_, ?_⟩
    · intro j hj
      obtain ⟨s, hs, henergy⟩ := href j hj
      have hjn : j < n := Finset.mem_range.mp (hgood hj)
      have hcast : (j : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hjn
      have hmul := mul_le_mul_of_nonneg_right hcast hstep.le
      have hnonneg_j := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hstep.le
      have hsT : s ∈ Ioo a T := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hsab : s ∈ Ioo a b := ⟨hsT.1, hsT.2.trans hT.2⟩
      have hlength := hrfloor.trans (hfloor s ⟨hsT.1.le, hsT.2.le⟩)
      have href' : s ∈ Ioo (a + (j : ℝ) * step) (a + (j : ℝ) * step + step) :=
        ⟨hs.1, by linarith [hs.2]⟩
      have hlocalWindow : s +
          (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2 < b :=
        by linarith [hsT.2]
      refine ⟨s, hs, hsT, hlength, henergy, ?_, ?_, ?_⟩
      · intro t ht i x
        apply m65FamilyJets_on_delayedCell C circumference h hlt z hsab
          href' hstep hr hr1 hwidth hlocalWindow hlength henergy hscale t _ i x
        constructor <;> linarith [ht.1, ht.2]
      · intro t ht
        constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
      · exact m65FamilyJets_on_enlargedDelayedCell C circumference h hlt z hsab
          href' hstep hr hr1 hwidth hlocalWindow hlength henergy hscale
    · rw [M65.delayedGrid_gap_sum a b step n good hgood, hend]
      linarith

end PoincareConjecture
