import PoincareConjecture.Proofs.M65.Mathlib.GoodTimeGrid
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.ClosedCellJets

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

theorem m65FamilyGoodTimeGrid (C : M63FamilyConclusion G Gamma zeta)
    (E : M64AppliedFamilyEstimates G C) (n : ℕ) {T step r B : ℝ}
    (hT : T ∈ Ioo a b) (hstep : 0 < step) (hr : 0 < r) (hr1 : r < 1) (hB : 0 < B)
    (hend : a + ((n : ℝ) + 2) * step ≤ T)
    (hwidth : 4 * step ≤
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2)
    (hwindow : T +
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2 ≤ b)
    (hscale : r * B ≤
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) ^ 2)
    (circumference : ℝ) (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere)
    (hlength : ∀ s ∈ Ioo a T, r ≤ m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) s) :
    ∃ good : Finset ℕ, good ⊆ Finset.range n ∧
      (∀ j ∈ good, ∀ t ∈ Icc (a + ((j : ℝ) + 2) * step) (a + ((j : ℝ) + 3) * step),
        ∀ i x, m63CurvatureJetSquared (G.product circumference h).flow
          ((C.solutions circumference h).curve z) i t x ≤
            C.derivative_estimates.constant i / step ^ (i + 1)) ∧
      ((Finset.range n \ good).card : ℝ) * step ≤
        ((m63FamilyLengthSup (F.metric a) Gamma + 1) * Real.exp (G.K2 * (b - a))) / B := by
  have hgrid : a + (n : ℝ) * step ≤ b := by linarith [hT.2]
  obtain ⟨good, hgood, href, hbad⟩ := M65.exists_energy_good_grid n
    (hT.1.trans hT.2).le hstep hgrid
    (m65FamilyEnergy_nonneg C circumference h z)
    (m64FamilyEnergyIntegrable C E circumference h z)
    (m64FamilyEnergyBound C E circumference h hlt z) hB
  refine ⟨good, hgood, ?_, hbad⟩
  intro j hj t ht i x
  obtain ⟨s, hs, henergy⟩ := href j hj
  have hjn : j < n := Finset.mem_range.mp (hgood hj)
  have hcast : (j : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hjn
  have hmul := mul_le_mul_of_nonneg_right hcast hstep.le
  have hnonneg_j := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hstep.le
  have hsT : s ∈ Ioo a T := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  apply m65FamilyJets_on_delayedCell C circumference h hlt z
    ⟨hsT.1, hsT.2.trans hT.2⟩
    (left := a + (j : ℝ) * step) (step := step) (r := r) (B := B)
    ⟨hs.1, by linarith [hs.2]⟩ hstep hr hr1 hwidth
    (by linarith [hsT.2]) (hlength s hsT) henergy hscale t _ i x
  constructor <;> linarith [ht.1, ht.2]

end PoincareConjecture
