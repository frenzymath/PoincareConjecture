import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.LocalJets









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}



theorem m65FamilyJets_on_delayedCell (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) {s left step r B : ℝ}
    (hs : s ∈ Ioo a b) (href : s ∈ Ioo left (left + step))
    (hstep : 0 < step) (hr : 0 < r) (hr1 : r < 1)
    (hwidth : 4 * step ≤
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2)
    (hwindow : s +
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2 < b)
    (hlength : r ≤ m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) s)
    (henergy : m65FamilyEnergy C circumference h z s ≤ B)
    (hscale : r * B ≤
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) ^ 2) :
    ∀ t ∈ Icc (left + 2 * step) (left + 3 * step), ∀ i x,
      m63CurvatureJetSquared (G.product circumference h).flow
        ((C.solutions circumference h).curve z) i t x ≤
          C.derivative_estimates.constant i / step ^ (i + 1) := by
  intro t ht i x
  have hsep : step < t - s := by linarith [ht.1, href.2]
  have hlocal : t ∈ Ioo s
      (s + (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2) :=
    ⟨by linarith, by linarith [ht.2, href.1]⟩
  have hjet := m65FamilyJets_of_energy_le C circumference h hlt z hs hr hr1
    hwindow hlength henergy hscale t hlocal i x
  exact hjet.trans (div_le_div_of_nonneg_left (C.derivative_estimates.constant_nonnegative i)
    (pow_pos hstep _) (pow_le_pow_left₀ hstep.le hsep.le _))




theorem m65FamilyJets_on_enlargedDelayedCell (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) {s left step r B : ℝ}
    (hs : s ∈ Ioo a b) (href : s ∈ Ioo left (left + step))
    (hstep : 0 < step) (hr : 0 < r) (hr1 : r < 1)
    (hwidth : 4 * step ≤
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2)
    (hwindow : s +
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2 < b)
    (hlength : r ≤ m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) s)
    (henergy : m65FamilyEnergy C circumference h z s ≤ B)
    (hscale : r * B ≤
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) ^ 2) :
    ∀ t ∈ Icc (left + 3 * step / 2) (left + 7 * step / 2), ∀ i x,
      m63CurvatureJetSquared (G.product circumference h).flow
        ((C.solutions circumference h).curve z) i t x ≤
          C.derivative_estimates.constant i / (step / 2) ^ (i + 1) := by
  intro t ht i x
  have hsep : step / 2 < t - s := by linarith [ht.1, href.2]
  have hlocal : t ∈ Ioo s
      (s + (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2) :=
    ⟨by linarith, by linarith [ht.2, href.1]⟩
  have hjet := m65FamilyJets_of_energy_le C circumference h hlt z hs hr hr1
    hwindow hlength henergy hscale t hlocal i x
  exact hjet.trans (div_le_div_of_nonneg_left (C.derivative_estimates.constant_nonnegative i)
    (pow_pos (half_pos hstep) _) (pow_le_pow_left₀ (half_pos hstep).le hsep.le _))

end PoincareConjecture
