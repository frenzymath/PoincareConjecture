import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FullStripPhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PeriodicStripEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseEnergy









set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

local notation "S" => interior m64AnnulusDomain
local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)




theorem full_strip_logarithmic_oscillation
    (L : LoopPlane → ℝ) (hLc : Continuous L) (hL : ContDiffOn ℝ 1 L Strip)
    {d : ℝ} (hp : ∀ x s,
      L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d)
    (hmono : Monotone (fun x => L (annulusPoint x 0)))
    (hF : IntegrableOn (phaseGradientDensity L) S)
    (x : ℝ) {rho : ℝ} (hrho : 0 < rho) (hwidth : rho < curvePeriod / 2)
    (hr : rho < 1) {N : ℕ} (hN : 0 < N) :
    (L (annulusPoint (x + rho * Real.exp (-(N : ℝ))) 0) -
      L (annulusPoint (x - rho * Real.exp (-(N : ℝ))) 0)) ^ 2 ≤
        Real.pi * (∫ p in S, phaseGradientDensity L p) / N := by
  let c := curvePeriod / 2
  let a := x - c
  let V := L ∘ angularStripShift a
  have hVs : ContDiffOn ℝ 1 V S := by
    apply hL.comp ((angularStripShift_contDiff a).of_le (by simp)).contDiffOn
    intro p hp
    have hh := (m64AnnulusInterior_coordinates p).mp hp
    exact ⟨hh.2.2.1, hh.2.2.2⟩
  have hVm : MonotoneOn (fun y => V (annulusPoint y 0)) (Icc (0 : ℝ) curvePeriod) := by
    intro y _ z _ hyz
    apply hmono
    change y + a ≤ z + a
    linarith
  obtain ⟨hVi, henergy⟩ := phase_angular_shift_energy L hL hp hF a
  have hcP : c + rho < curvePeriod := by dsimp only [c]; linarith
  have hsub := upperBoundaryDisk_subset_interior hwidth hcP hr
  have hosc := boundary_logarithmic_oscillation V
    (hLc.comp (angularStripShift_contDiff a).continuous) hVs hVm hrho hwidth hcP hr
    (hVi.mono_set hsub) hN
  have hdisk : (∫ p in upperBoundaryDisk c rho, phaseGradientDensity V p) ≤
      ∫ p in S, phaseGradientDensity V p :=
    setIntegral_mono_set hVi
      (ae_of_all _ (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))) (ae_of_all _ hsub)
  have hfinal := hosc.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hdisk.trans_eq henergy) Real.pi_pos.le)
      (by positivity : (0 : ℝ) ≤ N))
  have hpoint (y : ℝ) : V (annulusPoint y 0) = L (annulusPoint (y + a) 0) := rfl
  rw [hpoint, hpoint] at hfinal
  have hplus : c + rho * Real.exp (-(N : ℝ)) + a = x + rho * Real.exp (-(N : ℝ)) := by
    dsimp only [a]
    ring
  have hminus : c - rho * Real.exp (-(N : ℝ)) + a = x - rho * Real.exp (-(N : ℝ)) := by
    dsimp only [a]
    ring
  rw [hplus, hminus] at hfinal
  exact hfinal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem annulus_full_strip_lower_phase_bound
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map Strip)
    (L0 : ℝ → ℝ) (hL0 : Continuous L0)
    (hzero : ∀ x, P.circle.quotient (L0 x) = (c0 x).2)
    {d : ℝ} (hshift : ∀ x, L0 (x + curvePeriod) = L0 x + d)
    (hmono : Monotone L0) {lo hi r : ℝ} (hlo : 0 < lo) (hr : r ∈ Icc lo hi)
    (hE : IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
      r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2) m64AnnulusDomain)
    (x : ℝ) {rho : ℝ} (hrho : 0 < rho) (hwidth : rho < curvePeriod / 2)
    (hradius : rho < 1) {N : ℕ} (hN : 0 < N) :
    (L0 (x + rho * Real.exp (-(N : ℝ))) - L0 (x - rho * Real.exp (-(N : ℝ)))) ^ 2 ≤
      (2 * Real.pi * max lo⁻¹ hi) * m64ClassicalWeightedGramEnergy (P.flow.metric t) A r / N := by
  obtain ⟨L, hLc, hL, hquot, hb, hp⟩ :=
    annulus_full_strip_exists_circle_phase P t A hA L0 hL0 hzero hshift
  have hS : S ⊆ Strip := by
    intro p hp
    have hh := (m64AnnulusInterior_coordinates p).mp hp
    exact ⟨hh.2.2.1, hh.2.2.2⟩
  obtain ⟨hphase, henergy⟩ := circle_phase_energy_le_weighted_annulus P t A (hA.mono hS)
    L (hL.mono hS) (fun p hp => hquot p ⟨hp.2.2.1, hp.2.2.2⟩) hlo hr hE
  have hm : Monotone (fun y => L (annulusPoint y 0)) := by simpa only [hb] using hmono
  have hosc := full_strip_logarithmic_oscillation L hLc hL hp hm hphase
    x hrho hwidth hradius hN
  rw [hb, hb] at hosc
  have hfinal := hosc.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left henergy Real.pi_pos.le) (by positivity : (0 : ℝ) ≤ N))
  exact hfinal.trans_eq (by ring)

end PoincareConjecture.M64
