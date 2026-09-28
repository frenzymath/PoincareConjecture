import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialSmallFilling
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialReplacementEnergy












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => ball (0 : LoopPlane) 1
local notation "K" => closedBall (0 : LoopPlane) 1
local notation "mu" => volume.restrict S
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)




theorem m64RadialFilling_energy_le_columns
    (e : M → E) (hei : IsEmbedding e) (F : LoopPlane → M)
    (W : Fin 2 → Lp E 2 mu) (hu : MemLp (e ∘ F) 2 mu)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {D B : ℝ} (hD : 0 ≤ D) (hQbound : ∀ q, ‖Q q‖ ≤ D)
    (hbound : ∀ i, ‖W i‖ ^ 2 ≤ B) :
    (∫ z in S, (Q (F z) (W 0 z) (W 0 z) + Q (F z) (W 1 z) (W 1 z)) / 2) ≤ D * B := by
  let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
  have hf : AEStronglyMeasurable F mu :=
    hei.aestronglyMeasurable_comp_iff.mp hu.aestronglyMeasurable
  have hi := m64Observed_energyDensity_integrable Q hQ hQbound F hf
    (fun i z => W i z) (fun i => Lp.memLp (W i))
  have hnorm (i : Fin 2) : IntegrableOn (fun z => ‖W i z‖ ^ 2) S volume :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (W i))).mp (Lp.memLp (W i))
  have hpoint (z : LoopPlane) (i : Fin 2) :
      Q (F z) (W i z) (W i z) ≤ D * ‖W i z‖ ^ 2 := by
    have hop := (Q (F z)).le_opNorm₂ (W i z) (W i z)
    have hmul := mul_le_mul_of_nonneg_right (hQbound (F z)) (sq_nonneg ‖W i z‖)
    rw [Real.norm_eq_abs] at hop
    nlinarith [le_abs_self (Q (F z) (W i z) (W i z))]
  calc
    _ ≤ ∫ z in S, (D * ‖W 0 z‖ ^ 2 + D * ‖W 1 z‖ ^ 2) / 2 := by
      apply integral_mono hi (((hnorm 0).const_mul D).add
        ((hnorm 1).const_mul D) |>.div_const 2)
      intro z
      exact div_le_div_of_nonneg_right (add_le_add (hpoint z 0) (hpoint z 1)) (by norm_num)
    _ = (D * ‖W 0‖ ^ 2 + D * ‖W 1‖ ^ 2) / 2 := by
      rw [integral_div, integral_add ((hnorm 0).const_mul D) ((hnorm 1).const_mul D)]
      simp only [integral_const_mul, ← LpFiniteCoordinatesNative.l2_norm_sq]
    _ ≤ D * B := by
      have h0 := mul_le_mul_of_nonneg_left (hbound 0) hD
      have h1 := mul_le_mul_of_nonneg_left (hbound 1) hD
      linarith

variable [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]




theorem m64ChartReadable_small_radial_H1_filling_energy
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (c : ℝ → M) (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c)
    (hcP : Function.Periodic c curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ rho : ℝ, 0 < rho ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : LoopPlane) (r : ℝ), 0 < r → r ≤ rho →
        ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
          (∀ t, angularPoint t 1 ≤ 0 → gamma t = c ((a + r • angularPoint t) 0)) →
          ∀ (w : ℕ → ℝ → E), (∀ j, ContDiff ℝ 1 (w j)) →
            (∀ j, Function.Periodic (w j) curvePeriod) →
            TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
            ∀ v : ℝ → E, MemLp v 2 circleMu →
              (∀ x ∈ Icc (0 : ℝ) curvePeriod,
                e (gamma x) - e (gamma 0) = ∫ t in (0 : ℝ)..x, v t) →
              Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
                ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0) →
              (∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2) < epsilon →
              ∃ (F : LoopPlane → M) (W : Fin 2 → Lp E 2 mu),
                ContinuousOn F K ∧ (∀ t, F (angularPoint t) = gamma t) ∧
                (∀ z ∈ K, z 1 ≤ 0 → F z = c ((a + r • z) 0)) ∧
                MemLp (e ∘ F) 2 mu ∧
                (∀ i, ∀ᵐ z ∂mu, W i z ∈ range (mfderiv (𝓡 n) (𝓡 m) e (F z))) ∧
                (∀ i b, HasWeakPartialDeriv i
                  (fun z => W i z b) (fun z => e (F z) b) S) ∧
                (∫ z in S,
                  (Q (F z) (W 0 z) (W 0 z) + Q (F z) (W 1 z) (W 1 z)) / 2) ≤
                  C * ((∫ t in Icc (0 : ℝ) curvePeriod, ‖v t‖ ^ 2) + r ^ 2) := by
  obtain ⟨epsilon, hepsilon, rho, hrho, C, hC, hfill⟩ :=
    m64ChartReadable_small_radial_H1_filling g e he hei hread c hc hcP
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨D, hD⟩ := hbounded.exists_norm_le
  have hbound (q : M) : ‖Q q‖ ≤ max D 0 :=
    (hD _ (mem_range_self q)).trans (le_max_left _ _)
  refine ⟨epsilon, hepsilon, rho, hrho, max D 0 * C,
    mul_nonneg (le_max_right _ _) hC, ?_⟩
  intro a r hr hrrho gamma hgamma hgammaP hmatch w hw hwP hlim v hv hFTC hder hsmall
  obtain ⟨F, W, hcF, hcircle, hfixed, hu, ht, hweak, henergy⟩ :=
    hfill a r hr hrrho gamma hgamma hgammaP hmatch w hw hwP hlim v hv hFTC hder hsmall
  refine ⟨F, W, hcF, hcircle, hfixed, hu, ht, hweak, ?_⟩
  exact (m64RadialFilling_energy_le_columns e hei F W hu Q hQ
    (le_max_right _ _) hbound henergy).trans_eq (by ring)

end PoincareConjecture
