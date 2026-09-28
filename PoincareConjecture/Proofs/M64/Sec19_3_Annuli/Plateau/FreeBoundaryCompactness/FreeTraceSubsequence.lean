import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.LiftSelection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.VaryingTraceCompactness














set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.WeakCompactness



theorem degreeOneLift_continuous (sigma : M64PeriodicDegreeOneLift) :
    Continuous sigma.map := by
  have hLip : LipschitzWith
      (NNReal.mk sigma.lipschitz_constant sigma.lipschitz_nonnegative) sigma.map := by
    intro x y
    have hE := ENNReal.ofReal_le_ofReal (sigma.lipschitz_on x y)
    rw [ENNReal.ofReal_mul sigma.lipschitz_nonnegative] at hE
    simpa only [edist_dist, Real.dist_eq, ENNReal.coe_nnreal_eq, NNReal.coe_mk] using hE
  exact hLip.continuous

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "mu" => volume.restrict (interior m64AnnulusDomain)




theorem observedWeakAnnulus_free_trace_subsequence
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) (c0 c1 : ℝ → M)
    (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
    (A : ∀ j, M64ObservedWeakAnnulus (n := n) e
      (c0 ∘ (sigma0 j).map) (c1 ∘ (sigma1 j).map))
    {C : ℝ} (hC : ∀ j i, ‖(A j).column i‖ ^ 2 ≤ C) :
    ∃ (k : ℕ → ℕ) (L0 L1 : ℝ → ℝ)
      (L : M64ObservedWeakAnnulus (n := n) e (c0 ∘ L0) (c1 ∘ L1)),
      StrictMono k ∧ Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L0 0 ∈ Icc (0 : ℝ) curvePeriod ∧ L1 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      Tendsto (fun j => (A (k j)).value) atTop (𝓝 L.value) ∧
      (∀ i, WeakConverges (fun j => (A (k j)).column i) (L.column i)) ∧
      (∀ᵐ p ∂mu, Tendsto (fun j => (A (k j)).map p) atTop (𝓝 (L.map p))) ∧
      (∀ᵐ x ∂volume, Tendsto (fun j => c0 ((sigma0 (k j)).map x))
        atTop (𝓝 (c0 (L0 x)))) ∧
      ∀ᵐ x ∂volume, Tendsto (fun j => c1 ((sigma1 (k j)).map x))
        atTop (𝓝 (c1 (L1 x))) := by
  obtain ⟨k, L0, L1, hk, hL0, hL1, hP0, hP1, h00, h10, ht0, ht1⟩ :=
    degreeOneLift_pair_target_subsequence_ae c0 c1 hc0 hc1 hp0 hp1 sigma0 sigma1
  obtain ⟨l, L, hl, hv, hw, ha⟩ :=
    observedWeakAnnulus_varying_trace_subsequence e he hei hread
      (fun j => hc0.comp (degreeOneLift_continuous (sigma0 (k j))))
      (fun j => hc1.comp (degreeOneLift_continuous (sigma1 (k j))))
      ht0 ht1 (fun j => A (k j)) (fun j i => hC (k j) i)
  refine ⟨k ∘ l, L0, L1, L, hk.comp hl, hL0, hL1, hP0, hP1,
    h00, h10, hv, hw, ha, ?_, ?_⟩
  · filter_upwards [ht0] with x hx
    exact hx.comp hl.tendsto_atTop
  · filter_upwards [ht1] with x hx
    exact hx.comp hl.tendsto_atTop

end PoincareConjecture.M64
