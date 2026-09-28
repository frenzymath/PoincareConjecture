import PoincareConjecture.Proofs.M47.TerminalCommonIntervalScalar
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalFloorScale










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem limitAlternatives_terminal_common_duration
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (V : GeneralizedBlowupSequence.{u})
    {M : ℕ → ℕ → Type u} [∀ i k, TopologicalSpace (M i k)]
    [∀ i k, ChartedSpace E (M i k)] [∀ i k, IsManifold (𝓡 3) ∞ (M i k)]
    [∀ i k, T2Space (M i k)]
    {X : Type u} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    {g : ∀ i k, RiemannianMetric 3 (M i k)}
    (D : ∀ i k, LeviCivitaData (g i k))
    {g0 : RiemannianMetric 3 X} (D0 : LeviCivitaData g0)
    (f : ∀ i k, PartialDiffeomorph (𝓡 3) (𝓡 3) E (M i k) ∞)
    (f0 : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) E X ∞)
    (actual : ∀ i k, M i k → ((V.flow k).slice (V.base k).1).carrier)
    (hread : ∀ i, ∀ᶠ k in atTop, ∀ z,
      (D i k).scalarCurvature z =
        (V.flow k).scalar ⟨(V.base k).1, actual i k z⟩ / V.scale k)
    (hsource : ∀ i K, IsCompact K → K ⊆ (f0 i).source →
      ∀ᶠ k in atTop, K ⊆ (f i k).source)
    (hjet : ∀ i K, IsCompact K → K ⊆ (f0 i).source → ∀ j ≤ 2,
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ j ((g i k).pullbackCoefficients (f i k)))
        (iteratedFDeriv ℝ j (g0.pullbackCoefficients (f0 i))) atTop K)
    (hcover : ∀ A : ℝ, 0 < A → ∃ s : Finset ℕ, ∃ K : ℕ → Set E,
      (∀ i ∈ s, IsCompact (K i) ∧ K i ⊆ (f0 i).source) ∧
      ∀ᶠ k in atTop, ∀ y ∈ V.baseBall k A,
        ∃ i ∈ s, ∃ z ∈ K i, actual i k (f i k z) = y)
    {B0 : ℝ} (_hB0 : 0 < B0)
    (hnorm : ∀ z, D0.curvatureTensorNorm z ≤ B0)
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hthreshold : ∀ k, (r k)⁻¹ ^ 2 ≤ V.scale k)
    (eta : ℝ) :
    ∃ K0 Delta : ℝ,
      K0 = max 1 (3 * B0) ∧
      1 ≤ K0 ∧
      0 < Delta ∧
      Delta ≤ 1 ∧
      Delta = terminalCommonIntervalDuration S B K0 ∧
      (∀ A : ℝ, 0 < A → ∀ᶠ k in atTop, ∀ y ∈ V.baseBall k A,
        (V.flow k).scalar ⟨(V.base k).1, y⟩ ≤ (2 * K0) * V.scale k) ∧
      (∀ᶠ k in atTop,
        64 * (2 * Delta + 1) ≤ V.scale k ∧
        B.curvature_threshold ≤ V.scale k ∧
        blowupPinchingThreshold (8 * K0) eta ≤ V.scale k ∧
        (r k)⁻¹ ^ 2 ≤ V.scale k ∧
        0 < V.scale k ∧
        0 < (V.scale k * (r k) ^ 2)⁻¹ ∧
        (V.scale k * (r k) ^ 2)⁻¹ ≤ 1 ∧
        (r k)⁻¹ ^ 2 / V.scale k =
          (V.scale k * (r k) ^ 2)⁻¹ ∧
        (V.scale k)⁻¹ =
          (V.scale k * (r k) ^ 2)⁻¹ * (r k) ^ 2) := by
  let K0 : ℝ := max 1 (3 * B0)
  have hterminal := terminalCommonInterval_terminal_scalar V D D0 f f0 actual
    hread hsource hjet hcover hnorm
  have hterminal' :
      1 ≤ K0 ∧ ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop, ∀ y ∈ V.baseBall k A,
        (V.flow k).scalar ⟨(V.base k).1, y⟩ ≤ (2 * K0) * V.scale k := by
    simpa only [K0] using hterminal
  have hK : 1 ≤ K0 := hterminal'.1
  obtain ⟨Delta, hDelta, hDeltaPos, hDeltaLe, hscale⟩ :=
    terminalCommonInterval_after_terminal_curvature_floor S B V
      (K := K0) hK (eta := eta) r hr hthreshold
  refine ⟨K0, Delta, ?_, hK, hDeltaPos, hDeltaLe, hDelta,
    hterminal'.2, hscale⟩
  rfl

end PoincareConjecture.M47
