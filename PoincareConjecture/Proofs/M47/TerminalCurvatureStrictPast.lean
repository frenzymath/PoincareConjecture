import PoincareConjecture.Proofs.M47.TerminalCurvatureSurgeryCases
import PoincareConjecture.Definitions.Ch16.ControlledSurgery











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem terminalCurvature_readout_of_strict_past
    {ι : Type*} (F : ℕ → SurgeryFlowData.{u}) (t u Q r : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k)
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X] [ConnectedSpace X]
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcoverU : (⋃ k, U k) = univ) (hcompact : ∀ j, IsCompact (closure (U j)))
    (p : X) (hp : ∀ j, p ∈ U j)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X ((F k).slice (u k)).carrier ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i j K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j
        ((rescaledMetric ((F k).metric (u k)) (Q k) (hQ k)).pullbackCoefficients
          (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) (hxscalar : 0 < D.scalarCurvature x)
    (hballs : ∀ R : ℝ, 0 < R → ∃ j, ∀ᶠ k in atTop,
      (rescaledMetric ((F k).metric (u k)) (Q k) (hQ k)).ball (phi k x) R ⊆
        phi k '' U j)
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hroundSmall : epsilon ≤ 1 / 200) (hC : 0 < C)
    (hEpsilon : ∀ k, (F k).parameters.epsilon = epsilon)
    (hCeq : ∀ k, (F k).parameters.C = C)
    (xEarlier : ∀ k, ((F k).slice (u k)).carrier)
    (hpoint : ∀ k, phi k x = xEarlier k)
    (hPast : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (t k)) (r k))
    (huPast : ∀ k, u k ∈ Ico 0 (t k))
    (huDomain : ∀ k, u k ∈ (F k).time_domain)
    (hscalar : ∀ᶠ k in atTop,
      (r k)⁻¹ ^ 2 ≤ ((F k).connection (u k)).scalarCurvature (xEarlier k)) :
    (∃ W : EpsilonNeck h, W.connection = D ∧ W.epsilon = 2 * epsilon ∧
      D.scalarCurvature x ≤ (4 * max 1 C) * D.scalarCurvature W.center) ∨
        IsCompact (univ : Set X) := by
  have hscalar' : ∀ᶠ k in atTop,
      (r k)⁻¹ ^ 2 ≤ ((F k).connection (u k)).scalarCurvature (phi k x) := by
    filter_upwards [hscalar] with k hk
    simpa only [hpoint k] using hk
  have hcanonical : ∀ᶠ k in atTop,
      SurgeryCanonicalControl (F k) (u k) (phi k x) epsilon C := by
    filter_upwards [hscalar'] with k hk
    simpa only [hEpsilon k, hCeq k] using
      hPast k (u k) (huPast k) (huDomain k) (phi k x) hk
  exact terminalCurvature_readout_of_surgery_source_canonical
    F u Q hQ h D U hU hmono hcoverU hcompact p hp phi hsource c hcoverC hjet
      x hxscalar hballs hepsilon hsmall hroundSmall hC hcanonical

end PoincareConjecture.M47
