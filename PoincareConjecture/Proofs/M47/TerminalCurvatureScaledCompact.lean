import PoincareConjecture.Proofs.M47.TerminalCurvatureScaledRound
import PoincareConjecture.Proofs.M47.TerminalCurvatureComponentCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_eventually_compact_of_scaled_source_component
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X] [ConnectedSpace X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcoverU : (⋃ k, U k) = univ)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (M k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i j K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((rescaledMetric (g k) (Q k) (hQ k)).pullbackCoefficients
        (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) (hxscalar : 0 < D.scalarCurvature x)
    (hballs : ∀ R : ℝ, 0 < R → ∃ j, ∀ᶠ k in atTop,
      (rescaledMetric (g k) (Q k) (hQ k)).ball (phi k x) R ⊆ phi k '' U j)
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ k in atTop, ∀ Dk : LeviCivitaData (g k),
      ∀ N : SingularCComponent (g k) Dk C, phi k x ∈ N.carrier →
        IsCompact (univ : Set X) := by
  have hH := half_pos hxscalar
  obtain ⟨j, hj⟩ := hballs (C * (D.scalarCurvature x / 2) ^ (-1 / 2 : ℝ))
    (mul_pos hC (Real.rpow_pos_of_pos hH _))
  have hscalar := terminalCurvature_eventually_source_point_scalar
    (fun k => rescaledMetric (g k) (Q k) (hQ k)) h D
    U hU hmono hcoverU phi hsource c hcoverC hjet x hH
  filter_upwards [hj, hscalar, eventually_ge_atTop j] with k hkball hkscalar hjk Dk N hx
  have hlo : D.scalarCurvature x / 2 ≤
      (rescaledMetric_connection (g k) Dk (Q k) (hQ k)).scalarCurvature (phi k x) := by
    have he := (abs_lt.mp (hkscalar (rescaledMetric_connection (g k) Dk (Q k) (hQ k)))).1
    linarith
  have hNball := terminalCurvature_scaled_component_subset_ball N (hQ k) hH hx hlo
  have hc : N.carrier ⊆ (phi k).target := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hkball (hNball hy)
    apply (phi k).map_source
    rw [hsource k]
    exact hmono hjk hz
  exact terminalCurvature_compact_of_component_captured (phi k)
    N.component_eq N.compact hc

theorem terminalCurvature_eventually_compact_of_scaled_source_round
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X] [ConnectedSpace X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcoverU : (⋃ k, U k) = univ)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (M k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i j K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((rescaledMetric (g k) (Q k) (hQ k)).pullbackCoefficients
        (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) (hxscalar : 0 < D.scalarCurvature x)
    (hballs : ∀ R : ℝ, 0 < R → ∃ j, ∀ᶠ k in atTop,
      (rescaledMetric (g k) (Q k) (hQ k)).ball (phi k x) R ⊆ phi k '' U j)
    {epsilon : ℝ} (hsmall : epsilon ≤ 1 / 200) :
    ∀ᶠ k in atTop, ∀ _Dk : LeviCivitaData (g k),
      ∀ N : SingularRoundComponent (g k) epsilon, phi k x ∈ N.carrier →
        IsCompact (univ : Set X) := by
  have hH := half_pos hxscalar
  obtain ⟨j, hj⟩ := hballs
    (Real.sqrt (144 / (D.scalarCurvature x / 2)) * Real.sqrt 15 + 1) (by positivity)
  have hscalar := terminalCurvature_eventually_source_point_scalar
    (fun k => rescaledMetric (g k) (Q k) (hQ k)) h D
    U hU hmono hcoverU phi hsource c hcoverC hjet x hH
  filter_upwards [hj, hscalar, eventually_ge_atTop j] with k hkball hkscalar hjk Dk N hx
  have hlo : D.scalarCurvature x / 2 ≤
      (rescaledMetric_connection (g k) Dk (Q k) (hQ k)).scalarCurvature (phi k x) := by
    have he := (abs_lt.mp (hkscalar (rescaledMetric_connection (g k) Dk (Q k) (hQ k)))).1
    linarith
  have hNball := terminalCurvature_scaled_round_carrier_subset_ball Dk N hsmall (hQ k) hH hx hlo
  have hc : N.carrier ⊆ (phi k).target := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hkball (hNball hy)
    apply (phi k).map_source
    rw [hsource k]
    exact hmono hjk hz
  exact terminalCurvature_compact_of_component_captured (phi k)
    N.component_eq N.compact hc

end PoincareConjecture.M47
