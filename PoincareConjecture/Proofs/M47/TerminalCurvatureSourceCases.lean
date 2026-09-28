import PoincareConjecture.Proofs.M47.TerminalCurvatureSourceNeck
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourceCap
import PoincareConjecture.Proofs.M47.TerminalCurvatureRoundCapture









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_readout_of_source_cases
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X] [ConnectedSpace X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (h : RiemannianMetric 3 X)
    (D : LeviCivitaData h) (Dsource : ∀ k, LeviCivitaData (g k))
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcoverU : (⋃ k, U k) = univ) (hcompact : ∀ j, IsCompact (closure (U j)))
    (p : X) (hp : ∀ j, p ∈ U j)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (M k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i j K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((g k).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) (hxscalar : 0 < D.scalarCurvature x)
    (hballs : ∀ R : ℝ, 0 < R → ∃ j, ∀ᶠ k in atTop,
      (g k).ball (phi k x) R ⊆ phi k '' U j)
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hroundSmall : epsilon ≤ 1 / 200) (hC : 0 < C)
    (hmodels : ∀ᶠ k in atTop,
      (∃ N : EpsilonNeck (g k), N.epsilon = epsilon ∧ N.center = phi k x) ∨
      (∃ N : CapCertificate (g k), N.epsilon = epsilon ∧ N.cap_constant ≤ C ∧
        phi k x ∈ N.core) ∨
      (∃ N : SingularCComponent (g k) (Dsource k) C, phi k x ∈ N.carrier) ∨
      (∃ N : SingularRoundComponent (g k) epsilon, phi k x ∈ N.carrier)) :
    (∃ W : EpsilonNeck h, W.connection = D ∧ W.epsilon = 2 * epsilon ∧
      D.scalarCurvature x ≤ (4 * max 1 C) * D.scalarCurvature W.center) ∨
        IsCompact (univ : Set X) := by
  have hneck := terminalCurvature_eventually_source_neck_readout
    g h D U hU hmono hcoverU hcompact p hp phi hsource c hcoverC hjet x hxscalar hballs
      hepsilon hsmall
  have hcap := terminalCurvature_eventually_source_cap_readout
    g h D U hU hmono hcoverU hcompact p hp phi hsource c hcoverC hjet x hxscalar hballs
      hepsilon hsmall hC
  have hcomponent := terminalCurvature_eventually_compact_of_source_component
    g h D U hU hmono hcoverU phi hsource c hcoverC hjet x hxscalar hballs hC
  have hround := terminalCurvature_eventually_compact_of_source_round
    g h D U hU hmono hcoverU phi hsource c hcoverC hjet x hxscalar hballs hroundSmall
  obtain ⟨k, hkneck, hkcap, hkcomponent, hkround, hkmodels⟩ :=
    (hneck.and (hcap.and (hcomponent.and (hround.and hmodels)))).exists
  rcases hkmodels with ⟨N, hN, hcenter⟩ | ⟨N, hN, hNC, hx⟩ | ⟨N, hx⟩ | ⟨N, hx⟩
  · obtain ⟨W, hWepsilon, hWconnection, hWcenter, _⟩ := hkneck N hN hcenter
    refine Or.inl ⟨W, hWconnection, hWepsilon, ?_⟩
    rw [hWcenter]
    have hA : (1 : ℝ) ≤ 4 * max 1 C := by linarith [le_max_left (1 : ℝ) C]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hxscalar.le
  · obtain ⟨W, hWepsilon, hWconnection, _, hWscalar, _⟩ := hkcap N hN hNC hx
    exact Or.inl ⟨W, hWconnection, hWepsilon, hWscalar⟩
  · exact Or.inr (hkcomponent (Dsource k) N hx)
  · exact Or.inr (hkround (Dsource k) N hx)

end PoincareConjecture.M47
