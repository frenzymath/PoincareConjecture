import PoincareConjecture.Proofs.M47.TerminalCurvatureScaledSourceCap
import PoincareConjecture.Proofs.M47.TerminalCurvatureScaledCompact
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourceNeck
import PoincareConjecture.Definitions.Ch15.SurgeryFlow










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem terminalCurvature_readout_of_physical_source_canonical
    {ι : Type*} (S : ℕ → GeneralizedSliceCarrier.{u}) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow 3 (S k).carrier (J k)) (t Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X] [ConnectedSpace X]
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcoverU : (⋃ k, U k) = univ) (hcompact : ∀ j, IsCompact (closure (U j)))
    (p : X) (hp : ∀ j, p ∈ U j)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (S k).carrier ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i j K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j
        ((rescaledMetric ((F k).metric (t k)) (Q k) (hQ k)).pullbackCoefficients
          (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) (hxscalar : 0 < D.scalarCurvature x)
    (hballs : ∀ R : ℝ, 0 < R → ∃ j, ∀ᶠ k in atTop,
      (rescaledMetric ((F k).metric (t k)) (Q k) (hQ k)).ball (phi k x) R ⊆ phi k '' U j)
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hroundSmall : epsilon ≤ 1 / 200) (hC : 0 < C)
    (hcanonical : ∀ᶠ k in atTop,
      SurgeryOrdinaryCanonicalControl (S k) (F k) (t k) (phi k x) epsilon C) :
    (∃ W : EpsilonNeck h, W.connection = D ∧ W.epsilon = 2 * epsilon ∧
      D.scalarCurvature x ≤ (4 * max 1 C) * D.scalarCurvature W.center) ∨
        IsCompact (univ : Set X) := by
  let g := fun k => (F k).metric (t k)
  let gQ := fun k => rescaledMetric (g k) (Q k) (hQ k)
  have hneck := terminalCurvature_eventually_source_neck_readout
    gQ h D U hU hmono hcoverU hcompact p hp phi hsource c hcoverC hjet x hxscalar hballs
      hepsilon hsmall
  have hcap := terminalCurvature_eventually_scaled_source_cap_readout
    g Q hQ h D U hU hmono hcoverU hcompact p hp phi hsource c hcoverC hjet
      x hxscalar hballs hepsilon hsmall hC
  have hcomponent := terminalCurvature_eventually_compact_of_scaled_source_component
    g Q hQ h D U hU hmono hcoverU phi hsource c hcoverC hjet x hxscalar hballs hC
  have hround := terminalCurvature_eventually_compact_of_scaled_source_round
    g Q hQ h D U hU hmono hcoverU phi hsource c hcoverC hjet x hxscalar hballs hroundSmall
  obtain ⟨k, hkneck, hkcap, hkcomponent, hkround, hkcanonical⟩ :=
    (hneck.and (hcap.and (hcomponent.and (hround.and hcanonical)))).exists
  cases hkcanonical with
  | neck N hx =>
      obtain ⟨W, hWepsilon, hWconnection, hWcenter, _⟩ :=
        hkneck (N.neck.rescale (Q k) (hQ k)) N.epsilon_eq hx
      refine Or.inl ⟨W, hWconnection, hWepsilon, ?_⟩
      rw [hWcenter]
      have hA : (1 : ℝ) ≤ 4 * max 1 C := by linarith [le_max_left (1 : ℝ) C]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hxscalar.le
  | cap N he hNC _ hx =>
      obtain ⟨W, hWepsilon, hWconnection, _, hWscalar, _⟩ := hkcap N he hNC hx
      exact Or.inl ⟨W, hWconnection, hWepsilon, hWscalar⟩
  | component N hx => exact Or.inr (hkcomponent ((F k).connection (t k)) N hx)
  | round N hx => exact Or.inr (hkround ((F k).connection (t k)) N hx)

end PoincareConjecture.M47
