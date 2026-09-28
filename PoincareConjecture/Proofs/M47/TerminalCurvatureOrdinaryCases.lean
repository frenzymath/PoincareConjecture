import PoincareConjecture.Proofs.M47.TerminalCurvatureSourceCases
import PoincareConjecture.Definitions.Ch15.SurgeryFlow









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_readout_of_ordinary_source_canonical
    {ι : Type*} (S : ℕ → GeneralizedSliceCarrier.{u}) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow 3 (S k).carrier (J k)) (t : ℕ → ℝ)
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
        (((F k).metric (t k)).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) (hxscalar : 0 < D.scalarCurvature x)
    (hballs : ∀ R : ℝ, 0 < R → ∃ j, ∀ᶠ k in atTop,
      ((F k).metric (t k)).ball (phi k x) R ⊆ phi k '' U j)
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hroundSmall : epsilon ≤ 1 / 200) (hC : 0 < C)
    (hcanonical : ∀ᶠ k in atTop,
      SurgeryOrdinaryCanonicalControl (S k) (F k) (t k) (phi k x) epsilon C) :
    (∃ W : EpsilonNeck h, W.connection = D ∧ W.epsilon = 2 * epsilon ∧
      D.scalarCurvature x ≤ (4 * max 1 C) * D.scalarCurvature W.center) ∨
        IsCompact (univ : Set X) := by
  apply terminalCurvature_readout_of_source_cases
    (fun k => (F k).metric (t k)) h D (fun k => (F k).connection (t k))
    U hU hmono hcoverU hcompact p hp phi hsource c hcoverC hjet x hxscalar hballs
      hepsilon hsmall hroundSmall hC
  filter_upwards [hcanonical] with k hk
  cases hk with
  | neck N hx => exact Or.inl ⟨N.neck, N.epsilon_eq, hx⟩
  | cap N he hNC _ hx => exact Or.inr (Or.inl ⟨N, he, hNC, hx⟩)
  | component N hx => exact Or.inr (Or.inr (Or.inl ⟨N, hx⟩))
  | round N hx => exact Or.inr (Or.inr (Or.inr ⟨N, hx⟩))

end PoincareConjecture.M47
