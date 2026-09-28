import PoincareConjecture.Proofs.M47.TerminalCurvatureCapCaptureAssembly
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourcePointScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_eventually_source_cap_readout
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
    [∀ k, MeasurableSpace (M k)] [∀ k, BorelSpace (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X] [T3Space X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (h : RiemannianMetric 3 X)
    (D : LeviCivitaData h)
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
    (hC : 0 < C) :
    ∀ᶠ k in atTop, ∀ N : CapCertificate (g k), N.epsilon = epsilon →
      N.cap_constant ≤ C → phi k x ∈ N.core →
      ∃ W : EpsilonNeck h,
        W.epsilon = 2 * epsilon ∧ W.connection = D ∧
        W.center = (phi k).symm N.end_neck.center ∧
        D.scalarCurvature x ≤ (4 * max 1 C) * D.scalarCurvature W.center ∧
        W.coordinate_map = (phi k).symm ∘ N.end_neck.coordinate_map := by
  have hcap := terminalCurvature_eventually_cap_readout_of_source_balls
    g h D U hU hmono hcoverU hcompact p hp phi hsource c hcoverC hjet x hballs
      hepsilon hsmall hC (half_pos hxscalar) (J := D.scalarCurvature x + 1)
  have heta : 0 < min (D.scalarCurvature x / 2) 1 :=
    lt_min (half_pos hxscalar) zero_lt_one
  have hscalar := terminalCurvature_eventually_source_point_scalar
    g h D U hU hmono hcoverU phi hsource c hcoverC hjet x heta
  filter_upwards [hcap, hscalar] with k hkcap hkscalar N hN hNC hx
  have herr := abs_lt.mp (hkscalar N.connection)
  have hhalf := min_le_left (D.scalarCurvature x / 2) (1 : ℝ)
  have hone := min_le_right (D.scalarCurvature x / 2) (1 : ℝ)
  exact hkcap N hN hNC hx (by linarith [herr.1]) (by linarith [herr.2])

end PoincareConjecture.M47
