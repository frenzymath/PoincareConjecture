import PoincareConjecture.Proofs.M47.TerminalCurvatureSourcePointScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Definitions.Ch16.ControlledSurgery










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_eventually_earlier_canonical
    {ι : Type*} (S : ℕ → SurgeryFlowData.{u}) (b t Q r : ℕ → ℝ)
    (hQ : ∀ k, 0 < Q k) (hfloor : ∀ k, (r k)⁻¹ ^ 2 ≤ Q k)
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X ((S k).slice (t k)).carrier ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((rescaledMetric ((S k).metric (t k)) (Q k) (hQ k)).pullbackCoefficients
          (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K)
    (x : X) (hxscalar : 1 < D.scalarCurvature x)
    {epsilon C : ℝ}
    (hEpsilon : ∀ k, (S k).parameters.epsilon = epsilon)
    (hC : ∀ k, (S k).parameters.C = C)
    (hPast : ∀ k, SurgeryCanonicalOn (S k) (Ico 0 (b k)) (r k))
    (htPast : ∀ k, t k ∈ Ico 0 (b k))
    (htDomain : ∀ k, t k ∈ (S k).time_domain) :
    ∀ᶠ k in atTop,
      (r k)⁻¹ ^ 2 ≤ ((S k).connection (t k)).scalarCurvature (phi k x) ∧
      SurgeryCanonicalControl (S k) (t k) (phi k x) epsilon C := by
  have heta : 0 < (D.scalarCurvature x - 1) / 2 := by linarith
  have hscalar := terminalCurvature_eventually_source_point_scalar
    (fun k => rescaledMetric ((S k).metric (t k)) (Q k) (hQ k))
    g D U hU hmono hcover phi hsource c hcoverC hjet x heta
  filter_upwards [hscalar] with k hk
  have herr := hk (rescaledMetric_connection ((S k).metric (t k))
    ((S k).connection (t k)) (Q k) (hQ k))
  rw [rescaledMetric_scalarCurvature] at herr
  have hnormalized : 1 ≤
      ((S k).connection (t k)).scalarCurvature (phi k x) / Q k := by
    rw [div_eq_mul_inv, mul_comm]
    linarith [(abs_lt.mp herr).1]
  have hphysical : Q k ≤ ((S k).connection (t k)).scalarCurvature (phi k x) := by
    simpa only [one_mul] using (le_div_iff₀ (hQ k)).mp hnormalized
  have hthreshold := (hfloor k).trans hphysical
  refine ⟨hthreshold, ?_⟩
  simpa only [hEpsilon k, hC k] using
    hPast k (t k) (htPast k) (htDomain k) (phi k x) hthreshold

end PoincareConjecture.M47
