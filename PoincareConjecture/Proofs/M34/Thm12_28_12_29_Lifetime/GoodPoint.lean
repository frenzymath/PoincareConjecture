import PoincareConjecture.Definitions.M30ControlledBlowupLimits











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M34



structure Chapter11GoodPoint (G : GeneralizedRicciFlowData.{u})
    (epsilon C A : ℝ) (p : G.point) : Prop where
  canonical : Nonempty (GeneralizedCanonicalControl (F := G) p.1 p.2 epsilon C)
  scalar_gradient : ∀ v : TangentSpace (𝓡 3) p.2, (G.metric p.1).inner p.2 v v = 1 →
    |mvfderiv (𝓡 3) (G.connection p.1).scalarCurvature p.2 v| ≤
      A * (G.scalar p) ^ (3 / 2 : ℝ)
  scalar_time_derivative : ∀ b (ht : p.1 ∈ (G.box b).interval)
    (x : (G.box b).carrier.carrier), (G.box b).forward p.1 ht x = p.2 →
      ∃ d : ℝ, HasDerivWithinAt (fun s => ((G.box b).flow.connection s).scalarCurvature x)
        d (G.box b).interval p.1 ∧
          |d| ≤ A * (((G.box b).flow.connection p.1).scalarCurvature x) ^ 2



theorem chapter11GoodPoint_earlier_canonical
    {G : GeneralizedRicciFlowData.{u}} {epsilon C A : ℝ} (p : G.point)
    (hgood : ∀ q : G.point, q.1 ≤ p.1 → 4 * G.scalar p ≤ G.scalar q →
      Chapter11GoodPoint G epsilon C A q) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods G epsilon C p.1 p.2 := by
  apply generalizedEarlierStrongCanonicalNeighborhoods.left_dense
  intro t _ ht x hx
  exact (hgood ⟨t, x⟩ ht hx).canonical

end PoincareConjecture.M34
