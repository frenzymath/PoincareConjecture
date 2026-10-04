import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data

/-!
# The complete good-point property in the Chapter 12 blow-up argument

Goodness includes both the actual canonical certificate and the two
absolute scalar derivative estimates. The time derivative is taken in
every actual flow-box representation, on its included time domain.
Source: Morgan-Tian Theorem 12.28, pp. 323-324; bad-point selection
derivation, sections 1 and 6.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M34

/-- The geometric and analytic conclusions selected together in the
bad-point argument. All constants precede the spacetime point. -/
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

/-- Earlier good points give the exact left-dense whole-slice canonical
field required by M30, using each included time itself (Theorem 12.28). -/
theorem chapter11GoodPoint_earlier_canonical
    {G : GeneralizedRicciFlowData.{u}} {epsilon C A : ℝ} (p : G.point)
    (hgood : ∀ q : G.point, q.1 ≤ p.1 → 4 * G.scalar p ≤ G.scalar q →
      Chapter11GoodPoint G epsilon C A q) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods G epsilon C p.1 p.2 := by
  apply generalizedEarlierStrongCanonicalNeighborhoods.left_dense
  intro t _ ht x hx
  exact (hgood ⟨t, x⟩ ht hx).canonical

end PoincareMT.M34
