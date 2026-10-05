import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.OriginalChartBall
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Collars.ProtectedBoundaryCollar

/-!
# The actual full boundary collar from an original interior point

The original chart constructs the protected ball required by the
checked collar producer. Both constructions retain the same domain
and original atlas. See rigidity053, sections4--5.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in
/-- An actual original PL domain with an interior point constructs
its whole small boundary collar. The protected ball is derived in
an original chart, not supplied as a premise. See053, sections4--5. -/
theorem PLDomain.exists_small_boundary_collar_of_interior_nonempty
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hne : (interior R).Nonempty)
    (hU : IsOpen U) (hBU : frontier R ⊆ U) :
    ∃ (s : Finset R) (L : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : L.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → X),
      L.faces.Finite ∧ PolyhedralPLInCharts e c (L.space ×ˢ Icc (0 : ℝ) 1) ∧
      Topology.IsEmbedding
        (fun z : (L.space ×ˢ Icc (0 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)) => c z) ∧
      MapsTo c (L.space ×ˢ Icc (0 : ℝ) 1) R ∧
      (∀ x : L.space, c ((x : s → ℝ × V3), 0) = HB x) ∧
      (∀ z : (L.space ×ˢ Icc (0 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)),
        c z ∈ frontier R ↔ (z : (s → ℝ × V3) × ℝ).2 = 0) ∧
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 2 ∧
        MapsTo c (L.space ×ˢ Icc 0 delta) U ∧
        ∀ eps : ℝ, 0 < eps → eps ≤ delta →
          IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (L.space ×ˢ Ico 0 eps))) := by
  obtain ⟨D, _, hDR, ⟨b⟩⟩ := he.exists_ball_in_interior hne
  exact exists_protected_small_boundary_collar hR he
    (hDR.trans interior_subset) b hU hBU

end PoincareMT.M76
