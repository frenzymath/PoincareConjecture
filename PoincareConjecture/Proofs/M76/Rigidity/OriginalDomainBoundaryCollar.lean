import PoincareConjecture.Proofs.M76.Rigidity.OriginalChartBall
import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedBoundaryCollar

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in

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

end PoincareConjecture.M76
