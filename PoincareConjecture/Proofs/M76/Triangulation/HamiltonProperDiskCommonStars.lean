import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskLocalPairCharts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_proper_disk_triangulation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {R D : Set E} {S : Set F} (a : E ≃ᴬ[ℝ] V3)
    (hDomain : PLDomain
      (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) (a '' R))
    (hR : IsCompact R) (hreg : closure (interior R) = R) (hDR : D ⊆ R)
    (b : closedBall (0 : V2) 1 ≃ₜ D) (hb : b.IsFinitePL)
    (hproper : ∀ x : closedBall (0 : V2) 1,
      (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere (0 : V2) 1)
    (e : S ≃ₜ frontier R) (he : e.IsFinitePL) :
    Nonempty (HamiltonProperDiskTriangulation R D b) := by
  obtain ⟨_, ⟨JF, hJF, hfront, _⟩, _⟩ := he.symm
  exact exists_proper_disk_triangulation_of_pair_charts hR hreg hDR b hb JF hJF hfront
    (fun p => exists_proper_disk_pair_chart a hDomain hDR b hb hproper p.property)

end PoincareConjecture.M76.HamiltonIndexOne
