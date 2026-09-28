import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskLowerProductConstruction
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexAssembly
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnmarkedProductGluing

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

theorem HamiltonProperDiskTriangulation.exists_unmarked_disk_product
    (T : HamiltonProperDiskTriangulation R D b) (h3 : Module.finrank ℝ E = 3)
    (hb : b.IsFinitePL)
    (hproper : ∀ x : closedBall (0 : V2) 1,
      (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1) :
    Nonempty (HamiltonUnmarkedDiskProduct R b) := by
  let c : E ≃ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousLinearEquiv.ofFinrankEq (by simp [h3, Module.finrank_prod])).toContinuousAffineEquiv
  obtain ⟨C⟩ := T.exists_coherent_sides hb hproper c
  obtain ⟨P⟩ := C.exists_lower_products h3 hproper
  obtain ⟨V⟩ := P.exists_vertex_products hproper
  exact V.exists_unmarked_disk_product hb hproper

end PoincareConjecture.M76.HamiltonIndexOne
