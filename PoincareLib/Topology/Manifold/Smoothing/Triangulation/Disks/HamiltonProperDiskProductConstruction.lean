import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskLowerProductConstruction
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskVertexAssembly
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonUnmarkedProductGluing

/-!
# The actual proper-disk product on the retained triangulation

Construct the coherent sides, every lower-face product and every
vertex extension, then glue using their exact full overlap images.
The whole original disk parameter and its physical frontier remain
unchanged. See Hudson1969, pp.15--19,58--63 and M76 derivations351,358.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

/-- The same retained triangulation supplies an actual joint finite
PL product of the whole proper disk. Its complete zero section is b
and its full physical frontier preimage is the original disk rim.
Every internal side and product record is constructed. See351,358. -/
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

end PoincareMT.M76.HamiltonIndexOne
