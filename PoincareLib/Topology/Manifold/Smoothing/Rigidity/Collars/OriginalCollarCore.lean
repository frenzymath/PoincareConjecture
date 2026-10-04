import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.Mathlib.CompactCollarCore
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Spheres.OriginalSphereConnected
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.MeridianBicollar
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The original finite PL collar constructs its whole connected core

The actual frontier sphere supplies connectedness of the cut and
nonemptiness of the finite base. The original product certificate
supplies every continuity and image hypothesis of the core theorem.
The fixed lattice ambient has its actual connected topology. See045.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {K : Set X}

/-- The same original finite collar and full sphere construct the
literal compact core, all ambient boundary identities and a whole
continuous retraction. No core connectedness is supplied. See045. -/
theorem ChartwisePLSphere.collar_core (sph : ChartwisePLSphere e (frontier K))
    (hK : IsCompact K) (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ frontier K) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hinside : MapsTo c (L.space ×ˢ I) K)
    (hbase : ∀ z : L.space, c ((z : E), 0) = HB z)
    (hproper : ∀ z : (L.space ×ˢ I : Set (E × ℝ)),
      c z ∈ frontier K ↔ (z : E × ℝ).2 = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 2)
    (hopen : ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      IsOpen ((Subtype.val : K → X) ⁻¹' (c '' (L.space ×ˢ Ico 0 ε)))) :
    IsCompact (K \ (c '' (L.space ×ˢ Ico 0 (δ / 2)))) ∧
      IsConnected (K \ (c '' (L.space ×ˢ Ico 0 (δ / 2)))) ∧
      interior (K \ (c '' (L.space ×ˢ Ico 0 (δ / 2)))) =
        interior K \ (c '' (L.space ×ˢ Icc 0 (δ / 2))) ∧
      frontier (K \ (c '' (L.space ×ˢ Ico 0 (δ / 2)))) = c '' (L.space ×ˢ {δ / 2}) ∧
      K \ (c '' (L.space ×ˢ Ico 0 (δ / 2))) ⊆ interior K ∧
      (c '' (L.space ×ˢ Icc 0 (δ / 2))) ∩
        (K \ (c '' (L.space ×ˢ Ico 0 (δ / 2)))) = c '' (L.space ×ˢ {δ / 2}) ∧
      (c '' (L.space ×ˢ Icc 0 (δ / 2))) ∪
        (K \ (c '' (L.space ×ˢ Ico 0 (δ / 2)))) = K ∧
      (interior (K \ (c '' (L.space ×ˢ Ico 0 (δ / 2))))).Nonempty ∧
      ∃ r : K → X, Continuous r ∧ range r = K \ (c '' (L.space ×ˢ Ico 0 (δ / 2))) ∧
        ∀ x : K, (x : X) ∈ K \ (c '' (L.space ×ˢ Ico 0 (δ / 2))) → r x = x := by
  obtain ⟨x, hx⟩ := sph.isConnected.nonempty
  have hLne : L.space.Nonempty :=
    ⟨HB.symm ⟨x, hx⟩, (HB.symm ⟨x, hx⟩).property⟩
  exact compact_collar_core (δ := δ) hK (sph.isConnected_region hK)
    (L.isCompact_space_of_finite hL) hLne HB c hc.continuousOn hi hinside hbase hproper
    (half_pos hδ) (by linarith) (by linarith) (hopen (δ / 2) (half_pos hδ) (by linarith))

/-- The literal fixed-period ambient space is connected by its
actual circle comparison and the vector-space factor. See045, section1. -/
theorem connectedSpace_hamiltonSolidTorusAmbient :
    ConnectedSpace (LatticeHandleAmbient (Fin 2) (Fin 1)
      (hamiltonLowerPeriodLattice (Fin 1))) := by
  let : ConnectedSpace ((Fin 1 → ℝ) ⧸
      Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))) :=
    hamiltonSolidTorusCircleEquiv.connectedSpace_iff.mpr inferInstance
  change ConnectedSpace (V2 × ((Fin 1 → ℝ) ⧸
    Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))))
  infer_instance

end PoincareMT.M76
