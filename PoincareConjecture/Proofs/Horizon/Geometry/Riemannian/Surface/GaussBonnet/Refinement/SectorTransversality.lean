import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.SectorConnectivity

set_option autoImplicit false
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

theorem affineBasis_vector_reconstruction (c : AffineBasis (Fin 3) ℝ Plane) (w : Plane) :
    (c.coord 1).linear w • (c 1 - c 0) +
      (c.coord 2).linear w • (c 2 - c 0) = w := by
  have h := affineBasis_coordinate_reconstruction c (w + c 0)
  have h1 : c.coord 1 (w + c 0) = (c.coord 1).linear w := by
    simpa using (c.coord 1).map_vadd (c 0) w
  have h2 : c.coord 2 (w + c 0) = (c.coord 2).linear w := by
    simpa using (c.coord 2).map_vadd (c 0) w
  rw [h1, h2, add_assoc] at h
  exact add_left_cancel (h.trans (add_comm _ _))

theorem affineBasis_edge_ne_smul (b : AffineBasis (Fin 3) ℝ Plane)
    (i j k : Fin 3) (hji : j ≠ i) (hjk : j ≠ k) (a : ℝ) :
    b j - b i ≠ a • (b k - b i) := by
  intro h
  have he := congrArg (b.coord j).linear h
  have h1 : (b.coord j).linear (b j - b i) = 1 := by
    change (b.coord j).linear (b j -ᵥ b i) = 1
    rw [AffineMap.linearMap_vsub]
    simp [hji]
  have h2 : (b.coord j).linear (b k - b i) = 0 := by
    change (b.coord j).linear (b k -ᵥ b i) = 0
    rw [AffineMap.linearMap_vsub]
    simp [hji, hjk]
  rw [h1, map_smul, h2, smul_zero] at he
  exact one_ne_zero he

theorem affineBasis_second_coord_ne_zero_of_mapped_first_edge
    (b c : AffineBasis (Fin 3) ℝ Plane) (L : Plane →L[ℝ] Plane)
    (hL : Function.Injective L) (i j k : Fin 3) (hji : j ≠ i) (hjk : j ≠ k)
    (w : Plane) (hw : L (b j - b i) = -w)
    (hk : L (b k - b i) = c 1 - c 0) : (c.coord 2).linear w ≠ 0 := by
  intro hz
  have he : w = (c.coord 1).linear w • (c 1 - c 0) := by
    simpa only [hz, zero_smul, add_zero] using (affineBasis_vector_reconstruction c w).symm
  apply affineBasis_edge_ne_smul b i j k hji hjk (-(c.coord 1).linear w)
  apply hL
  rw [map_smul, hw, hk, neg_smul]
  exact congrArg Neg.neg he

theorem affineBasis_first_coord_ne_zero_of_mapped_second_edge
    (b c : AffineBasis (Fin 3) ℝ Plane) (L : Plane →L[ℝ] Plane)
    (hL : Function.Injective L) (i j k : Fin 3) (hji : j ≠ i) (hjk : j ≠ k)
    (w : Plane) (hw : L (b j - b i) = -w)
    (hk : L (b k - b i) = c 2 - c 0) : (c.coord 1).linear w ≠ 0 := by
  intro hz
  have he : w = (c.coord 2).linear w • (c 2 - c 0) := by
    simpa only [hz, zero_smul, zero_add] using (affineBasis_vector_reconstruction c w).symm
  apply affineBasis_edge_ne_smul b i j k hji hjk (-(c.coord 2).linear w)
  apply hL
  rw [map_smul, hw, hk, neg_smul]
  exact congrArg Neg.neg he

end PoincareConjecture.Topology.Surface
