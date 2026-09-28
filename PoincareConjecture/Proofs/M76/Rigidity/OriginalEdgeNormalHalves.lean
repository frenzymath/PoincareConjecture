import PoincareConjecture.Proofs.M76.Rigidity.OriginalEdgeNormalWitnesses
import PoincareConjecture.Proofs.M76.Rigidity.OriginalEdgeZeroArcs
import PoincareConjecture.Proofs.M76.Rigidity.OriginalEdgeRegion

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

theorem exists_edge_normal_halves
    (p : (T.marked 2).vertices) {s : Finset (T.index → ℝ × V3)}
    (hps : (p : T.index → ℝ × V3) ∈ s) (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 2) :
    IsFinitePLBallPair (ℝ × ℝ) (T.dualRegion s ∩ {x | T.height p x ≤ 0})
        ((T.dualRegionRim s ∩ {x | T.height p x ≤ 0}) ∪
          (T.dualRegion s ∩ (T.marked 2).space)) ∧
      IsFinitePLBallPair (ℝ × ℝ) (T.dualRegion s ∩ {x | 0 ≤ T.height p x})
        ((T.dualRegion s ∩ (T.marked 2).space) ∪
          (T.dualRegionRim s ∩ {x | 0 ≤ T.height p x})) ∧
      ∃ t ∈ (T.marked 2).faces, ∃ u ∈ T.ambient.faces, ∃ v ∈ T.ambient.faces,
        s ⊆ t ∧ t.card = 3 ∧ t ⊆ u ∧ t ⊆ v ∧ u.card = 4 ∧ v.card = 4 ∧
        u.centroid ℝ id ∈ T.dualRegionRim s ∧
        v.centroid ℝ id ∈ T.dualRegionRim s ∧
        T.height p (u.centroid ℝ id) < 0 ∧ 0 < T.height p (v.centroid ℝ id) := by
  have hball := T.edge_region_ball p hps hs hscard
  obtain ⟨a, z, haz, hW, hrim⟩ := T.exists_edge_zero_arc hs hscard
  have hzero : T.dualRegion s ∩ {x | T.height p x = 0} =
      T.dualRegion s ∩ (T.marked 2).space := by
    ext x
    exact and_congr_right (fun hx => T.height_eq_zero_iff_on_dualRegion p hps hx)
  have hqzero : T.dualRegionRim s ∩ {x | T.height p x = 0} = {a, z} := by
    calc
      T.dualRegionRim s ∩ {x | T.height p x = 0} =
          T.dualRegionRim s ∩ (T.marked 2).space := by
        ext x
        exact and_congr_right (fun hx =>
          T.height_eq_zero_iff_on_dualRegion p hps (hball.1 hx))
      _ = {a, z} := hrim
  obtain ⟨t, ht, hst, htc⟩ := T.exists_disk_triangle_coface hs
  obtain ⟨u, hu, v, hv, htu, htv, huc, hvc, huRim, hvRim, hun, hvp⟩ :=
    T.exists_edge_normal_witnesses p hps hs hscard ht htc hst
  have hcuts := hball.signed_halves_of_zero_arc (T.height p)
    (T.continuousOn_height_dualRegion p hps) hW haz hzero hqzero
    ⟨u.centroid ℝ id, huRim, hun⟩ ⟨v.centroid ℝ id, hvRim, hvp⟩
  exact ⟨hcuts.1, hcuts.2, t, ht, u, hu, v, hv, hst, htc, htu, htv,
    huc, hvc, huRim, hvRim, hun, hvp⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
