import PoincareConjecture.Proofs.M76.Rigidity.OriginalEdgeNormalHalves
import PoincareConjecture.Proofs.M76.Rigidity.OriginalTriangleCofaceSigns









set_option autoImplicit false

open Set Geometry SignType

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)




theorem sign_eq_on_edge_dualRegion
    (p q : (T.marked 2).vertices) {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 2)
    (hps : (p : T.index → ℝ × V3) ∈ s) (hqs : (q : T.index → ℝ × V3) ∈ s) :
    EqOn (fun x => sign (T.height p x)) (fun x => sign (T.height q x))
      (T.dualRegion s) := by
  obtain ⟨hn, hp, t, ht, u, hu, v, hv, hst, htc, htu, htv,
    huc, hvc, huRim, hvRim, hun, hvp⟩ := T.exists_edge_normal_halves p hps hs hscard
  have hball := T.edge_region_ball p hps hs hscard
  have huHull : u.centroid ℝ id ∈ convexHull ℝ (u : Set (T.index → ℝ × V3)) :=
    u.centroid_mem_convexHull (T.ambient.nonempty_of_mem_faces hu)
  have hvHull : v.centroid ℝ id ∈ convexHull ℝ (v : Set (T.index → ℝ × V3)) :=
    v.centroid_mem_convexHull (T.ambient.nonempty_of_mem_faces hv)
  have heu : sign (T.height p (u.centroid ℝ id)) =
      sign (T.height q (u.centroid ℝ id)) :=
    T.sign_eq_on_triangle_coface p q ht htc (hst hps) (hst hqs) hu huc htu huHull
  have hev : sign (T.height p (v.centroid ℝ id)) =
      sign (T.height q (v.centroid ℝ id)) :=
    T.sign_eq_on_triangle_coface p q ht htc (hst hps) (hst hqs) hv hvc htv hvHull
  have hqu : T.height q (u.centroid ℝ id) < 0 :=
    sign_eq_neg_one_iff.mp (heu.symm.trans (sign_eq_neg_one_iff.mpr hun))
  have hqv : 0 < T.height q (v.centroid ℝ id) :=
    sign_eq_one_iff.mp (hev.symm.trans (sign_eq_one_iff.mpr hvp))
  have hpos : MapsTo (T.height q)
      (T.dualRegion s ∩ {x | 0 ≤ T.height p x}) (Ici 0) := by
    apply hp.mapsTo_nonneg_of_zeros_in_boundary (T.height q)
      ((T.continuousOn_height_dualRegion q hqs).mono inter_subset_left)
    · intro x hx
      exact Or.inl ⟨hx.1.1,
        (T.height_eq_zero_iff_on_dualRegion q hqs hx.1.1).mp hx.2⟩
    · exact ⟨v.centroid ℝ id, ⟨hball.1 hvRim, hvp.le⟩, hqv⟩
  have hneg : MapsTo (T.height q)
      (T.dualRegion s ∩ {x | T.height p x ≤ 0}) (Iic 0) := by
    apply hn.mapsTo_nonpos_of_zeros_in_boundary (T.height q)
      ((T.continuousOn_height_dualRegion q hqs).mono inter_subset_left)
    · intro x hx
      exact Or.inr ⟨hx.1.1,
        (T.height_eq_zero_iff_on_dualRegion q hqs hx.1.1).mp hx.2⟩
    · exact ⟨u.centroid ℝ id, ⟨hball.1 huRim, hun.le⟩, hqu⟩
  intro x hx
  change sign (T.height p x) = sign (T.height q x)
  have hzero : T.height p x = 0 ↔ T.height q x = 0 :=
    (T.height_eq_zero_iff_on_dualRegion p hps hx).trans
      (T.height_eq_zero_iff_on_dualRegion q hqs hx).symm
  rcases lt_trichotomy (T.height p x) 0 with hlt | heq | hgt
  · have hqne : T.height q x ≠ 0 := fun h => (ne_of_lt hlt) (hzero.mpr h)
    have hqlt : T.height q x < 0 := lt_of_le_of_ne (hneg ⟨hx, hlt.le⟩) hqne
    exact (sign_eq_neg_one_iff.mpr hlt).trans (sign_eq_neg_one_iff.mpr hqlt).symm
  · rw [heq, hzero.mp heq]
  · have hqne : T.height q x ≠ 0 := fun h => (ne_of_gt hgt) (hzero.mpr h)
    have hqgt : 0 < T.height q x :=
      lt_of_le_of_ne (hpos ⟨hx, hgt.le⟩) (Ne.symm hqne)
    exact (sign_eq_one_iff.mpr hgt).trans (sign_eq_one_iff.mpr hqgt).symm

end PoincareConjecture.M76.OriginalProperDiskTriangulation
