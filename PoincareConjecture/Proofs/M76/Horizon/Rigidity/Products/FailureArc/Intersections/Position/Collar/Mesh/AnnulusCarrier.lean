import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.SourceGeometry
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusOpenChart
import Mathlib.Topology.Instances.AddCircle.Real



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn.Annuli
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem isPreconnected_planar_annulus_without_frontier :
    IsPreconnected (Ann \ frontier Ann) := by
  let : PreconnectedSpace (Ioo (-1 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hmap : Continuous (fun p : Circle × Ioo (-1 : ℝ) 1 =>
      annulusMap 8 (by norm_num) (p.1, p.2)) :=
    (isOpenEmbedding_annulusMap_open (L := 8) (d := 1)
      (by norm_num) (by norm_num) (by norm_num)).continuous
  have hpre := isPreconnected_range hmap
  rw [range_annulusMap_open (by norm_num) (by norm_num) (by norm_num)] at hpre
  have heq : Ann \ frontier Ann = depth 8 ⁻¹' Ioo (-1) 1 := by
    ext x
    change (x ∈ Ann ∧ x ∉ frontier Ann) ↔ -1 < depth 8 x ∧ depth 8 x < 1
    rw [mem_squareAnnulus_iff_depth, mem_frontier_planar_annulus_iff]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hne⟩
      exact ⟨lt_of_le_of_ne hlo (fun h => hne (Or.inl h.symm)),
        lt_of_le_of_ne hhi (fun h => hne (Or.inr h))⟩
    · rintro ⟨hlo, hhi⟩
      exact ⟨⟨hlo.le, hhi.le⟩, fun h => h.elim
        (fun hh => hlo.ne' hh) (fun hh => hhi.ne hh)⟩
  exact heq.symm ▸ hpre

theorem exists_connected_planar_annulus_carrier :
    ∃ K : SimplicialComplex ℝ (ℝ × ℝ),
      K.faces.Finite ∧ K.space = Ann ∧ IsPreconnected (K.space \ frontier Ann) := by
  obtain ⟨K, hK, hKs⟩ := exists_planar_annulus_complex
  exact ⟨K, hK, hKs, hKs.symm ▸ isPreconnected_planar_annulus_without_frontier⟩

end PoincareConjecture.M76
