import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductSlices
import PoincareConjecture.Proofs.M76.Rigidity.SourceDiskPairCharts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.exists_slice_pair_chart (P : OriginalDiskProduct e R j)
    (he : PLDomain e R) {t : ℝ} (ht : t ∈ I) (z : D) :
    ∃ H : OpenPartialHomeomorph X C3,
      P.slice t z ∈ H.source ∧ H.target = interior (CoordinateHalfBoxes.box 1) ∧
      H (P.slice t z) = 0 ∧
      (∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source ∧
        LocallyPiecewiseAffineOn (H.symm.trans (e i)) (H.symm.trans (e i)).source) ∧
      ((H.source ⊆ interior R ∧
        ∀ x ∈ H.source, x ∈ P.slice t '' D ↔ (H x).2 = 0) ∨
       ((∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1) ∧
        ∀ x ∈ H.source, x ∈ P.slice t '' D ↔ 0 ≤ (H x).1.1 ∧ (H x).2 = 0)) :=
  exists_original_proper_disk_pair_chart he (P.polyhedral_slice ht) (P.embedding_slice ht)
    (P.slice_inside ht) (P.slice_proper ht) z

end PoincareConjecture.M76
