import PoincareConjecture.Proofs.M76.Rigidity.FixedDiskPairProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.NormalProductUnits
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1




theorem exists_original_proper_disk_normal_units
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) {j : V2 → X}
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q) :
    ∃ (H : D → OpenPartialHomeomorph X C3)
      (q : D → OpenPartialHomeomorph (D × ℝ) R) (a : D → D → SignTypeˣ),
      (∀ z,
        j z ∈ (H z).source ∧ (H z).target = interior (CoordinateHalfBoxes.box 1) ∧
        H z (j z) = 0 ∧
        (∀ i,
          LocallyPiecewiseAffineOn ((e i).symm.trans (H z)) ((e i).symm.trans (H z)).source ∧
          LocallyPiecewiseAffineOn ((H z).symm.trans (e i)) ((H z).symm.trans (e i)).source) ∧
        (((H z).source ⊆ interior R ∧
          ∀ x ∈ (H z).source, x ∈ j '' D ↔ (H z x).2 = 0) ∨
         ((∀ x ∈ (H z).source, x ∈ R ↔ 0 ≤ (H z x).1.1) ∧
          ∀ x ∈ (H z).source, x ∈ j '' D ↔ 0 ≤ (H z x).1.1 ∧ (H z x).2 = 0)) ∧
        (z, (0 : ℝ)) ∈ (q z).source ∧
        (q z).target ⊆ (Subtype.val : R → X) ⁻¹' (H z).source ∧
        (∀ s, (s, (0 : ℝ)) ∈ (q z).source → (q z (s, 0) : X) = j s) ∧
        (∀ w ∈ (q z).source, (H z (q z w : X)).2 = w.2) ∧
        ∀ w ∈ (q z).source, (q z w : X) ∈ j '' D ↔ w.2 = 0) ∧
      (∀ z, ContinuousOn (a z) {s | (s, (0 : ℝ)) ∈ (q z).source}) ∧
      ∀ i k z, (z, (0 : ℝ)) ∈ (q i).source → (z, (0 : ℝ)) ∈ (q k).source →
        BrownCollar.NormalSignAt ((q i).trans (q k).symm) z
          ((a k z : SignType) * (a i z : SignType)) := by
  choose H hHpoint hHtarget hHz hHcompat hHmodel using
    fun z : D => exists_original_proper_disk_pair_chart he hj hemb hDR hproper z
  choose q hqpoint hqH hqzero hqnormal hqpair using fun z : D =>
    exists_disk_parameter_product_of_pair_chart hemb hDR (H z) (hHmodel z) z (hHpoint z)
  let : Nonempty D := ⟨⟨0, mem_closedBall_self zero_le_one⟩⟩
  let : LocallyPathConnectedSpace D := (convex_closedBall (0 : V2) 1).locallyPathConnectedSpace
  let : ContractibleSpace D := (convex_closedBall (0 : V2) 1).contractibleSpace
    ⟨0, mem_closedBall_self zero_le_one⟩
  let b : D → R := fun z => ⟨j z, hDR z.property⟩
  let S : Set R := (Subtype.val : R → X) ⁻¹' (j '' D)
  have hzero (i z : D) (hz : (z, (0 : ℝ)) ∈ (q i).source) : q i (z, 0) = b z :=
    Subtype.ext (hqzero i z hz)
  obtain ⟨a, hac, ha⟩ := BrownCollar.exists_coherent_normal_product_units
    q b S hzero hqpair (fun z => ⟨z, hqpoint z⟩)
  refine ⟨H, q, a, ?_, hac, ha⟩
  intro z
  exact ⟨hHpoint z, hHtarget z, hHz z, hHcompat z, hHmodel z,
    hqpoint z, hqH z, hqzero z, hqnormal z, hqpair z⟩

end PoincareConjecture.M76
