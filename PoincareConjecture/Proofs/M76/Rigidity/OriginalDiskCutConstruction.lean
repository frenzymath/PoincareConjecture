import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSmallDiskProduct









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}




theorem exists_original_disk_cut
    (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    {U : Set X} (hU : IsOpen U) (hDU : j '' D ⊆ U) :
    ∃ P : OriginalDiskProduct e R j,
      MapsTo P.map (D ×ˢ I) U ∧
      IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip) ∧
      IsCompact P.cutCarrier ∧
      interior P.cutCarrier = interior R \ P.closedStrip ∧
      frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = R ∧
      (interior P.cutCarrier).Nonempty := by
  obtain ⟨P, hP, hopen⟩ := exists_small_original_disk_product hR he hj hemb hDR hproper hU hDU
  have hstrip : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip) :=
    (hopen (1 / 2) (by norm_num) (by norm_num)).1
  exact ⟨P, hP, hstrip, P.cut_geometry hR hstrip⟩

end PoincareConjecture.M76
