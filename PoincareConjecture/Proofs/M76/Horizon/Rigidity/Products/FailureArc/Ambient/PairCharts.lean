import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Ambient.MetricNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)



theorem OriginalSurfacePairChart.exists_neighborhood_restriction
    {X ι : Type*} [TopologicalSpace X] {N S T : Set X}
    {e : ι → OpenPartialHomeomorph X V3}
    (hN : IsOpen N) (d : ι × N → OpenPartialHomeomorph N V3)
    (hdtarget : ∀ k, (d k).target ⊆ (e k.1).target)
    (hdinv : ∀ k, EqOn ((Subtype.val : N → X) ∘ (d k).symm)
      (e k.1).symm (d k).target)
    (y : N) {b : Bool} (C : OriginalSurfacePairChart e S T y b) :
    ∃ B : OriginalSurfacePairChart d ((Subtype.val : N → X) ⁻¹' S)
        ((Subtype.val : N → X) ⁻¹' T) y b,
      B.coordinates.source ⊆ C.coordinates.source ∧
      (∀ z, B.coordinates z = C.coordinates z) ∧
      ∀ z ∈ B.coordinates.source, (B.chart.symm z : X) = C.chart.symm z := by
  classical
  let : Nonempty N := ⟨y⟩
  let J := hN.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : N → X)
  let A := J.trans C.chart
  have hAv (x : N) : A x = C.chart x := rfl
  have hyA : y ∈ A.source := ⟨mem_univ y, C.center_source⟩
  have hAi (z : V3) (hz : z ∈ A.target) : (A.symm z : X) = C.chart.symm z :=
    J.right_inv hz.2
  let Q := C.coordinates.restr A.target
  have hQs : Q.source = C.coordinates.source ∩ A.target :=
    C.coordinates.restr_source' A.target A.open_target
  have hcompat (k : ι × N) : (d k).symm.trans A ∈ piecewiseAffineGroupoid V3 := by
    have hsub : ((d k).symm.trans A).source ⊆ ((e k.1).symm.trans C.chart).source := by
      intro z hz
      refine ⟨hdtarget k hz.1, ?_⟩
      have hh : ((d k).symm z : X) ∈ C.chart.source := hz.2.2
      rwa [show ((d k).symm z : X) = (e k.1).symm z from hdinv k hz.1] at hh
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    apply (((mem_piecewiseAffineGroupoid_iff_forward _).mp (C.compatible k.1)).mono
      ((d k).symm.trans A).open_source hsub).congr
    intro z hz
    change C.chart ((e k.1).symm z) = C.chart ((d k).symm z : X)
    rw [show ((d k).symm z : X) = (e k.1).symm z from hdinv k hz.1]
  let B : OriginalSurfacePairChart d ((Subtype.val : N → X) ⁻¹' S)
      ((Subtype.val : N → X) ⁻¹' T) y b :=
    { chart := A
      coordinates := Q
      compatible := hcompat
      center_source := hyA
      center_coordinates := hQs.symm.subset ⟨C.center_coordinates, A.map_source hyA⟩
      center_zero := C.center_zero
      source_subset := fun _ hz => (hQs.subset hz).2
      forwardPL := C.forwardPL.mono Q.open_source (fun _ hz => (hQs.subset hz).1)
      inversePL := C.inversePL.mono Q.open_target (fun _ hz => hz.1)
      first_surface := by
        intro z hz
        change (A.symm z : X) ∈ S ↔ _
        rw [hAi z (hQs.subset hz).2]
        exact C.first_surface z (hQs.subset hz).1
      second_surface := by
        intro z hz
        change (A.symm z : X) ∈ T ↔ _
        rw [hAi z (hQs.subset hz).2]
        exact C.second_surface z (hQs.subset hz).1 }
  exact ⟨B, fun _ hz => (hQs.subset hz).1, fun _ => rfl,
    fun z hz => hAi z (hQs.subset hz).2⟩

end PoincareConjecture.M76
