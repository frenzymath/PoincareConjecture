import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.RawChart









set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "V3" => (Fin 3 → ℝ)


theorem RawSourceCrossing.exists_ordered
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {sourceSet : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X} {x y : E}
    (C : RawSourceCrossing e f sourceSet R x y) :
    ∃ D : RawSourceCrossing e f sourceSet R x y, x ∈ D.left ∧ y ∈ D.right := by
  rcases C.labels with h | h
  · exact ⟨C, h⟩
  let L : V3 ≃L[ℝ] V3 :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 3 ↦ ℝ) (Equiv.swap 0 1)
  have hL0 (z : V3) : L z 0 = z 1 := by
    simp [L, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  have hL1 (z : V3) : L z 1 = z 0 := by
    simp [L, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  have hL2 (z : V3) : L z 2 = z 2 := by
    simp [L, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply,
      Equiv.swap_apply_def, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
  let T := C.chart.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hTs : T.source = C.chart.source := by
    ext z
    simp [T]
  have hTv (z : X) : T z = L (C.chart z) := rfl
  have hPL (k : ι) : (e k).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
    let W := (e k).symm.trans C.chart
    have hW : LocallyPiecewiseAffineOn W W.source :=
      (mem_piecewiseAffineGroupoid_iff_forward _).mp (C.compatible k)
    have hcomp := (locallyPiecewiseAffineOn_affine
      L.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp hW
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact hcomp.mono ((e k).symm.trans T).open_source
      (fun z hz ↦ ⟨⟨hz.1, hTs.subset hz.2⟩, mem_univ _⟩)
  refine ⟨{
    chart := T
    left := C.right
    right := C.left
    left_subset := C.right_subset
    right_subset := C.left_subset
    left_open := C.right_open
    right_open := C.left_open
    disjoint := C.disjoint.symm
    labels := Or.inl h
    point := hTs.symm ▸ C.point
    left_embedding := C.right_embedding
    right_embedding := C.left_embedding
    whole_preimage := by rw [hTs, C.whole_preimage, union_comm]
    compatible := hPL
    left_image := by
      intro z hz
      rw [hTv, hL0]
      exact C.right_image z (hTs.subset hz)
    right_image := by
      intro z hz
      rw [hTv, hL1]
      exact C.left_image z (hTs.subset hz)
    region := by
      rcases C.region with hin | hout
      · exact Or.inl (hTs.subset.trans hin)
      · right
        constructor <;> intro z hz <;> rw [hTv, hL2]
        · exact hout.1 z (hTs.subset hz)
        · exact hout.2 z (hTs.subset hz)
  }, h⟩

end PoincareConjecture.M76.Dehn.Annuli
