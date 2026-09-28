import PoincareConjecture.Proofs.M76.Mathlib.PolygonOriginalCutRays
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIncidence

set_option autoImplicit false

open Set Filter AffineMap
open scoped Topology

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem isClosed_cutArc (P : Polygon E n) (t : Fin n → ℝ) (i : Fin n) :
    IsClosed (P.cutArc t i) := by
  change IsClosed ((lineMap (P i) (P (finRotate n i)) '' Icc (t i) 1) ∪
    (lineMap (P (finRotate n i)) (P (finRotate n (finRotate n i))) ''
      Icc 0 (t (finRotate n i))))
  exact ((isCompact_Icc.image (ContinuousAffineMap.lineMap (P i)
    (P (finRotate n i))).continuous).union
      (isCompact_Icc.image (ContinuousAffineMap.lineMap (P (finRotate n i))
        (P (finRotate n (finRotate n i)))).continuous)).isClosed

theorem eventually_boundary_iff_original_cut_segments
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (i : Fin (n + 3)) :
    ∀ᶠ x in 𝓝 (P (finRotate (n + 3) i)), x ∈ P.boundary ℝ ↔
      x ∈ segment ℝ (P (finRotate (n + 3) i)) (P.edgeCut t i) ∪
        segment ℝ (P (finRotate (n + 3) i)) (P.edgeCut t (finRotate (n + 3) i)) := by
  have hlocal (k : Fin (n + 3)) :
      ∀ᶠ x in 𝓝 (P (finRotate (n + 3) i)), x ∈ P.cutArc t k → k = i := by
    by_cases hki : k = i
    · exact Eventually.of_forall fun _ _ => hki
    · have hnot : P (finRotate (n + 3) i) ∉ P.cutArc t k := by
        intro h
        have hnext := (P.vertex_mem_cutArc_iff hP hinj t ht (finRotate (n + 3) i) k).mp h
        exact hki ((finRotate (n + 3)).injective hnext).symm
      filter_upwards [(P.isClosed_cutArc t k).isOpen_compl.mem_nhds hnot] with x hx
      exact fun h => (hx h).elim
  have htc (k : Fin (n + 3)) : t k ∈ Icc (0 : ℝ) 1 := ⟨(ht k).1.le, (ht k).2.le⟩
  have hcover := P.iUnion_cutArc t htc
  filter_upwards [Filter.eventually_all.mpr hlocal] with x hx
  have hiff : x ∈ P.boundary ℝ ↔ x ∈ P.cutArc t i := by
    constructor
    · intro h
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover.symm.subset h)
      exact (hx k hk) ▸ hk
    · intro h
      exact hcover.subset (mem_iUnion.mpr ⟨i, h⟩)
  rw [hiff, P.cutArc_eq_segments t htc i,
    segment_symm ℝ (P.edgeCut t i) (P (finRotate (n + 3) i))]

end Polygon

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {n : ℕ}

theorem original_cut_link_zero_data
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (A : E →ₗ[ℝ] ℝ)
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P)
    (hsection : P.boundary ℝ = K.space ∩ {x | A x = 0})
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (i : Fin (n + 3)) (hvertex : P (finRotate (n + 3) i) = 0) :
    (NormedSpace.normalize '' ((K.link 0).space ∩ {x | A x = 0}) =
      {NormedSpace.normalize (P.edgeCut t i),
        NormedSpace.normalize (P.edgeCut t (finRotate (n + 3) i))}) ∧
      ((K.link 0).space ∩ {x | A x = 0}).ncard = 2 := by
  have hnonzero (k : Fin (n + 3)) : P.edgeCut t k ≠ 0 := by
    intro h
    exact P.edgeCut_notMem_range hP hinj t (ht k)
      ⟨finRotate (n + 3) i, hvertex.trans h.symm⟩
  have hlocal : ∀ᶠ x in 𝓝 (0 : E), x ∈ K.space ∩ {x | A x = 0} ↔
      x ∈ segment ℝ 0 (P.edgeCut t i) ∪
        segment ℝ 0 (P.edgeCut t (finRotate (n + 3) i)) := by
    simpa only [hvertex, hsection] using
      P.eventually_boundary_iff_original_cut_segments hP hinj t ht i
  have hinter : segment ℝ 0 (P.edgeCut t i) ∩
      segment ℝ 0 (P.edgeCut t (finRotate (n + 3) i)) ⊆ {0} := by
    have h := P.adjacent_cut_segments_inter hP hinj t
      (fun k => ⟨(ht k).1.le, (ht k).2.le⟩) i
    rw [hvertex] at h
    exact h.subset
  exact ⟨K.normalize_image_link_zero_of_local_segments hK hzero A
    (hnonzero i) (hnonzero (finRotate (n + 3) i)) hlocal,
    K.ncard_link_zero_of_local_segments hK hzero A
      (hnonzero i) (hnonzero (finRotate (n + 3) i)) hinter hlocal⟩

end Geometry.SimplicialComplex
