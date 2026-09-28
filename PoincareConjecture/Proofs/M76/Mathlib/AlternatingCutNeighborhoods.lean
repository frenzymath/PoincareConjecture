import PoincareConjecture.Proofs.M76.Mathlib.AlternatingPolygonCuts
import PoincareConjecture.Proofs.M76.Mathlib.OriginalEndpointCutSelection
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIncidence

set_option autoImplicit false

open Set AffineMap

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

def midpointArcNeighborhoods (U V : Fin n → Set E) : Fin (n * 2) → Set E := fun k =>
  let ij := finProdFinEquiv.symm k
  if ij.2 = 0 then V ij.1 else U (finRotate n ij.1)

theorem midpointArcNeighborhoods_properties (P : Polygon E n)
    (α β : Fin n → ℝ) (hα : ∀ i, α i ∈ Ioo (0 : ℝ) (1 / 2))
    (hβ : ∀ i, β i ∈ Ioo (1 / 2 : ℝ) 1)
    (U V : Fin n → Set E) (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hconv : ∀ i, Convex ℝ (U i)) (hPU : ∀ i, P i ∈ U i)
    (hαU : ∀ i, P.edgeCut α i ∈ U i)
    (hβU : ∀ i, P.edgeCut β i ∈ U (finRotate n i))
    (hsegment : ∀ i, segment ℝ (P.edgeCut α i) (P.edgeCut β i) ⊆ V i) :
    let Q := P.midpointSubdivision
    let τ := midpointCutParameters α β
    let W := midpointArcNeighborhoods U V
    ∀ k, IsOpen (W k) ∧ Q.cutArc τ k ⊆ W k ∧
      Q (finRotate (n * 2) k) ∈ W k ∧
      Q.edgeCut τ k ∈ W k ∩ W ((finRotate (n * 2)).symm k) := by
  let Q := P.midpointSubdivision
  let τ := midpointCutParameters α β
  let W := midpointArcNeighborhoods U V
  have ht (k) : τ k ∈ Icc (0 : ℝ) 1 :=
    ⟨(midpointCutParameters_mem α β hα hβ k).1.le,
      (midpointCutParameters_mem α β hα hβ k).2.le⟩
  have hW (k) : IsOpen (W k) := by
    dsimp only [W, midpointArcNeighborhoods]
    split_ifs
    · exact hV _
    · exact hU _
  have harc (k) : Q.cutArc τ k ⊆ W k := by
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · have hsub : Q.cutArc τ (finProdFinEquiv (i, (0 : Fin 2))) ⊆ V i := by
        rw [P.midpointSubdivision_cutArc_zero α β hα hβ]
        exact hsegment i
      simpa [W, midpointArcNeighborhoods] using hsub
    · have hsub : Q.cutArc τ (finProdFinEquiv (i, (1 : Fin 2))) ⊆
          U (finRotate n i) := by
        rw [Q.cutArc_eq_segments τ ht, midpoint_rotate_one]
        change segment ℝ
            (P.midpointSubdivision.edgeCut (midpointCutParameters α β)
              (finProdFinEquiv (i, (1 : Fin 2))))
            (P.midpointSubdivision (finProdFinEquiv (finRotate n i, (0 : Fin 2)))) ∪
          segment ℝ (P.midpointSubdivision (finProdFinEquiv (finRotate n i, (0 : Fin 2))))
            (P.midpointSubdivision.edgeCut (midpointCutParameters α β)
              (finProdFinEquiv (finRotate n i, (0 : Fin 2)))) ⊆ _
        rw [midpointSubdivision_edgeCut_one, midpointSubdivision_apply_zero,
          midpointSubdivision_edgeCut_zero]
        exact union_subset ((hconv _).segment_subset (hβU i) (hPU _))
          ((hconv _).segment_subset (hPU _) (hαU _))
      simpa [W, midpointArcNeighborhoods] using hsub
  dsimp only
  intro k
  refine ⟨hW k, harc k, ?_, ?_, ?_⟩
  · apply harc k
    rw [Q.cutArc_eq_segments τ ht]
    exact Or.inl (right_mem_segment ℝ _ _)
  · exact harc k (Q.cutArc_endpoints_subset τ ht k (Or.inl rfl))
  · apply harc ((finRotate (n * 2)).symm k)
    have hend := Q.cutArc_endpoints_subset τ ht ((finRotate (n * 2)).symm k)
    apply hend
    simp only [Equiv.apply_symm_apply, mem_insert_iff, mem_singleton_iff]
    exact Or.inr rfl

theorem exists_alternating_cut_neighborhoods (P : Polygon E n)
    (U : Fin n → Set E) (hU : ∀ i, IsOpen (U i))
    (hconv : ∀ i, Convex ℝ (U i)) (hPU : ∀ i, P i ∈ U i) :
    ∃ α β : Fin n → ℝ,
      (∀ i, α i ∈ Ioo (0 : ℝ) (1 / 2) ∧ β i ∈ Ioo (1 / 2 : ℝ) 1 ∧
        P.edgeCut α i ∈ U i ∧ P.edgeCut β i ∈ U (finRotate n i) ∧
        P.edgeCut (fun _ => (1 / 2 : ℝ)) i ∈
          segment ℝ (P.edgeCut α i) (P.edgeCut β i) ∧
        segment ℝ (P.edgeCut α i) (P.edgeCut β i) ⊆
          lineMap (P i) (P (finRotate n i)) '' Ioo (0 : ℝ) 1) ∧
      ∀ V : Fin n → Set E, (∀ i, IsOpen (V i)) →
        (∀ i, segment ℝ (P.edgeCut α i) (P.edgeCut β i) ⊆ V i) →
        let Q := P.midpointSubdivision
        let τ := midpointCutParameters α β
        let W := midpointArcNeighborhoods U V
        ∀ k, IsOpen (W k) ∧ Q.cutArc τ k ⊆ W k ∧
          Q (finRotate (n * 2) k) ∈ W k ∧
          Q.edgeCut τ k ∈ W k ∩ W ((finRotate (n * 2)).symm k) := by
  obtain ⟨α, β, h⟩ := P.exists_ordered_endpoint_cuts U hU hPU
    (fun _ => (1 / 2 : ℝ)) (by intro i; constructor <;> norm_num)
  refine ⟨α, β, ?_, ?_⟩
  · intro i
    obtain ⟨hα, hβ, hαU, hβU, _, hmid, hseg⟩ := h i
    exact ⟨hα, hβ, hαU, hβU, hmid, hseg⟩
  · intro V hV hsegment
    exact P.midpointArcNeighborhoods_properties α β (fun i => (h i).1)
      (fun i => (h i).2.1) U V hU hV hconv hPU (fun i => (h i).2.2.1)
      (fun i => (h i).2.2.2.1) hsegment

end Polygon
