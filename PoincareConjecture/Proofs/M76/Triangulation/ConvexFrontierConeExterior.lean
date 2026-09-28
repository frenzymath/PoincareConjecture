import PoincareConjecture.Proofs.M76.Mathlib.ConvexCylinderExteriorBody
import PoincareConjecture.Proofs.M76.Mathlib.ConvexConeIncidence
import PoincareConjecture.Proofs.M76.Mathlib.CylinderExteriorAttachmentSets
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierDiskCone
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRadialConeDisk
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall
import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereDiskComplement
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels












set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem isFinitePLBallPair_convexFrontierCone_cylinderExterior
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hJ : J.faces.Finite)
    {Q C d q : Set E} (hQ : IsCompact Q) (hC : IsCompact C)
    (hQcv : Convex ℝ Q) (hCcv : Convex ℝ C)
    (hQ0 : (0 : E) ∈ interior Q) (hQC : Q ⊆ interior C)
    (hKC : K.space = C) (hJQ : J.space = frontier Q)
    (hdim : Module.finrank ℝ E = 3)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : Q = {x | ∀ i, L i x ≤ 1})
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (hdQ : d ⊆ frontier Q)
    (hout : (frontier Q \ d).Nonempty) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior (convexJoin ℝ {0} d) ×ˢ {1})
      ((d ∪ convexJoin ℝ {0} q) ×ˢ {(1 : ℝ)}) := by
  let d' := frontier Q \ (d \ q)
  let B := convexJoin ℝ {0} d
  let B' := convexJoin ℝ {0} d'
  let l := convexJoin ℝ {0} q
  let O := frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior Q ×ˢ {(1 : ℝ)}
  have hd' : IsFinitePLBallPair (ℝ × ℝ) d' q :=
    J.isFinitePLBallPair_convex_sphere_disk_complement hJ hQ hQcv ⟨0, hQ0⟩
      hJQ hdim hd hdQ hout
  have hd'Q : d' ⊆ frontier Q := sdiff_subset
  have hdd' : d ∪ d' = frontier Q := by
    ext x
    change (x ∈ d ∨ (x ∈ frontier Q ∧ ¬ (x ∈ d ∧ x ∉ q))) ↔ x ∈ frontier Q
    have hh := @hdQ x
    tauto
  have hdd'q : d ∩ d' = q := by
    ext x
    change (x ∈ d ∧ x ∈ frontier Q ∧ ¬ (x ∈ d ∧ x ∉ q)) ↔ x ∈ q
    have hh := @hd.1 x
    have hhQ := @hdQ x
    tauto
  obtain ⟨n, P, hPi, hPe, hPq⟩ := hd.exists_polygon_boundary
  have hqne : q.Nonempty := ⟨P 0, hPq.subset (P.vertex_mem_boundary 0)⟩
  have hqQ : q ⊆ frontier Q := hd.1.trans hdQ
  have hl : IsFinitePLBallPair (ℝ × ℝ) l q := by
    have h := P.isFinitePLBallPair_radial_cone hPe hPi hQcv hQ0
      (hPq.subset.trans hqQ)
    simpa only [hPq] using h
  have hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (d ∪ l) :=
    hd.convexJoin_zero_of_subset_frontier hQcv hQ0 hdQ
  have hB' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B' (d' ∪ l) :=
    hd'.convexJoin_zero_of_subset_frontier hQcv hQ0 hd'Q
  have hmodeldim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ E := by
    simp [Module.finrank_prod, hdim]
  have hfrontB : frontier B = d ∪ l := hB.frontier_eq_of_finrank_eq hmodeldim
  have hBB' : B ∪ B' = Q := by
    change (convexJoin ℝ {0} d) ∪ (convexJoin ℝ {0} d') = Q
    rw [← convexJoin_union_right, hdd']
    exact hQ.convexJoin_zero_frontier_eq hQcv hQ0 (hqne.mono hqQ)
  have hBinter : B ∩ B' = l := by
    have h := hQcv.convexJoin_zero_inter_of_nonempty hQ0 hdQ hd'Q
      (hdd'q.symm ▸ hqne)
    simpa only [hdd'q] using h
  have hB'Q : B' ⊆ Q := fun _ hx => hBB'.subset (Or.inr hx)
  have hB'front : B' ∩ frontier Q = d' :=
    hQcv.convexJoin_zero_inter_frontier hQ0 hd'Q
  have hlfront : l ∩ frontier Q = q := hQcv.convexJoin_zero_inter_frontier hQ0 hqQ
  have hld' : l ∩ d' = q := by
    apply Subset.antisymm
    · exact fun _ hx => hlfront.subset ⟨hx.1, hd'Q hx.2⟩
    · exact subset_inter hl.1 hd'.1
  have hO : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) O
      ((d ×ˢ {(1 : ℝ)}) ∪ (d' ×ˢ {1})) := by
    have h := K.isFinitePLBallPair_convex_cylinderExterior hK hQ hC hQcv hCcv hQ0 hQC
      hKC L hL hrep hmodeldim.symm
    rwa [← hdd', union_prod] at h
  have htop : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (B' ×ˢ {(1 : ℝ)})
      ((l ×ˢ {1}) ∪ (d' ×ˢ {1})) := by
    simpa only [union_prod, union_comm] using hB'.prod_singleton (1 : ℝ)
  have hjoin : O ∩ (B' ×ˢ {(1 : ℝ)}) = d' ×ˢ {1} :=
    (inter_comm _ _).trans (top_face_inter_inner_cylinderExterior hB'Q
      (hQC.trans interior_subset) hB'front)
  have hresult := hO.union_of_ball_disk_attachment htop (hd.prod_singleton (1 : ℝ))
    (hl.prod_singleton (1 : ℝ)) (hd'.prod_singleton (1 : ℝ))
    (by rw [← inter_prod, hdd'q]) (by rw [← inter_prod, hld']) hjoin
  have hunion : frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior B ×ˢ {(1 : ℝ)} =
      O ∪ (B' ×ˢ {1}) := cylinderExterior_eq_union_of_boundary_cut
        (hQC.trans interior_subset) hBB' hBinter hfrontB hdQ
  rw [← union_prod, ← hunion] at hresult
  exact hresult

end Geometry.SimplicialComplex
