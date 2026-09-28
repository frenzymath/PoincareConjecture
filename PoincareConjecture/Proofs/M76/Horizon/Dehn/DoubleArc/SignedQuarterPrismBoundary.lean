import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedRadiusPrism
import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

def signedTubeSectorPrescribed (eps delta : Bool) (α β : ℝ) : Set (P2 × ℝ) :=
  (signedTubeRadialRim eps delta ×ˢ Icc α β) ∪
    (signedTubeQuarter eps delta ×ˢ {α, β})

def signedTubeSectorRim (eps delta : Bool) (α β : ℝ) : Set (P2 × ℝ) :=
  (({signedTubeCorner 0 delta, signedTubeCorner 1 eps} : Set P2) ×ˢ Icc α β) ∪
    (signedTubeOuterArc eps delta ×ˢ {α, β})

theorem signedTubeSector_boundary_disks (eps delta : Bool) (α β : ℝ) (hαβ : α < β) :
    IsFinitePLBallPair (P2 × ℝ) (signedTubeQuarter eps delta ×ˢ Icc α β)
      ((signedTubeOuterArc eps delta ×ˢ Icc α β) ∪
        signedTubeSectorPrescribed eps delta α β) ∧
    IsFinitePLBallPair P2 (signedTubeOuterArc eps delta ×ˢ Icc α β)
      (signedTubeSectorRim eps delta α β) ∧
    IsFinitePLBallPair P2 (signedTubeSectorPrescribed eps delta α β)
      (signedTubeSectorRim eps delta α β) ∧
    (signedTubeOuterArc eps delta ×ˢ Icc α β) ∩
      signedTubeSectorPrescribed eps delta α β =
        signedTubeSectorRim eps delta α β := by
  classical
  let Q := signedTubeQuarter eps delta
  let O := signedTubeOuterArc eps delta
  let R := signedTubeRadialRim eps delta
  let ends : Set P2 := {signedTubeCorner 0 delta, signedTubeCorner 1 eps}
  let S := (O ×ˢ Icc α β) ∪ signedTubeSectorPrescribed eps delta α β
  have hQ := signedTube_quarter_ball eps delta
  have hOQ : O ⊆ Q := subset_union_left.trans hQ.1
  have hRQ : R ⊆ Q := subset_union_right.trans hQ.1
  have hends : O ∩ R = ends := signedTube_outer_inter_rim eps delta
  have hOBall : IsFinitePLBallPair ℝ O ends := by
    have hne : signedTubeCorner 1 eps ≠ signedTubeCorner 0 delta :=
      signedTube_corner_ne_corner 1 eps 0 delta (by simp)
    simpa only [O, ends, signedTubeOuterArc, pair_comm] using
      signedTube_segment_ball _ _ hne
  have hside := hOBall.prod (isFinitePLBallPair_Icc hαβ)
  change IsFinitePLBallPair P2 (O ×ˢ Icc α β)
    (signedTubeSectorRim eps delta α β) at hside
  have hball : IsFinitePLBallPair (P2 × ℝ) (Q ×ˢ Icc α β) S := by
    have h := hQ.prod (isFinitePLBallPair_Icc hαβ)
    have heq : ((O ∪ R) ×ˢ Icc α β) ∪ (Q ×ˢ {α, β}) = S := by
      ext x
      simp only [S, signedTubeSectorPrescribed, O, R, Q, mem_union, mem_prod]
      tauto
    rwa [heq] at h
  have hmeet : (O ×ˢ Icc α β) ∩ signedTubeSectorPrescribed eps delta α β =
      signedTubeSectorRim eps delta α β := by
    ext x
    have hm := Set.ext_iff.mp hends x.1
    change (x.1 ∈ O ∧ x.1 ∈ R) ↔ x.1 ∈ ends at hm
    have ho := hOQ (a := x.1)
    have ht : x.2 ∈ ({α, β} : Set ℝ) → x.2 ∈ Icc α β := by
      rintro (rfl | rfl)
      · exact ⟨le_rfl, hαβ.le⟩
      · exact ⟨hαβ.le, le_rfl⟩
    change ((x.1 ∈ O ∧ x.2 ∈ Icc α β) ∧
      ((x.1 ∈ R ∧ x.2 ∈ Icc α β) ∨ (x.1 ∈ Q ∧ x.2 ∈ ({α, β} : Set ℝ)))) ↔
      ((x.1 ∈ ends ∧ x.2 ∈ Icc α β) ∨ (x.1 ∈ O ∧ x.2 ∈ ({α, β} : Set ℝ)))
    tauto
  have hzR : (0, 0) ∈ R := Or.inl (left_mem_segment ℝ _ _)
  have hzO : (0, 0) ∉ O := by
    intro hz
    have h := hends.subset ⟨hz, hzR⟩
    rcases h with h | h
    · exact signedTube_corner_ne_center 0 delta h.symm
    · exact signedTube_corner_ne_center 1 eps h.symm
  have hout : (S \ (O ×ˢ Icc α β)).Nonempty := by
    refine ⟨((0, 0), α), Or.inr (Or.inl ⟨hzR, le_rfl, hαβ.le⟩), ?_⟩
    exact fun h => hzO h.1
  have hcomp := hball.boundary_disk_complement (by simp [Module.finrank_prod])
    hside subset_union_left hout
  have heq : S \ ((O ×ˢ Icc α β) \ signedTubeSectorRim eps delta α β) =
      signedTubeSectorPrescribed eps delta α β := by
    ext x
    have hm := Set.ext_iff.mp hmeet x
    change (x ∈ O ×ˢ Icc α β ∧ x ∈ signedTubeSectorPrescribed eps delta α β) ↔
      x ∈ signedTubeSectorRim eps delta α β at hm
    change ((x ∈ O ×ˢ Icc α β ∨ x ∈ signedTubeSectorPrescribed eps delta α β) ∧
      ¬(x ∈ O ×ˢ Icc α β ∧ x ∉ signedTubeSectorRim eps delta α β)) ↔
        x ∈ signedTubeSectorPrescribed eps delta α β
    constructor
    · rintro ⟨hx | hx, hn⟩
      · by_contra hnot
        exact hn ⟨hx, fun hr => hnot (hm.mpr hr).2⟩
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun h => h.2 (hm.mp ⟨h.1, hx⟩)⟩
  exact ⟨hball, hside, heq ▸ hcomp, hmeet⟩

end PoincareConjecture.M76.Dehn
