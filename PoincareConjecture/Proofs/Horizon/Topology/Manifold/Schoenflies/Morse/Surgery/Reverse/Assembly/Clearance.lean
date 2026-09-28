import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Reconstruction
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Correction.CapEdge











noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem cap_inter_retained
    (f : S2 → E3) (g : E2 → E3) (K : Set E3)
    (hgi : Injective g)
    (hcap : g '' closedBall (0 : E2) 1 ⊆ range f)
    (hretained : range f \ (g '' ball (0 : E2) 1) = K) :
    (g '' closedBall (0 : E2) 1) ∩ K = g '' sphere (0 : E2) 1 := by
  rw [← hretained]
  have heq : (g '' closedBall (0 : E2) 1) ∩
      (range f \ (g '' ball (0 : E2) 1)) =
      (g '' closedBall (0 : E2) 1) \ (g '' ball (0 : E2) 1) := by
    ext y
    exact ⟨fun hy => ⟨hy.1, hy.2.2⟩, fun hy => ⟨hy.1, hcap hy.1, hy.2⟩⟩
  rw [heq, ← image_sdiff hgi]
  congr 1
  ext x
  simp only [mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff,
    mem_sphere_zero_iff_norm, not_lt]
  exact le_antisymm_iff.symm

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)


theorem capMinus_inter_retained :
    (S.gMinus '' closedBall (0 : E2) 1) ∩
      ((fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1)) =
      S.gMinus '' sphere (0 : E2) 1 := by
  apply cap_inter_retained S.fMinus S.gMinus _ S.gMinus_injective
  · rw [S.fMinus_range]
    exact subset_union_left
  · exact S.range_minus_open_capMinus


theorem capPlus_inter_retained :
    (S.gPlus '' closedBall (0 : E2) 1) ∩
      ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1)) =
      S.gPlus '' sphere (0 : E2) 1 := by
  apply cap_inter_retained S.fPlus S.gPlus _ S.gPlus_injective
  · rw [S.fPlus_range]
    exact subset_union_left
  · exact S.range_minus_open_capPlus

private theorem tube_not_mem_open_retained (q : S1) {t : Real}
    (ht : t ∈ Icc (-S.a) S.a) :
    S.T (q, t) ∉ S.eMinus '' ball (0 : E2) 1 ∪ S.ePlus '' ball (0 : E2) 1 := by
  have hmem : S.T (q, t) ∈ S.T '' (univ ×ˢ Icc (-S.a) S.a) :=
    mem_image_of_mem S.T ⟨mem_univ q, ht⟩
  rwa [S.slab_eq] at hmem


theorem tube_not_mem_retainedMinus (q : S1) {t : Real}
    (ht : t ∈ Ioo (-S.a) S.a) :
    S.T (q, t) ∉ S.eMinus '' closedBall (0 : E2) 1 := by
  rintro ⟨x, hx, heq⟩
  have hxnot : x ∉ ball (0 : E2) 1 := by
    intro hxb
    exact S.tube_not_mem_open_retained q ⟨ht.1.le, ht.2.le⟩
      (Or.inl ⟨x, hxb, heq⟩)
  have hxs : x ∈ sphere (0 : E2) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact le_antisymm (mem_closedBall_zero_iff.mp hx)
      (not_lt.mp (fun h => hxnot (mem_ball_zero_iff.mpr h)))
  have hboundary : S.T (q, t) ∈ range (fun q : S1 => S.T (q, -S.a)) :=
    S.eMinus_boundary ▸ (show S.T (q, t) ∈ S.eMinus '' sphere (0 : E2) 1 from
      ⟨x, hxs, heq⟩)
  obtain ⟨q', heq'⟩ := hboundary
  have hts : (q, t) ∈ S.T.source := by
    rw [S.tube_source]
    exact ⟨mem_univ q, by linarith [ht.1, S.a_lt_quarter_ε, S.a_pos],
      by linarith [ht.2, S.a_lt_quarter_ε, S.a_pos]⟩
  have hqs : (q', -S.a) ∈ S.T.source := by
    rw [S.tube_source]
    exact ⟨mem_univ q', by linarith [S.a_lt_quarter_ε, S.a_pos],
      by linarith [S.a_lt_quarter_ε, S.a_pos]⟩
  have := congrArg Prod.snd (S.T.injOn hqs hts heq')
  exact (ne_of_lt ht.1) this


theorem tube_not_mem_retainedPlus (q : S1) {t : Real}
    (ht : t ∈ Ioo (-S.a) S.a) :
    S.T (q, t) ∉ S.ePlus '' closedBall (0 : E2) 1 := by
  rintro ⟨x, hx, heq⟩
  have hxnot : x ∉ ball (0 : E2) 1 := by
    intro hxb
    exact S.tube_not_mem_open_retained q ⟨ht.1.le, ht.2.le⟩
      (Or.inr ⟨x, hxb, heq⟩)
  have hxs : x ∈ sphere (0 : E2) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact le_antisymm (mem_closedBall_zero_iff.mp hx)
      (not_lt.mp (fun h => hxnot (mem_ball_zero_iff.mpr h)))
  have hboundary : S.T (q, t) ∈ range (fun q : S1 => S.T (q, S.a)) :=
    S.ePlus_boundary ▸ (show S.T (q, t) ∈ S.ePlus '' sphere (0 : E2) 1 from
      ⟨x, hxs, heq⟩)
  obtain ⟨q', heq'⟩ := hboundary
  have hts : (q, t) ∈ S.T.source := by
    rw [S.tube_source]
    exact ⟨mem_univ q, by linarith [ht.1, S.a_lt_quarter_ε, S.a_pos],
      by linarith [ht.2, S.a_lt_quarter_ε, S.a_pos]⟩
  have hqs : (q', S.a) ∈ S.T.source := by
    rw [S.tube_source]
    exact ⟨mem_univ q', by linarith [S.a_lt_quarter_ε, S.a_pos],
      by linarith [S.a_lt_quarter_ε, S.a_pos]⟩
  have := congrArg Prod.snd (S.T.injOn hqs hts heq')
  exact (ne_of_lt ht.2) this.symm



theorem middle_cylinder_disjoint_retained {l u : Real}
    (hl : -S.a < l) (hu : u < S.a) :
    Disjoint
      {y : E3 | inner Real v y ∈ Icc (c + l) (c + u) ∧
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1}
      (((fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1)) ∪
        ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1))) := by
  apply disjoint_left.mpr
  intro y hy hyretained
  have hyp : y ∈ range (fun p => S.D (f p)) := by
    rcases hyretained with ⟨p, _, hp⟩ | ⟨p, _, hp⟩ <;> exact ⟨p, hp⟩
  have hcircle := S.projection_mem_circle_of_mem_prepared hyp hy.2
    (abs_le.mpr ⟨by linarith [hy.1.1, S.a_pos],
      by linarith [hy.1.2, S.a_pos]⟩)
  have htube : y ∈ (fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc l u)) := by
    rw [← S.cylindrical_slab_eq_tube_image
      (by linarith [S.a_lt_quarter_ε, S.a_pos])
      (by linarith [S.a_lt_quarter_ε, S.a_pos])]
    exact ⟨hy.1, hcircle⟩
  obtain ⟨_, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩ := htube
  have ht' : t ∈ Ioo (-S.a) S.a := ⟨hl.trans_le ht.1, ht.2.trans_lt hu⟩
  rcases hyretained with ⟨p, hp, heq⟩ | ⟨p, hp, heq⟩
  · have heq' := S.prepared_embedding.isEmbedding.injective heq
    exact S.tube_not_mem_retainedMinus q ht' (heq' ▸ hp)
  · have heq' := S.prepared_embedding.isEmbedding.injective heq
    exact S.tube_not_mem_retainedPlus q ht' (heq' ▸ hp)


theorem isCompact_retained_union :
    IsCompact (((fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1)) ∪
      ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1))) := by
  have hminus := (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
    (S.eMinus.continuousOn.mono S.eMinus_source)
  have hplus := (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
    (S.ePlus.continuousOn.mono S.ePlus_source)
  exact (hminus.image S.prepared_embedding.contMDiff.continuous).union
    (hplus.image S.prepared_embedding.contMDiff.continuous)



theorem exists_middle_cylinder_neighborhood {l u : Real}
    (hl : -S.a < l) (hu : u < S.a) :
    ∃ O : Set E3, IsOpen O ∧
      {y : E3 | inner Real v y ∈ Icc (c + l) (c + u) ∧
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1} ⊆ O ∧
      Disjoint O (((fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1)) ∪
        ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1))) := by
  refine ⟨_, S.isCompact_retained_union.isClosed.isOpen_compl, ?_, disjoint_compl_left⟩
  intro y hy
  exact fun hyr => disjoint_left.mp (S.middle_cylinder_disjoint_retained hl hu) hy hyr

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies
