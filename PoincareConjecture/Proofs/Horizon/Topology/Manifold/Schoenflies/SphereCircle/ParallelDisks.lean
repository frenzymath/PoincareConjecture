import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.InwardDisk
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.ParallelDisks.Charts



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)




theorem exists_parallel_disks_of_sphere_tube
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε) :
    ∃ a : Real, 0 < a ∧ a < ε / 4 ∧ a < 1 / 4 ∧
      ∃ d : OpenPartialHomeomorph E2 S2,
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
        closedBall 0 (1 + 2 * a) ⊆ d.source ∧
        ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
          (∀ p : S1, ∀ t : Real, |t| ≤ 2 * a ->
            d ((1 + t) • (p : E2)) = T (q p, t)) ∧
          ∃ eMinus ePlus : OpenPartialHomeomorph E2 S2,
            closedBall 0 1 ⊆ eMinus.source ∧ closedBall 0 1 ⊆ ePlus.source ∧
            ContMDiffOn (𝓡 2) (𝓡 2) ∞ eMinus eMinus.source ∧
            ContMDiffOn (𝓡 2) (𝓡 2) ∞ eMinus.symm eMinus.target ∧
            ContMDiffOn (𝓡 2) (𝓡 2) ∞ ePlus ePlus.source ∧
            ContMDiffOn (𝓡 2) (𝓡 2) ∞ ePlus.symm ePlus.target ∧
            eMinus '' closedBall 0 1 = d '' closedBall 0 (1 - a) ∧
            eMinus '' ball 0 1 = d '' ball 0 (1 - a) ∧
            ePlus '' closedBall 0 1 = (d '' ball 0 (1 + a))ᶜ ∧
            ePlus '' ball 0 1 = (d '' closedBall 0 (1 + a))ᶜ ∧
            eMinus '' sphere (0 : E2) 1 = range (fun p : S1 => T (p, -a)) ∧
            ePlus '' sphere (0 : E2) 1 = range (fun p : S1 => T (p, a)) ∧
            Disjoint (eMinus '' closedBall 0 1) (ePlus '' closedBall 0 1) ∧
            eMinus '' closedBall 0 1 ∪ T '' (univ ×ˢ Icc (-a) a) ∪
              ePlus '' closedBall 0 1 = univ ∧
            T '' (univ ×ˢ Icc (-a) a) =
              (eMinus '' ball 0 1 ∪ ePlus '' ball 0 1)ᶜ := by
  obtain ⟨e, hesource, he, hei, hecenter, henegative⟩ :=
    exists_inward_disk_of_sphere_tube hε T hT hTi hsource
  obtain ⟨d, hd, hdi, hdsource, _, _, _, q, η, hη, hηlim, hraw⟩ :=
    exists_disk_chart_matching_collar e he hei hesource hε T hT hTi hsource
      hecenter henegative
  let a := η / 8
  have ha : 0 < a := by dsimp [a]; positivity
  have haε : a < ε / 4 := by
    have := hηlim.trans_le (min_le_left ε 1)
    dsimp [a]
    linarith
  have ha1 : a < (1 / 4 : Real) := by
    have := hηlim.trans_le (min_le_right ε 1)
    dsimp [a]
    linarith
  have h2a : 2 * a < η := by dsimp [a]; linarith
  have hminus : 0 < 1 - a := by linarith
  have hplus : 0 < 1 + a := by linarith
  have hradial {x : E2} (hx : 0 < ‖x‖) :
      ‖x‖ • (CircleCollar.direction x : E2) = x := by
    rw [CircleCollar.direction_coe (norm_pos_iff.mp hx), smul_smul,
      mul_inv_cancel₀ hx.ne', one_smul]
  have hwide : closedBall (0 : E2) (1 + 2 * a) ⊆ d.source := by
    intro x hx
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hdsource (mem_closedBall_zero_iff.mpr hx1)
    · have hpos : 0 < ‖x‖ := by linarith [lt_of_not_ge hx1]
      have hclose : |‖x‖ - 1| < η := by
        rw [abs_of_pos (by linarith [lt_of_not_ge hx1])]
        linarith [mem_closedBall_zero_iff.mp hx]
      have hh := (hraw (CircleCollar.direction x) ‖x‖ hclose).1
      rwa [hradial hpos] at hh
  have hmatch (p : S1) (t : Real) (ht : |t| ≤ 2 * a) :
      d ((1 + t) • (p : E2)) = T (q p, t) := by
    have hh := (hraw p (1 + t) (by simpa using ht.trans_lt h2a)).2
    simpa only [add_sub_cancel_left] using hh
  have htimepos {t : Real} (ht : |t| ≤ 2 * a) : 0 < 1 + t := by
    have hh := (abs_le.mp ht).1
    linarith
  have hsphere (t : Real) (ht : |t| ≤ 2 * a) :
      d '' sphere (0 : E2) (1 + t) = range (fun p : S1 => T (p, t)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hnorm := mem_sphere_zero_iff_norm.mp hx
      refine ⟨q (CircleCollar.direction x), ?_⟩
      have hh := hmatch (CircleCollar.direction x) t ht
      rw [← hnorm, hradial (hnorm.symm ▸ htimepos ht)] at hh
      exact hh.symm
    · rintro ⟨p, rfl⟩
      refine ⟨(1 + t) • ((q.symm p : S1) : E2), ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (htimepos ht), norm_eq_of_mem_sphere, mul_one]
      · rw [hmatch _ t ht, q.apply_symm_apply]
  have hsmallsource : closedBall (0 : E2) (1 - a) ⊆ d.source :=
    (closedBall_subset_closedBall (by linarith)).trans hwide
  have hbigsource : closedBall (0 : E2) (1 + a) ⊆ d.source :=
    (closedBall_subset_closedBall (by linarith)).trans hwide
  obtain ⟨eMinus, hsMinus, heMinus, heiMinus, hclosedMinus, hballMinus, hsphereMinus⟩ :=
    ParallelDisks.exists_rescaled_disk_chart hminus d hsmallsource hd hdi
  let D : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
    { d with contMDiffOn_toFun := hd, contMDiffOn_invFun := hdi }
  obtain ⟨R, E, hR, hEs, hE, hEi, hEclosed⟩ := exists_complementary_disk_neighborhood
    hplus d (d.injOn.mono hbigsource)
      (fun x hx => D.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hbigsource hx))
  obtain ⟨ePlus, hsPlus, hePlus, heiPlus, hclosedPlus, _, _⟩ :=
    ParallelDisks.exists_rescaled_disk_chart hR E hEs hE hEi
  have houter : ePlus '' closedBall 0 1 = (d '' ball 0 (1 + a))ᶜ :=
    hclosedPlus.trans hEclosed
  have houteropen : ePlus '' ball 0 1 = (d '' closedBall 0 (1 + a))ᶜ := by
    rw [ePlus.image_ball_eq_interior hsPlus houter, interior_compl,
      ParallelDisks.closure_image_ball hplus d hbigsource]
  have hbminus : eMinus '' sphere (0 : E2) 1 = range (fun p : S1 => T (p, -a)) := by
    rw [hsphereMinus]
    convert! hsphere (-a) (by rw [abs_neg, abs_of_pos ha]; linarith) using 1
  have hbplus : ePlus '' sphere (0 : E2) 1 = range (fun p : S1 => T (p, a)) := by
    rw [ePlus.image_sphere_eq_frontier hsPlus houter, frontier_compl,
      ParallelDisks.frontier_image_ball hplus d hbigsource hd hdi]
    exact hsphere a (by rw [abs_of_pos ha]; linarith)
  have hslab : T '' (univ ×ˢ Icc (-a) a) =
      d '' (closedBall 0 (1 + a) \ ball 0 (1 - a)) := by
    ext y
    constructor
    · rintro ⟨⟨p, t⟩, ht, rfl⟩
      have hta : |t| ≤ a := abs_le.mpr ht.2
      have ht2 : |t| ≤ 2 * a := by linarith
      refine ⟨(1 + t) • ((q.symm p : S1) : E2), ⟨?_, ?_⟩, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (htimepos ht2), norm_eq_of_mem_sphere, mul_one]
        linarith [ht.2.2]
      · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (htimepos ht2), norm_eq_of_mem_sphere, mul_one]
        linarith [ht.2.1]
      · rw [hmatch _ t ht2, q.apply_symm_apply]
    · rintro ⟨x, ⟨hxhi, hxlo⟩, rfl⟩
      have hlo : 1 - a ≤ ‖x‖ := le_of_not_gt (fun hx => hxlo (mem_ball_zero_iff.mpr hx))
      have hhi : ‖x‖ ≤ 1 + a := mem_closedBall_zero_iff.mp hxhi
      have hnormpos : 0 < ‖x‖ := hminus.trans_le hlo
      have ht : ‖x‖ - 1 ∈ Icc (-a) a := ⟨by linarith, by linarith⟩
      refine ⟨(q (CircleCollar.direction x), ‖x‖ - 1), ⟨mem_univ _, ht⟩, ?_⟩
      have hh := hmatch (CircleCollar.direction x) (‖x‖ - 1)
        ((abs_le.mpr ht).trans (by linarith))
      rw [show 1 + (‖x‖ - 1) = ‖x‖ by ring, hradial hnormpos] at hh
      exact hh.symm
  have hslabdiff : T '' (univ ×ˢ Icc (-a) a) =
      d '' closedBall 0 (1 + a) \ d '' ball 0 (1 - a) := by
    rw [hslab]
    exact (d.injOn.mono hbigsource).image_sdiff_subset
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have hinnerouter : d '' closedBall 0 (1 - a) ⊆ d '' ball 0 (1 + a) :=
    image_mono (closedBall_subset_ball (by linarith))
  refine ⟨a, ha, haε, ha1, d, hd, hdi, hwide, q, hmatch, eMinus, ePlus,
    hsMinus, hsPlus, heMinus, heiMinus, hePlus, heiPlus, hclosedMinus, hballMinus, houter, houteropen,
    hbminus, hbplus, ?_, ?_, ?_⟩
  · rw [hclosedMinus, houter]
    exact disjoint_left.mpr fun y hy hny => hny (hinnerouter hy)
  · rw [hclosedMinus, houter, hslabdiff]
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ d '' ball 0 (1 + a)
    · by_cases hsmall : y ∈ d '' ball 0 (1 - a)
      · exact Or.inl (Or.inl (image_mono ball_subset_closedBall hsmall))
      · exact Or.inl (Or.inr ⟨image_mono ball_subset_closedBall hy, hsmall⟩)
    · exact Or.inr hy
  · rw [hballMinus, houteropen, hslabdiff]
    ext y
    simp only [mem_sdiff, mem_compl_iff, mem_union, not_or, not_not]
    exact and_comm

end Poincare.Manifold.Schoenflies
