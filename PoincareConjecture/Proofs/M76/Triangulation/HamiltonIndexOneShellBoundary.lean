import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneComplementFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineSlabComplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (ℝ × ℝ)
local notation "W" => (ℝ × V2)


def squareInnerAnnulus : Set W := Icc (-1) 1 ×ˢ sphere 0 (3 / 2)

private theorem block_interior :
    interior squareBlock = Ioo (-1) 1 ×ˢ ball (0 : V2) 2 := by
  rw [squareBlock, interior_prod_eq, interior_Icc, interior_closedBall _ (by norm_num)]

private theorem shell_interior : interior squareShell =
    Ioo (-1) 1 ×ˢ {v : V2 | (3 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2} := by
  have hrep : ((norm : V2 → ℝ) ⁻¹' Icc (3 / 2) 2) =
      closedBall (0 : V2) 2 ∩ (ball 0 (3 / 2))ᶜ := by
    ext v
    simp only [mem_preimage, mem_Icc, mem_inter_iff, mem_compl_iff,
      mem_closedBall_zero_iff, mem_ball_zero_iff, not_lt]
    exact and_comm
  rw [squareShell, interior_prod_eq, interior_Icc, hrep, interior_inter,
    interior_closedBall _ (by norm_num), interior_compl, closure_ball _ (by norm_num)]
  congr 1
  ext v
  simp only [mem_inter_iff, mem_compl_iff, mem_ball_zero_iff,
    mem_closedBall_zero_iff, not_le, mem_ofPred_eq]
  exact and_comm



theorem squareShell_frontier :
    frontier squareShell = squareInnerAnnulus ∪ squareOuterAnnulus := by
  have hc : IsClosed squareShell :=
    isClosed_Icc.prod (isClosed_Icc.preimage continuous_norm)
  have hL : IsClosed squareBlock := isClosed_Icc.prod isClosed_closedBall
  rw [frontier, hc.closure_eq, shell_interior]
  ext x
  change (x ∈ squareShell ∧ x ∉ Ioo (-1) 1 ×ˢ
    {v : V2 | (3 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2}) ↔
    x ∈ squareInnerAnnulus ∨ (x ∈ frontier squareBlock ∧ (3 / 2 : ℝ) ≤ ‖x.2‖)
  rw [frontier, hL.closure_eq, block_interior]
  simp only [squareShell, squareInnerAnnulus, squareBlock, mem_sdiff,
    mem_prod, mem_preimage, mem_Icc, mem_Ioo, mem_sphere_zero_iff_norm,
    mem_closedBall_zero_iff, mem_ball_zero_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hs, hr0, hr2⟩, hn⟩
    by_cases hr : ‖x.2‖ = (3 / 2 : ℝ)
    · exact Or.inl ⟨hs, hr⟩
    · right
      refine ⟨⟨⟨hs, hr2⟩, ?_⟩, hr0⟩
      rintro ⟨hsi, hri⟩
      exact hn ⟨hsi, lt_of_le_of_ne hr0 (Ne.symm hr), hri⟩
  · rintro (⟨hs, hr⟩ | ⟨⟨⟨hs, hr2⟩, hn⟩, hr0⟩)
    · refine ⟨⟨hs, ?_, ?_⟩, ?_⟩
      · exact hr.ge
      · linarith
      · intro hi
        exact (lt_irrefl (3 / 2 : ℝ)) (hr ▸ hi.2.1)
    · exact ⟨⟨hs, hr0, hr2⟩, fun hi => hn ⟨hi.1, hi.2.2⟩⟩

private theorem inner_inter_outer : squareInnerAnnulus ∩ squareOuterAnnulus = squareRims := by
  ext x
  constructor
  · rintro ⟨hxI, hxO⟩
    refine ⟨?_, hxI.2⟩
    have hn : ‖x.2‖ = (3 / 2 : ℝ) := mem_sphere_zero_iff_norm.mp hxI.2
    have hs : x.1 = -1 ∨ x.1 = 1 := by
      by_contra h
      push Not at h
      apply hxO.1.2
      rw [block_interior]
      exact ⟨⟨lt_of_le_of_ne hxI.1.1 (Ne.symm h.1),
        lt_of_le_of_ne hxI.1.2 h.2⟩, mem_ball_zero_iff.mpr (by linarith)⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using hs
  · intro hx
    have hs : x.1 = -1 ∨ x.1 = 1 := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hx.1
    have hsI : x.1 ∈ Icc (-1 : ℝ) 1 := by
      rcases hs with hs | hs <;> rw [hs] <;> norm_num
    have hn : ‖x.2‖ = (3 / 2 : ℝ) := mem_sphere_zero_iff_norm.mp hx.2
    refine ⟨⟨hsI, hx.2⟩, ⟨?_, hn.ge⟩⟩
    refine ⟨subset_closure ⟨hsI, mem_closedBall_zero_iff.mpr (by linarith)⟩, ?_⟩
    intro hi
    rw [block_interior] at hi
    rcases hs with hs | hs
    · exact (lt_irrefl (-1 : ℝ)) (hs ▸ hi.1.1)
    · exact (lt_irrefl (1 : ℝ)) (hs ▸ hi.1.2)

private def radialCoordinate (i : Fin 4) : W →L[ℝ] ℝ :=
  ![(ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ V2),
    -((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ V2)),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ V2),
    -((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ V2))] i

private theorem radialCoordinate_le (x : W) (i : Fin 4) : radialCoordinate i x ≤ ‖x.2‖ := by
  change radialCoordinate i x ≤ max |x.2.1| |x.2.2|
  fin_cases i
  · exact (le_abs_self _).trans (le_max_left _ _)
  · exact (neg_le_abs _).trans (le_max_left _ _)
  · exact (le_abs_self _).trans (le_max_right _ _)
  · exact (neg_le_abs _).trans (le_max_right _ _)

private theorem exists_radialCoordinate (x : W) : ∃ i, radialCoordinate i x = ‖x.2‖ := by
  by_cases h : |x.2.1| ≤ |x.2.2|
  · rcases le_total 0 x.2.2 with hp | hn
    · refine ⟨2, ?_⟩
      change x.2.2 = max |x.2.1| |x.2.2|
      rw [max_eq_right h, abs_of_nonneg hp]
    · refine ⟨3, ?_⟩
      change -x.2.2 = max |x.2.1| |x.2.2|
      rw [max_eq_right h, abs_of_nonpos hn]
  · rcases le_total 0 x.2.1 with hp | hn
    · refine ⟨0, ?_⟩
      change x.2.1 = max |x.2.1| |x.2.2|
      rw [max_eq_left (not_le.mp h).le, abs_of_nonneg hp]
    · refine ⟨1, ?_⟩
      change -x.2.1 = max |x.2.1| |x.2.2|
      rw [max_eq_left (not_le.mp h).le, abs_of_nonpos hn]

private theorem outer_identity_finitePL :
    FinitePiecewiseAffineOn (id : W → W) squareOuterAnnulus := by
  have hbase : CoordinateHalfBoxes.base 2 = closedBall (0 : V2) 2 := by
    ext v
    simp only [CoordinateHalfBoxes.base, mem_prod, mem_Icc, mem_closedBall_zero_iff,
      Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
  have hblock := (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
    (CoordinateHalfBoxes.base_ballPair (by norm_num : (0 : ℝ) < 2))
  rw [hbase] at hblock
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hblock
  let J := K.frontierSubcomplex squareBlock
  have hJ : J.faces.Finite := K.frontierSubcomplex_finite squareBlock hK
  have hJs : J.space = frontier squareBlock := K.frontierSubcomplex_space
    (isClosed_Icc.prod isClosed_closedBall)
    ((convex_Icc (-1 : ℝ) 1).prod (convex_closedBall (0 : V2) 2))
    ⟨0, by rw [block_interior]; norm_num [mem_ball_zero_iff]⟩ hKs
  choose L hL hLs using fun i : Fin 4 => J.exists_finite_affineSlab_complex hJ
    (radialCoordinate i).toLinearMap.toAffineMap (3 / 2) 2
  obtain ⟨N, hN, hNs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion L hL
  have hspace : N.space = squareOuterAnnulus := hNs.trans (by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rw [hLs i, hJs] at hi
      exact ⟨hi.1, hi.2.1.trans (radialCoordinate_le x i)⟩
    · intro hx
      obtain ⟨i, hi⟩ := exists_radialCoordinate x
      refine ⟨i, ?_⟩
      rw [hLs i, hJs]
      refine ⟨hx.1, ?_⟩
      change radialCoordinate i x ∈ Icc (3 / 2 : ℝ) 2
      rw [hi]
      exact ⟨hx.2, mem_closedBall_zero_iff.mp
        (((isClosed_Icc.prod isClosed_closedBall : IsClosed squareBlock).frontier_subset hx.1).2)⟩)
  exact ⟨N, hN, hspace, N.affineOnFaces_affine (ContinuousAffineMap.id ℝ W)⟩




theorem exists_marked_shell_frontier_map {T : Set W}
    (tau : squareInnerAnnulus ≃ₜ T) (htau : tau.IsFinitePL)
    (hrims : T ∩ frontier squareBlock = squareRims)
    (hfix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x) :
    ∃ e : frontier squareShell ≃ₜ (T ∪ squareOuterAnnulus : Set W), e.IsFinitePL ∧
      (∀ x : squareInnerAnnulus, ∀ hx : (x : W) ∈ frontier squareShell,
        (e ⟨x, hx⟩ : W) = tau x) ∧
      ∀ x : squareOuterAnnulus, ∀ hx : (x : W) ∈ frontier squareShell,
        (e ⟨x, hx⟩ : W) = x := by
  have hTrims : T ∩ squareOuterAnnulus = squareRims := by
    ext x
    constructor
    · intro hx
      exact hrims ▸ ⟨hx.1, hx.2.1⟩
    · intro hx
      have h := hrims.symm ▸ hx
      exact ⟨h.1, h.2, (mem_sphere_zero_iff_norm.mp hx.2).ge⟩
  let d := Homeomorph.refl squareOuterAnnulus
  have hd : d.IsFinitePL := ⟨id, outer_identity_finitePL, fun _ => rfl⟩
  have hover (x : squareInnerAnnulus) : (x : W) ∈ squareOuterAnnulus ↔
      (tau x : W) ∈ squareOuterAnnulus := by
    constructor
    · intro hx
      have hr : (x : W) ∈ squareRims := inner_inter_outer ▸ ⟨x.property, hx⟩
      rwa [hfix x hr]
    · intro hx
      have hr : (tau x : W) ∈ squareRims := hTrims ▸ ⟨(tau x).property, hx⟩
      have hpre := inner_inter_outer.symm ▸ hr
      let y : squareInnerAnnulus := ⟨tau x, hpre.1⟩
      have heq : tau y = tau x := Subtype.ext (hfix y hr)
      have hxy := tau.injective heq
      have hval : (x : W) = tau x := (congrArg Subtype.val hxy).symm
      rwa [hval]
  obtain ⟨H, hH, hinner, houter⟩ := Homeomorph.exists_union_finitePL tau d htau hd hover
    (fun x hxI hxO => hfix ⟨x, hxI⟩ (inner_inter_outer ▸ ⟨hxI, hxO⟩))
  let e := (Homeomorph.setCongr squareShell_frontier).trans H
  refine ⟨e, ?_, ?_, ?_⟩
  · obtain ⟨f, hf, hfeq⟩ := hH
    refine ⟨f, squareShell_frontier.symm ▸ hf, ?_⟩
    intro x
    exact hfeq ((Homeomorph.setCongr squareShell_frontier) x)
  · intro x hx
    exact hinner x
  · intro x hx
    exact houter x

end PoincareConjecture.M76.HamiltonIndexOne
