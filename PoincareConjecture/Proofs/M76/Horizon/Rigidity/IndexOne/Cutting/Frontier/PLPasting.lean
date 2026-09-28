import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Frontier.FaceSeparation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Frontier.ComplementaryHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem finitePiecewiseAffineOn_complementary_frontier_coordinate
    {E V α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hfront : frontier (sourceSlab phi a b) =
      (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (G : frontier (sourceSlab phi a b) → X)
    (hfix : ∀ x : frontier (sourceSlab phi a b),
      (x : X) ∈ sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) → G x = x)
    (hstrip : ∀ x : ↥(sourceSlab phi a b ∩ frontier R),
      G ⟨x, hfront.symm ▸ Or.inl x.property⟩ =
        complementaryOldStripReversal phi a b F hab (by linarith) x)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (q : E → frontier (sourceSlab phi a b)) (hq : ContinuousOn q K.space)
    (hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) K.space)
    (sigma : X → V)
    (hsigma : ∀ i, LocallyPiecewiseAffineOn (sigma ∘ (e i).symm) (e i).target) :
    FinitePiecewiseAffineOn (fun z => sigma (G (q z))) K.space := by
  classical
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hR := isCompact_latticeHandleDomain (Fin 1) (Fin 2) L
  let : CompactSpace R := isCompact_iff_compactSpace.mp hR
  let phase : C(R, C) := (sourcePhase phi).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  have hNc : IsCompact (sourceSlab phi a b) :=
    (((AddCircle.isCompact_closedIntervalArc p a b).isClosed.preimage phase.continuous).isCompact).image
      continuous_subtype_val
  have hqN (y : E) : (q y : X) ∈ sourceSlab phi a b := hNc.isClosed.frontier_subset (q y).property
  let qR : E → R := fun y => ⟨q y, sourceSlab_subset phi a b (hqN y)⟩
  have hqR : ContinuousOn qR K.space := by
    apply Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
    change ContinuousOn (fun y => (q y : X)) K.space
    exact continuous_subtype_val.comp_continuousOn hq
  let A := AddCircle.openPartialHomeomorphCoe p 0
  let t := fun y => A.symm (phase (qR y))
  have ht (y : E) : t y ∈ Icc a b ∧ ((t y : ℝ) : C) = phase (qR y) := by
    obtain ⟨u, hu, huq⟩ := (mem_sourceSlab_iff phi a b (qR y)).mp (hqN y)
    have huA : u ∈ A.source := ⟨ha.trans_le hu.1, by simpa only [zero_add] using hu.2.trans_lt hb⟩
    have htu : t y = u := by
      change (u : C) = phase (qR y) at huq
      change A.symm (phase (qR y)) = u
      rw [← huq]
      exact A.left_inv huA
    rw [htu]
    exact ⟨hu, huq⟩
  have htPL : FinitePiecewiseAffineOn t K.space :=
    finitePiecewiseAffineOn_sourcePhase_coordinate hd phi hphi K hK qR hqR hqPL 0
      (by
        intro y _ hy
        have hm := (mem_sourceSlab_iff phi a b (qR y)).mp (hqN y)
        rw [hy] at hm
        exact AddCircle.zero_notMem_closedIntervalArc p ha hb hm)
  obtain ⟨J, hJ, hJK, htJ⟩ := htPL
  let : Finite J.faces := hJ.to_subtype
  have hface (s : J.faces) :
      FinitePiecewiseAffineOn (fun z => sigma (G (q z))) (convexHull ℝ (s.val : Set E)) := by
    obtain ⟨l, hl⟩ := htJ s.val s.property
    have hsub : convexHull ℝ (s.val : Set E) ⊆ K.space :=
      (J.convexHull_subset_space s.property).trans hJK.subset
    have hbetween (y : E) (hy : y ∈ convexHull ℝ (s.val : Set E))
        (hly : l y ∈ Ioo a b) : (q y : X) ∈ frontier R := by
      have hqy := hfront.subset (q y).property
      rcases hqy with hqy | hqy
      · exact hqy.2
      · have htI : t y ∈ Ico (0 : ℝ) (0 + p) :=
          ⟨ha.le.trans (ht y).1.1, by linarith [(ht y).1.2]⟩
        have haI : a ∈ Ico (0 : ℝ) (0 + p) := ⟨ha.le, by linarith⟩
        have hbI : b ∈ Ico (0 : ℝ) (0 + p) := ⟨by linarith, by linarith⟩
        rcases hqy with hqa | hqb
        · have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI haI).mp
            ((ht y).2.trans ((mem_sourceSurface_iff phi (a : C) (qR y)).mp hqa))
          exact False.elim (by rw [← hl hy, heq] at hly; exact lt_irrefl _ hly.1)
        · have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI hbI).mp
            ((ht y).2.trans ((mem_sourceSurface_iff phi (b : C) (qR y)).mp hqb))
          exact False.elim (by rw [← hl hy, heq] at hly; exact lt_irrefl _ hly.2)
    obtain ⟨M, hM, hMs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
      (fun _ : Unit => s.val) (fun _ => J.indep s.property)
    have hMspace : M.space = convexHull ℝ (s.val : Set E) := hMs.trans (by
      ext y
      simp only [mem_iUnion]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩)
    have hMK : M.space ⊆ K.space := hMspace.subset.trans hsub
    have hqM := hqPL.restrict_finite M hM hMK
    have hcases := affine_closed_piece_boundary_or_endpoint
      (s.val.finite_toSet.isCompact_convexHull ℝ).isClosed (convex_convexHull ℝ _)
      (hqPL.continuousOn.mono hsub) isClosed_frontier l hab
      (fun y hy => (hl hy) ▸ (ht y).1) hbetween
    rcases hcases with hold | hleft | hright
    · obtain ⟨y0, hy0⟩ := J.nonempty_of_mem_faces s.property
      have hy0S : y0 ∈ convexHull ℝ (s.val : Set E) := subset_convexHull ℝ _ hy0
      let qB : E → ↥(sourceSlab phi a b ∩ frontier R) := fun y =>
        if hy : (q y : X) ∈ frontier R then ⟨q y, hqN y, hy⟩
        else ⟨q y0, hqN y0, hold hy0S⟩
      have hqBval (y : E) (hy : y ∈ M.space) : (qB y : X) = q y := by
        simp only [qB, dif_pos (hold (hMspace.subset hy))]
      have hqBc : ContinuousOn qB M.space :=
        Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
          (hqM.continuousOn.congr hqBval)
      have hqBPL : PolyhedralPLInCharts e (fun y => (qB y : X)) M.space :=
        hqM.congr (fun y hy => (hqBval y hy).symm)
      have hrev := polyhedralPL_complementaryOldStripReversal hd phi hphi F ha hab hb
        M hM qB hqBc hqBPL
      have hcomp := hrev.finitePiecewiseAffineOn_comp M hM hsigma
      rw [← hMspace]
      apply hcomp.congr
      intro y hy
      change sigma (complementaryOldStripReversal phi a b F hab _ (qB y)) = sigma (G (q y))
      rw [← hstrip]
      congr 2
      exact Subtype.ext (hqBval y hy)
    · have hcomp := hqM.finitePiecewiseAffineOn_comp M hM hsigma
      rw [← hMspace]
      apply hcomp.congr
      intro y hy
      change sigma (q y) = sigma (G (q y))
      rw [hfix (q y) (Or.inl ((mem_sourceSurface_iff phi (a : C) (qR y)).mpr ?_))]
      exact (ht y).2.symm.trans (congrArg (fun r : ℝ => (r : C))
        ((hl (hMspace.subset hy)).trans (hleft y (hMspace.subset hy))))
    · have hcomp := hqM.finitePiecewiseAffineOn_comp M hM hsigma
      rw [← hMspace]
      apply hcomp.congr
      intro y hy
      change sigma (q y) = sigma (G (q y))
      rw [hfix (q y) (Or.inr ((mem_sourceSurface_iff phi (b : C) (qR y)).mpr ?_))]
      exact (ht y).2.symm.trans (congrArg (fun r : ℝ => (r : C))
        ((hl (hMspace.subset hy)).trans (hright y (hMspace.subset hy))))
  have hcover : (⋃ s : J.faces, convexHull ℝ (s.val : Set E)) = K.space := by
    rw [← hJK]
    ext y
    simp only [mem_iUnion, SimplicialComplex.mem_space_iff]
    exact ⟨fun ⟨s, hs⟩ => ⟨s.val, s.property, hs⟩,
      fun ⟨s, hs, hy⟩ => ⟨⟨s, hs⟩, hy⟩⟩
  rw [← hcover]
  exact FinitePiecewiseAffineOn.iUnion hface

end PoincareConjecture.M76.HamiltonIntervalTorus
