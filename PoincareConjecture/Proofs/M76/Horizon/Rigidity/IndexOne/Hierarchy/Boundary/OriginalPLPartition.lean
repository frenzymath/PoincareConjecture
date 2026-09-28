import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Frontier.FaceSeparation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Interior











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩



theorem exists_finite_source_frontier_parameter_partition
    {V α β : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (sourceSlab phi a b) =
      (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (q : V → frontier (sourceSlab phi a b))
    (hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) K.space) :
    ∃ J : SimplicialComplex ℝ V, J.faces.Finite ∧ J.space = K.space ∧
      ∀ s ∈ J.faces,
        MapsTo (fun z => (q z : X)) (convexHull ℝ (s : Set V)) (frontier R) ∨
        MapsTo (fun z => (q z : X)) (convexHull ℝ (s : Set V)) (sourceSurface phi (a : C)) ∨
        MapsTo (fun z => (q z : X)) (convexHull ℝ (s : Set V)) (sourceSurface phi (b : C)) := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hNc := sourceSlab_isCompact phi a b
  have hqN (y : V) : (q y : X) ∈ sourceSlab phi a b :=
    hNc.isClosed.frontier_subset (q y).property
  let qR : V → R := fun y => ⟨q y, sourceSlab_subset phi a b (hqN y)⟩
  have hqR : ContinuousOn qR K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  let phase : C(R, C) := (sourcePhase phi).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  let A := AddCircle.openPartialHomeomorphCoe p c
  let t := fun y => A.symm (phase (qR y))
  have ht (y : V) : t y ∈ Icc a b ∧ ((t y : ℝ) : C) = phase (qR y) := by
    obtain ⟨u, hu, huq⟩ := (mem_sourceSlab_iff phi a b (qR y)).mp (hqN y)
    have huA : u ∈ A.source := ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩
    have htu : t y = u := by
      change (u : C) = phase (qR y) at huq
      change A.symm (phase (qR y)) = u
      rw [← huq]
      exact A.left_inv huA
    rw [htu]
    exact ⟨hu, huq⟩
  have htI (y : V) : t y ∈ Ico c (c + p) :=
    ⟨ha.le.trans (ht y).1.1, (ht y).1.2.trans_lt hb⟩
  have haI : a ∈ Ico c (c + p) := ⟨ha.le, hab.trans hb⟩
  have hbI : b ∈ Ico c (c + p) := ⟨(ha.trans hab).le, hb⟩
  have htPL : FinitePiecewiseAffineOn t K.space :=
    finitePiecewiseAffineOn_sourcePhase_coordinate hd phi hphi K hK qR hqR hqPL c
      (by
        intro y _ hy
        have hcI : c ∈ Ico c (c + p) := ⟨le_rfl, by norm_num⟩
        have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico (htI y) hcI).mp
          ((ht y).2.trans hy)
        linarith [(ht y).1.1])
  obtain ⟨J, hJ, hJK, htJ⟩ := htPL
  refine ⟨J, hJ, hJK, ?_⟩
  intro s hs
  obtain ⟨l, hl⟩ := htJ s hs
  have hsub : convexHull ℝ (s : Set V) ⊆ K.space :=
    (J.convexHull_subset_space hs).trans hJK.subset
  have hbetween (y : V) (hy : y ∈ convexHull ℝ (s : Set V))
      (hly : l y ∈ Ioo a b) : (q y : X) ∈ frontier R := by
    rcases hfront.subset (q y).property with hqy | hqa | hqb
    · exact hqy.2
    · have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico (htI y) haI).mp
        ((ht y).2.trans ((mem_sourceSurface_iff phi (a : C) (qR y)).mp hqa))
      exact False.elim (by rw [← hl hy, heq] at hly; exact lt_irrefl _ hly.1)
    · have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico (htI y) hbI).mp
        ((ht y).2.trans ((mem_sourceSurface_iff phi (b : C) (qR y)).mp hqb))
      exact False.elim (by rw [← hl hy, heq] at hly; exact lt_irrefl _ hly.2)
  have hcases := affine_closed_piece_boundary_or_endpoint
    (s.finite_toSet.isCompact_convexHull ℝ).isClosed (convex_convexHull ℝ _)
    (hqPL.continuousOn.mono hsub) isClosed_frontier l hab
    (fun y hy => (hl hy) ▸ (ht y).1) hbetween
  rcases hcases with hold | hleft | hright
  · exact Or.inl hold
  · refine Or.inr (Or.inl ?_)
    intro y hy
    apply (mem_sourceSurface_iff phi (a : C) (qR y)).mpr
    exact (ht y).2.symm.trans
      (congrArg (fun r : ℝ => (r : C)) ((hl hy).trans (hleft y hy)))
  · refine Or.inr (Or.inr ?_)
    intro y hy
    apply (mem_sourceSurface_iff phi (b : C) (qR y)).mpr
    exact (ht y).2.symm.trans
      (congrArg (fun r : ℝ => (r : C)) ((hl hy).trans (hright y hy)))

end PoincareConjecture.M76.HamiltonIntervalTorus
