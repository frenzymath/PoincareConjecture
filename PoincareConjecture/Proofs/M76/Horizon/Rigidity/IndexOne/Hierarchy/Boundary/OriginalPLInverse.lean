import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.OriginalPLPartition
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.StandardAnnulusPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.OriginalCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.OriginalPLIdentity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.OriginalToStandard












set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1




theorem polyhedralPL_standard_to_original_frontier_on_parameter
    {V α β : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (sourceSlab phi a b) =
      (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (A : ∀ theta ∈ ({(a : C), (b : C)} : Set C), Ann ≃ₜ sourceSurface phi theta)
    (qA : ∀ theta ∈ ({(a : C), (b : C)} : Set C), (ℝ × ℝ) → X)
    (hqA : ∀ theta htheta, PolyhedralPLInCharts e (qA theta htheta) Ann)
    (hA : ∀ theta htheta (z : Ann), (A theta htheta z : X) = qA theta htheta z)
    (E : frontier (sourceSlab phi a b) ≃ₜ frontier (sourceSlab (ContinuousMap.id H) a b))
    (hfix : ∀ x : frontier (sourceSlab phi a b), (x : X) ∈ frontier R → (E x : X) = x)
    (hphase : ∀ theta htheta (x : frontier (sourceSlab phi a b))
      (hx : (x : X) ∈ sourceSurface phi theta),
      (E x : X) = (standardTargetAnnulus theta ((A theta htheta).symm ⟨x, hx⟩) : X))
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (q : V → frontier (sourceSlab (ContinuousMap.id H) a b))
    (hqPL : PolyhedralPLInCharts d (fun z => (q z : X)) K.space) :
    PolyhedralPLInCharts e (fun z => (E.symm (q z) : X)) K.space := by
  classical
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hfront' := frontier_standard_sourceSlab ha hab.le hb
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  have hqN (z : V) : (q z : X) ∈ sourceSlab (ContinuousMap.id H) a b :=
    (sourceSlab_isCompact (ContinuousMap.id H) a b).isClosed.frontier_subset (q z).property
  let qR : V → R := fun z => ⟨q z, sourceSlab_subset (ContinuousMap.id H) a b (hqN z)⟩
  have hqR : ContinuousOn qR K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  have hinvfix (y : frontier (sourceSlab (ContinuousMap.id H) a b))
      (hy : (y : X) ∈ frontier R) : (E.symm y : X) = y := by
    have hyN := (sourceSlab_isCompact (ContinuousMap.id H) a b).isClosed.frontier_subset y.property
    have hyold : (y : X) ∈ sourceSlab phi a b ∩ frontier R :=
      (old_sourceSlab_eq_of_relative_maps phi (ContinuousMap.id H) a b F (.refl _ _)).symm.subset
        ⟨hyN, hy⟩
    let x : frontier (sourceSlab phi a b) := ⟨y, hfront.symm.subset (Or.inl hyold)⟩
    have hEx : E x = y := Subtype.ext (hfix x hy)
    rw [← hEx, E.symm_apply_apply]
    exact hfix x hy |>.symm
  have hinvphase (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
      (y : frontier (sourceSlab (ContinuousMap.id H) a b))
      (hy : (y : X) ∈ sourceSurface (ContinuousMap.id H) theta) :
      (E.symm y : X) = (A theta htheta ((standardTargetAnnulus theta).symm ⟨y, hy⟩) : X) := by
    let z : sourceSurface phi theta := A theta htheta ((standardTargetAnnulus theta).symm ⟨y, hy⟩)
    have hzfront : (z : X) ∈ frontier (sourceSlab phi a b) := by
      apply hfront.symm.subset
      right
      rcases htheta with rfl | rfl
      · exact Or.inl z.property
      · exact Or.inr z.property
    let x : frontier (sourceSlab phi a b) := ⟨z, hzfront⟩
    have hEx : E x = y := by
      apply Subtype.ext
      rw [hphase theta htheta x z.property]
      change (standardTargetAnnulus theta ((A theta htheta).symm
        (A theta htheta ((standardTargetAnnulus theta).symm ⟨y, hy⟩))) : X) = y
      rw [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
    exact congrArg Subtype.val ((congrArg E.symm hEx).symm.trans (E.symm_apply_apply x))
  have hfixphi (x : R) (hx : (x : X) ∈ frontier R) :
      latticeHandleMapInDomain (Fin 1) (Fin 2) L phi x = x :=
    ((latticeHandleMapInDomain_homotopyRel (Fin 1) (Fin 2) L phi F).fst_eq_snd hx).symm
  obtain ⟨J, hJ, hJK, hpieces⟩ := exists_finite_source_frontier_parameter_partition
    hd (ContinuousMap.id H) (standard_chartwisePLMap_identity hd) ha hab hb hfront' K hK q hqPL
  let : Finite J.faces := hJ.to_subtype
  have hmodels (s : J.faces) : ∃ M : SimplicialComplex ℝ V,
      M.faces.Finite ∧ M.space = convexHull ℝ (s.val : Set V) := by
    obtain ⟨M, hM, hMs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
      (fun _ : Unit => s.val) (fun _ => J.indep s.property)
    exact ⟨M, hM, hMs.trans (by simp only [iUnion_const])⟩
  choose M hM hMs using hmodels
  have hMK (s : J.faces) : (M s).space ⊆ K.space :=
    (hMs s).subset.trans ((J.convexHull_subset_space s.property).trans hJK.subset)
  have hpiecePL (s : J.faces) :
      PolyhedralPLInCharts e (fun z => (E.symm (q z) : X)) (M s).space := by
    have hqM := hqPL.restrict_finite (M s) (hM s) (hMK s)
    have hphasePL (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
        (hmap : MapsTo (fun z => (q z : X)) (M s).space
          (sourceSurface (ContinuousMap.id H) theta)) :
        PolyhedralPLInCharts e (fun z => (E.symm (q z) : X)) (M s).space := by
      obtain ⟨qt, hqt, hqtval⟩ := exists_standardTargetAnnulus_polyhedral_parameter hd theta
      exact polyhedralPL_annulus_transition_on_parameter hd.domain.compatible
        (standardTargetAnnulus theta) (A theta htheta) qt (qA theta htheta)
        hqt hqtval (hqA theta htheta) (hA theta htheta)
        (M s) (hM s) (fun z => (q z : X)) hqM hmap (fun z => (E.symm (q z) : X))
        (fun z => hinvphase theta htheta (q z) (hmap z.property))
    rcases hpieces s.val s.property with hold | hleft | hright
    · have hboundary := hphi.polyhedralPLInCharts_boundary_fixed hfixphi (M s) (hM s) qR
        (hqR.mono (hMK s)) (fun z hz => hold ((hMs s).subset hz)) hqM
      exact hboundary.congr (fun z hz => (hinvfix (q z) (hold ((hMs s).subset hz))).symm)
    · exact hphasePL (a : C) (by simp) (hleft.mono_left (hMs s).subset)
    · exact hphasePL (b : C) (by simp) (hright.mono_left (hMs s).subset)
  apply polyhedralPLInCharts_of_finite_cover hphi.source_domain.cover hphi.source_domain.compatible
    K hK M hM
    ((continuous_subtype_val.comp E.symm.continuous).comp_continuousOn hq) hpiecePL
  intro z hz
  obtain ⟨s, hs, hzs⟩ := SimplicialComplex.mem_space_iff.mp (hJK.symm.subset hz)
  exact mem_iUnion.mpr ⟨⟨s, hs⟩, (hMs ⟨s, hs⟩).symm.subset hzs⟩





theorem exists_original_frontier_inverse_parameter
    {V α β : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (sourceSlab phi a b) =
      (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (A : ∀ theta ∈ ({(a : C), (b : C)} : Set C), Ann ≃ₜ sourceSurface phi theta)
    (qA : ∀ theta ∈ ({(a : C), (b : C)} : Set C), (ℝ × ℝ) → X)
    (hqA : ∀ theta htheta, PolyhedralPLInCharts e (qA theta htheta) Ann)
    (hA : ∀ theta htheta (z : Ann), (A theta htheta z : X) = qA theta htheta z)
    (E : frontier (sourceSlab phi a b) ≃ₜ frontier (sourceSlab (ContinuousMap.id H) a b))
    (hfix : ∀ x : frontier (sourceSlab phi a b), (x : X) ∈ frontier R → (E x : X) = x)
    (hphase : ∀ theta htheta (x : frontier (sourceSlab phi a b))
      (hx : (x : X) ∈ sourceSurface phi theta),
      (E x : X) = (standardTargetAnnulus theta ((A theta htheta).symm ⟨x, hx⟩) : X))
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (qTarget : V → X) (hqTarget : PolyhedralPLInCharts d qTarget K.space)
    (hqfront : MapsTo qTarget K.space (frontier (sourceSlab (ContinuousMap.id H) a b))) :
    ∃ qSource : V → X, PolyhedralPLInCharts e qSource K.space ∧
      ∀ z (hz : z ∈ K.space), qSource z = (E.symm ⟨qTarget z, hqfront hz⟩ : X) := by
  classical
  by_cases hne : K.space.Nonempty
  · obtain ⟨z0, hz0⟩ := hne
    let q : V → frontier (sourceSlab (ContinuousMap.id H) a b) := fun z =>
      if hz : z ∈ K.space then ⟨qTarget z, hqfront hz⟩ else ⟨qTarget z0, hqfront hz0⟩
    have hqval (z : V) (hz : z ∈ K.space) : (q z : X) = qTarget z := by
      simp only [q, dif_pos hz]
    have hq : PolyhedralPLInCharts d (fun z => (q z : X)) K.space :=
      hqTarget.congr (fun z hz => (hqval z hz).symm)
    refine ⟨fun z => (E.symm (q z) : X),
      polyhedralPL_standard_to_original_frontier_on_parameter hd phi hphi F ha hab hb
        hfront A qA hqA hA E hfix hphase K hK q hq, ?_⟩
    intro z hz
    simp only [q, dif_pos hz]
  · have hempty : K.space = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ => 0, ?_, ?_⟩
    · rw [hempty]
      exact ⟨continuousOn_empty _, fun x => False.elim x.property⟩
    · intro z hz
      exact False.elim (hne ⟨z, hz⟩)

end PoincareConjecture.M76.HamiltonIntervalTorus
