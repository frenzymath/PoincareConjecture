import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Hierarchy.Boundary.OriginalPLPartition
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Hierarchy.Boundary.StandardAnnulusPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Hierarchy.Annuli.OriginalCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLGluing

/-!
# The glued frontier comparison is PL in the original atlases

Every finite original-atlas parameter has a constructed finite subdivision
into old-boundary pieces and endpoint-annulus pieces. On old pieces the
given PL map is the identity. On annulus pieces the actual finite inverse
coordinates compose with the literal standard target annulus. Closed
finite pasting retains the whole rims and all intersections.
See Hamilton (1976), Lemma 3 and application, pp. 65--67, and Hudson
(1969), pp. 15--19.
-/

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareMT.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1

/-- Original-atlas PL regularity of the actual glued frontier map on
every finite source parameter, including parameters crossing the rims.
No adapted subdivision or PL certificate for the glued map is assumed. -/
theorem polyhedralPL_original_to_standard_frontier_on_parameter
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
    (G : C(frontier (sourceSlab phi a b), X))
    (hfix : ∀ x : frontier (sourceSlab phi a b), (x : X) ∈ frontier R → G x = x)
    (hphase : ∀ theta htheta (x : frontier (sourceSlab phi a b))
      (hx : (x : X) ∈ sourceSurface phi theta),
      G x = (standardTargetAnnulus theta ((A theta htheta).symm ⟨x, hx⟩) : X))
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (q : V → frontier (sourceSlab phi a b))
    (hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) K.space) :
    PolyhedralPLInCharts d (fun z => G (q z)) K.space := by
  classical
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  have hqN (z : V) : (q z : X) ∈ sourceSlab phi a b :=
    (sourceSlab_isCompact phi a b).isClosed.frontier_subset (q z).property
  let qR : V → R := fun z => ⟨q z, sourceSlab_subset phi a b (hqN z)⟩
  have hqR : ContinuousOn qR K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  have hfixphi (x : R) (hx : (x : X) ∈ frontier R) :
      latticeHandleMapInDomain (Fin 1) (Fin 2) L phi x = x :=
    ((latticeHandleMapInDomain_homotopyRel (Fin 1) (Fin 2) L phi F).fst_eq_snd hx).symm
  obtain ⟨J, hJ, hJK, hpieces⟩ :=
    exists_finite_source_frontier_parameter_partition hd phi hphi ha hab hb hfront K hK q hqPL
  let : Finite J.faces := hJ.to_subtype
  have hmodels (s : J.faces) : ∃ M : SimplicialComplex ℝ V,
      M.faces.Finite ∧ M.space = convexHull ℝ (s.val : Set V) := by
    obtain ⟨M, hM, hMs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
      (fun _ : Unit => s.val) (fun _ => J.indep s.property)
    refine ⟨M, hM, hMs.trans ?_⟩
    simp only [iUnion_const]
  choose M hM hMs using hmodels
  have hMK (s : J.faces) : (M s).space ⊆ K.space :=
    (hMs s).subset.trans ((J.convexHull_subset_space s.property).trans hJK.subset)
  have hpiecePL (s : J.faces) : PolyhedralPLInCharts d (fun z => G (q z)) (M s).space := by
    have hqM := hqPL.restrict_finite (M s) (hM s) (hMK s)
    have hphasePL (theta : C) (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
        (hmap : MapsTo (fun z => (q z : X)) (M s).space (sourceSurface phi theta)) :
        PolyhedralPLInCharts d (fun z => G (q z)) (M s).space := by
      obtain ⟨qt, hqt, hqtval⟩ := exists_standardTargetAnnulus_polyhedral_parameter hd theta
      exact polyhedralPL_annulus_transition_on_parameter hphi.source_domain.compatible
        (A theta htheta) (standardTargetAnnulus theta) (qA theta htheta) qt
        (hqA theta htheta) (hA theta htheta) hqt hqtval
        (M s) (hM s) (fun z => (q z : X)) hqM hmap (fun z => G (q z))
        (fun z => hphase theta htheta (q z) (hmap z.property))
    rcases hpieces s.val s.property with hold | hleft | hright
    · have hcomp := hphi.polyhedralPLInCharts_comp (M s) (hM s) qR
        (hqR.mono (hMK s)) hqM (fun _ _ => mem_univ _)
      apply hcomp.congr
      intro z hz
      have hzB := hold ((hMs s).subset hz)
      change (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi (qR z) : X) = G (q z)
      rw [hfixphi (qR z) hzB, hfix (q z) hzB]
    · exact hphasePL (a : C) (by simp) (hleft.mono_left (hMs s).subset)
    · exact hphasePL (b : C) (by simp) (hright.mono_left (hMs s).subset)
  apply polyhedralPLInCharts_of_finite_cover hd.domain.cover hd.domain.compatible
    K hK M hM (G.continuous.comp_continuousOn hq) hpiecePL
  intro z hz
  obtain ⟨s, hs, hzs⟩ := SimplicialComplex.mem_space_iff.mp (hJK.symm.subset hz)
  exact mem_iUnion.mpr ⟨⟨s, hs⟩, (hMs ⟨s, hs⟩).symm.subset hzs⟩

end PoincareMT.M76.HamiltonIntervalTorus
