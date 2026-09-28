import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Frontier.StripReversal
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.TargetTranslation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.SourcePhaseCharts
import PoincareConjecture.Proofs.M76.Rigidity.SourceBoundaryCylinder
import PoincareConjecture.Proofs.M76.Mathlib.AddCirclePLCharts










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



theorem polyhedralPL_original_boundaryTranslation
    {E α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (q : E → R) (hq : ContinuousOn q K.space)
    (hqB : ∀ z ∈ K.space, (q z : X) ∈ frontier R)
    (hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) K.space)
    {w : E → ℝ} (hw : FinitePiecewiseAffineOn w K.space) :
    PolyhedralPLInCharts e (fun z => targetTranslation (w z, (q z : X))) K.space := by
  let f := latticeHandleMapInDomain (Fin 1) (Fin 2) L phi
  let F' := latticeHandleMapInDomain_homotopyRel (Fin 1) (Fin 2) L phi F
  have hfix (x : R) (hx : (x : X) ∈ frontier R) : f x = x :=
    (F'.fst_eq_snd hx).symm
  have hqd : PolyhedralPLInCharts d (fun z => (q z : X)) K.space :=
    (hphi.polyhedralPLInCharts_comp K hK q hq hqPL (fun _ _ => mem_univ _)).congr
      (fun z hz => congrArg Subtype.val (hfix (q z) (hqB z hz)))
  have htranslated := polyhedralPL_targetTranslation hd hqd hw
  let q' : E → R := fun z => ⟨targetTranslation (w z, (q z : X)), (q z).property⟩
  have hq' : ContinuousOn q' K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr htranslated.continuousOn
  have hqB' : MapsTo q' K.space ((Subtype.val : R → X) ⁻¹' frontier R) := by
    intro z hz
    have hb := hqB z hz
    change (targetTranslation (w z, (q z : X))) ∈ frontier R
    change (q z : X) ∈ frontier (closedBall (0 : Fin 1 → ℝ) 1 ×ˢ Set.univ) at hb
    change targetTranslation (w z, (q z : X)) ∈
      frontier (closedBall (0 : Fin 1 → ℝ) 1 ×ˢ Set.univ)
    rw [frontier_prod_univ_eq] at hb ⊢
    exact ⟨hb.1, mem_univ _⟩
  exact hphi.polyhedralPLInCharts_boundary_fixed hfix K hK q' hq' hqB' htranslated




theorem finitePiecewiseAffineOn_sourcePhase_coordinate
    {E α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (q : E → R) (hq : ContinuousOn q K.space)
    (hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) K.space)
    (c : ℝ)
    (hseam : ∀ z ∈ K.space,
      sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (q z)) ≠ (c : C)) :
    FinitePiecewiseAffineOn (fun z => (AddCircle.openPartialHomeomorphCoe p c).symm
      (sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (q z)))) K.space := by
  let A := AddCircle.openPartialHomeomorphCoe p c
  let Bc : Set ℝ := ((↑) : ℝ → C) ⁻¹' {(c : C)}ᶜ
  have hBc : IsOpen Bc := isClosed_singleton.isOpen_compl.preimage (AddCircle.continuous_mk' p)
  have hmod : LocallyPiecewiseAffineOn (toIcoMod (by norm_num : 0 < p) c) Bc :=
    locallyPiecewiseAffineOn_toIcoMod _ c hBc (fun _ h => h)
  have hqc : Continuous (fun z : K.space => (q z : X)) :=
    continuous_subtype_val.comp hq.domRestrict
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, J, V, hJ, hJK, hV, hxV, hVJ, hqi, hcoord⟩ := hqPL.coordinates x
  have hxJ : (x : E) ∈ J.space := hVJ ⟨x, hxV, rfl⟩
  obtain ⟨T, w, hT, hxT, _, hw, hlift⟩ :=
    exists_sourcePhase_lift_in_compatible_chart e d hd phi hphi (q x) (e i)
      (fun j => hphi.source_domain.compatible j i) (hqi hxJ)
  let O : Set K.space := V ∩ (fun z : K.space => (q z : X)) ⁻¹'
    ((e i).source ∩ (e i) ⁻¹' interior T.space)
  have hO : IsOpen O := hV.inter
    (((e i).continuousOn.isOpen_inter_preimage (e i).open_source isOpen_interior).preimage hqc)
  obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO ⟨hxV, hqi hxJ, hxT⟩
  have hNJ : N.space ⊆ J.space := by
    intro y hy
    exact hVJ ⟨⟨y, hNK hy⟩, (hNO hy).1, rfl⟩
  have hqT : MapsTo (fun z => e i (q z)) N.space T.space := by
    intro y hy
    exact interior_subset (hNO (show (⟨y, hNK hy⟩ : K.space) ∈
      Subtype.val ⁻¹' N.space from hy)).2.2
  have hwlift : FinitePiecewiseAffineOn (fun z => w (e i (q z))) N.space :=
    (hw.finitePiecewiseAffineOn hT).comp (hcoord.restrict N hN hNJ) hqT
  have hphase (y : E) (hy : y ∈ N.space) :
      sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (q y)) =
        (w (e i (q y)) : C) := hlift (q y) (hqi (hNJ hy)) (hqT hy)
  have hmapBc : MapsTo (fun z => w (e i (q z))) N.space Bc := by
    intro y hy
    change (w (e i (q y)) : C) ≠ (c : C)
    rw [← hphase y hy]
    exact hseam y (hNK hy)
  have hlocal := hmod.comp_finitePiecewiseAffineOn hwlift hmapBc
  have hfinal : FinitePiecewiseAffineOn (fun z => A.symm
      (sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (q z)))) N.space :=
    hlocal.congr (by
      intro y hy
      change toIcoMod _ c (w (e i (q y))) = A.symm
        (sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (q y)))
      rw [hphase y hy]
      rfl)
  obtain ⟨M, hM, hMN, hMF⟩ := hfinal
  exact ⟨M, W, hM, hW, hxW, fun y hy => hMN.symm.subset (hWN hy), hMF⟩

theorem complementaryOldStripReversal_eq_translation
    (phi : C(H, H)) (a b : ℝ) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (hab : a < b) (hgap : b < a + p)
    (x : ↥(sourceSlab phi a b ∩ frontier R)) :
    let z := oldSlabCoordinates phi a b F x
    let t := (closedPhaseIntervalCoordinatesWide a b hgap).symm z.2
    (complementaryOldStripReversal phi a b F hab hgap x : X) =
      targetTranslation
        ((complementaryIntervalReversal a b hab hgap t : ℝ) - (t : ℝ), (x : X)) := by
  intro z t
  let E := latticeHandleDomainEquiv (Fin 1) (Fin 2) L
  let J := hamiltonOneHierarchyCoordinates
  let w := (complementaryIntervalReversal a b hab hgap t : ℝ) - (t : ℝ)
  have ht : ((t : ℝ) : C) = z.2 :=
    congrArg Subtype.val ((closedPhaseIntervalCoordinatesWide a b hgap).apply_symm_apply z.2)
  have hphase : J.symm (z.1.val, ((complementaryIntervalReversal a b hab hgap t : ℝ) : C)) =
      handleTranslation (w, J.symm (z.1.val, z.2.val)) := by
    apply J.injective
    rw [J.apply_symm_apply, handleTranslation_coordinates, J.apply_symm_apply]
    apply Prod.ext
    · rfl
    · change ((complementaryIntervalReversal a b hab hgap t : ℝ) : C) = (z.2 : C) + (w : C)
      rw [← ht]
      change _ = _ + (((complementaryIntervalReversal a b hab hgap t : ℝ) - (t : ℝ) : ℝ) : C)
      rw [AddCircle.coe_sub]
      abel
  calc
    (complementaryOldStripReversal phi a b F hab hgap x : X) =
        (E.symm (J.symm (z.1.val,
          ((complementaryIntervalReversal a b hab hgap t : ℝ) : C))) : X) := rfl
    _ = (E.symm (handleTranslation (w, J.symm (z.1.val, z.2.val))) : X) := by rw [hphase]
    _ = targetTranslation (w, (x : X)) := by
      rw [handleTranslation_domain]
      congr 1
      exact Prod.ext rfl (congrArg Subtype.val ((oldSlabCoordinates phi a b F).symm_apply_apply x))



theorem polyhedralPL_complementaryOldStripReversal
    {E α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (q : E → ↥(sourceSlab phi a b ∩ frontier R)) (hq : ContinuousOn q K.space)
    (hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) K.space) :
    PolyhedralPLInCharts e
      (fun z => (complementaryOldStripReversal phi a b F hab (by linarith) (q z) : X))
      K.space := by
  let hgap : b < a + p := by linarith
  let qR : E → R := fun z => ⟨q z, sourceSlab_subset phi a b (q z).property.1⟩
  have hqR : ContinuousOn qR K.space := by
    apply Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
    change ContinuousOn (fun z => (q z : X)) K.space
    exact continuous_subtype_val.comp_continuousOn hq
  let z := fun y => oldSlabCoordinates phi a b F (q y)
  let t := fun y => (closedPhaseIntervalCoordinatesWide a b hgap).symm (z y).2
  have hphase (y : E) :
      sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (qR y)) = (z y).2 := by
    apply sourcePhase_eq_on_boundary phi F
    exact (Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary (Fin 1) (Fin 2) L)
      (qR y)).mpr (q y).property.2
  have htphase (y : E) : (((t y : Icc a b) : ℝ) : C) = (z y).2 :=
    congrArg Subtype.val ((closedPhaseIntervalCoordinatesWide a b hgap).apply_symm_apply (z y).2)
  have htcoord (y : E) : (AddCircle.openPartialHomeomorphCoe p 0).symm
      (sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (qR y))) = (t y : ℝ) := by
    rw [hphase y, ← htphase y]
    exact (AddCircle.openPartialHomeomorphCoe p 0).left_inv
      ⟨ha.trans_le (t y).property.1, by simpa only [zero_add] using (t y).property.2.trans_lt hb⟩
  have ht : FinitePiecewiseAffineOn (fun y => (t y : ℝ)) K.space :=
    (finitePiecewiseAffineOn_sourcePhase_coordinate hd phi hphi K hK qR hqR hqPL 0
      (by
        intro y _ hy
        have hm := (mem_sourceSlab_iff phi a b (qR y)).mp (q y).property.1
        rw [hy] at hm
        exact AddCircle.zero_notMem_closedIntervalArc p ha hb hm)).congr
      (fun y _ => htcoord y)
  let l : ℝ →ᴬ[ℝ] ℝ :=
    (-(a + p - b) / (b - a) - 1) • ContinuousAffineMap.id ℝ ℝ +
      ContinuousAffineMap.const ℝ ℝ ((a + p - b) * (1 + a / (b - a)) + b)
  let w := fun y => (complementaryIntervalReversal a b hab hgap (t y) : ℝ) - (t y : ℝ)
  have hw : FinitePiecewiseAffineOn w K.space := (ht.postcomp l).congr (by
    intro y _
    rw [Function.comp_apply, show l (t y) =
      (-(a + p - b) / (b - a) - 1) * (t y : ℝ) +
        ((a + p - b) * (1 + a / (b - a)) + b) from rfl]
    change _ = (complementaryIntervalReversal a b hab hgap (t y) : ℝ) - (t y : ℝ)
    rw [complementaryIntervalReversal_apply]
    simp only [div_eq_mul_inv]
    ring)
  have htranslated := polyhedralPL_original_boundaryTranslation hd phi hphi F K hK qR hqR
    (fun y _ => (q y).property.2) hqPL hw
  exact htranslated.congr (fun y _ =>
    (complementaryOldStripReversal_eq_translation phi a b F hab hgap (q y)).symm)

end PoincareConjecture.M76.HamiltonIntervalTorus
