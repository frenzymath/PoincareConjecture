import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.Compression.SphericalSlabRemoval
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.Compression.PrescribedPhaseProducts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.FiniteComponentBicollar












set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

private instance period_positive : Fact (0 < p) := ⟨by norm_num⟩

theorem ChartwisePLMap.exists_hamiltonZero_original_spherical_slab_reduction {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)})
    {Nlower Nupper Nselected : Set X0}
    (lower : FrontierResidualModel e Nlower (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}))
    (upper : FrontierResidualModel e Nupper (hamiltonZeroCircleMap phi ⁻¹' {(b : C0)}))
    (theta : ℝ) (htheta : theta = a ∨ theta = b)
    (selected : FrontierResidualModel e Nselected (hamiltonZeroCircleMap phi ⁻¹' {(theta : C0)}))
    (i : Fin selected.count) (sph : ChartwisePLSphere e (selected.components i)) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      PLDomain e (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      frontier (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
        hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} ∧
      ∃ (lowerNew : FrontierResidualModel e Nlower (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}))
        (upperNew : FrontierResidualModel e Nupper (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)})),
        lowerNew.complexity + upperNew.complexity ≤ lower.complexity + upper.complexity ∧
        lowerNew.count + upperNew.count < lower.count + upper.count := by
  classical
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨g, hg, ⟨H⟩, ⟨Fg⟩, hlevelA, hlevelB, hslab, _, _, s, rho, hrho, hproducts⟩ :=
    exists_hamiltonZero_prescribed_phase_products e d hd phi hphi F a b ha hab hb he hfront
  have hlevel : hamiltonZeroCircleMap g ⁻¹' {(theta : C0)} =
      hamiltonZeroCircleMap phi ⁻¹' {(theta : C0)} := by
    rcases htheta with htheta | htheta
    · simpa only [htheta] using hlevelA
    · simpa only [htheta] using hlevelB
  have heG : PLDomain e (hamiltonZeroCircleMap g ⁻¹' AddCircle.closedIntervalArc p a b) :=
    hslab.symm ▸ he
  have hfG : frontier (hamiltonZeroCircleMap g ⁻¹' AddCircle.closedIntervalArc p a b) =
      hamiltonZeroCircleMap g ⁻¹' {(a : C0), (b : C0)} := by
    rw [hslab, hfront]
    have hsplit (q : X0 → C0) : q ⁻¹' {(a : C0), (b : C0)} =
        (q ⁻¹' {(a : C0)}) ∪ (q ⁻¹' {(b : C0)}) := by ext x; simp
    rw [hsplit, hsplit, hlevelA, hlevelB]
  obtain ⟨L, HB, c, K, hL, hK, hKs, hc, hi, hbase, hopen, hphase, _⟩ :=
    hproducts theta htheta
  let r := min rho (min (b - a) (p - (b - a))) / 2
  have hr : 0 < r := by
    dsimp only [r]
    exact half_pos (lt_min hrho (lt_min (sub_pos.mpr hab) (by linarith)))
  have hrmin : r < min rho (min (b - a) (p - (b - a))) := by
    dsimp only [r] at hr ⊢
    linarith
  have hrrho : r < rho := hrmin.trans_le (min_le_left _ _)
  have hrgap : r < b - a := hrmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrcomp : r < p - (b - a) := hrmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Ksmall, hKsmall, hKsmallSpace⟩ := L.exists_finite_interval_product hL (show -r < r by linarith)
  have hsub : L.space ×ˢ Icc (-r) r ⊆ K.space := by
    rw [hKs]
    exact prod_mono subset_rfl (Icc_subset_Icc (neg_le_neg hrrho.le) hrrho.le)
  have hcsmall : PolyhedralPLInCharts e c (L.space ×ˢ Icc (-r) r) :=
    hKsmallSpace ▸ hc.restrict_finite Ksmall hKsmall (hKsmallSpace.subset.trans hsub)
  have hismall : Topology.IsEmbedding
      (fun z : (L.space ×ˢ Icc (-r) r : Set ((s → ℝ × V3) × ℝ)) => c z) :=
    hi.comp (Topology.IsEmbedding.inclusion hsub)
  obtain ⟨J, HJ, hJ, hJL, _, hJbase, hcJ, hiJ, hopenJ⟩ :=
    exists_finite_component_bicollar L hL HB selected.components
      (fun j => (selected.component j).1.isClosed) selected.disjoint selected.cover c hr
      hcsmall hismall hbase (hopen r hr hrrho.le) i
  have hSphase : selected.components i ⊆ hamiltonZeroCircleMap g ⁻¹' {(theta : C0)} :=
    (selected.component i).2.2.1.trans hlevel.symm.subset
  let sign : ℝ := if theta = a then 1 else -1
  have hsign : sign = 1 ∨ sign = -1 := by
    dsimp only [sign]
    split_ifs <;> simp
  have hphaseJ (z : (s → ℝ × V3) × ℝ) (hz : z ∈ J.space ×ˢ Icc (-r) r) :
      hamiltonZeroCircleMap g (c z) = ((theta + sign * z.2 : ℝ) : C0) := by
    have hzL := SimplicialComplex.space_subset_of_le hJL hz.1
    have hzt : z.2 ∈ Icc (-rho) rho :=
      (Icc_subset_Icc (neg_le_neg hrrho.le) hrrho.le) hz.2
    simpa only [AddCircle.coe_add] using hphase z.1 hzL z.2 hzt
  obtain ⟨psi, hpsi, ⟨Hnew⟩, hid, heNew, hfNew, lowerNew, upperNew, hcomplexity, hcount⟩ :=
    hg.exists_hamiltonZero_spherical_slab_removal hI hd Fg ha hab hb heG hfG
      (lower.transportPhase hlevelA.symm) (upper.transportPhase hlevelB.symm)
      theta htheta sph hSphase J hJ HJ c hr hrgap hrcomp hcJ hiJ hJbase hopenJ
      sign hsign hphaseJ
  refine ⟨psi, hpsi, ⟨H.trans Hnew⟩, hid, heNew, hfNew, lowerNew, upperNew, ?_, ?_⟩
  · simpa only [FrontierResidualModel.transportPhase_complexity] using hcomplexity
  · simpa only [FrontierResidualModel.transportPhase_count] using hcount

end PoincareConjecture.M76
