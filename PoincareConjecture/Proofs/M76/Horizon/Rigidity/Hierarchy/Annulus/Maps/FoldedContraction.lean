import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.NormalizedMap
import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetPhaseRetractionPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SquareAnnulusEulerCount

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem ChartwisePLMap.exists_hamiltonZero_folded_annulus_contraction
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {cut alpha beta theta : ℝ}
    (ha : cut < alpha) (hb : beta < cut + p) (htheta : theta ∈ Icc alpha beta)
    (j : (ℝ × ℝ) → X0) (hj : PolyhedralPLInCharts e j Ann)
    (hslab : ∀ z : Ann, (Q0 (hamiltonZeroAmbientMap phi (j z))).2 ∈
      AddCircle.closedIntervalArc p alpha beta)
    (hrim : ∀ side : Bool, ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint side z)))).2 = (theta : C0)) :
    let u : C(Ann, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩
    PolyhedralPLInCharts d
      (hamiltonZeroTargetPhaseRetraction theta ∘ hamiltonZeroAmbientMap phi ∘ j) Ann ∧
      ∃ H : u.HomotopyRel ((hamiltonZeroTargetPhaseRetraction theta).comp u) Dehn.annulusRims,
        (∀ t z, (Q0 (H (t, z))).1 = (Q0 (u z)).1) ∧
        (∀ t z, (Q0 (H (t, z))).2 ∈ AddCircle.closedIntervalArc p alpha beta) ∧
        ∀ z, (Q0 (H (1, z))).2 = (theta : C0) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  intro u
  obtain ⟨R, D, U01, U23, W, K, _, hD, hU01, hU23, _, hK, hKs, _⟩ :=
    exists_squareAnnulus_count (by norm_num : (0 : ℝ) < 1) (by norm_num : 4 * (1 : ℝ) < 8)
  have hKfinite : K.faces.Finite := by
    rw [hK, hU01, hU23]
    exact ((hD 0).1.union (hD 1).1).union ((hD 2).1.union (hD 3).1)
  have hcomposite : PolyhedralPLInCharts d
      (fun z => hamiltonZeroAmbientMap phi (j z)) Ann := by
    simpa only [hKs] using hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hKfinite
      (by simpa only [hKs] using hj)
  refine ⟨hd.polyhedralPL_hamiltonZeroTargetPhaseRetraction theta hcomposite, ?_⟩
  let f : C(Ann, (C0 × C0) × C0) := ⟨fun z => Q0 (u z), (Q0).continuous.comp u.continuous⟩
  obtain ⟨T, hT⟩ := AddCircle.exists_shifted_closedArc_normal_contraction p
    ha hb htheta f hslab
  let H : u.HomotopyRel ((hamiltonZeroTargetPhaseRetraction theta).comp u) Dehn.annulusRims := {
    toFun := fun z => (Q0).symm (T z)
    continuous_toFun := (Q0).symm.continuous.comp T.continuous_toFun
    map_zero_left := by
      intro z
      rw [T.apply_zero]
      exact (Q0).symm_apply_apply (u z)
    map_one_left := by intro z; rw [T.apply_one]; rfl
    prop' := by
      intro t z hz
      have hphase : (f z).2 = (theta : C0) := by
        rcases hz with ⟨w, rfl⟩ | ⟨w, rfl⟩
        · exact hrim false w
        · exact hrim true w
      change (Q0).symm (T (t, z)) = u z
      rw [T.eq_fst t hphase]
      exact (Q0).symm_apply_apply (u z) }
  have hcoord (t : unitInterval) (z : Ann) : Q0 (H (t, z)) = T (t, z) :=
    (Q0).apply_symm_apply _
  refine ⟨H, ?_, ?_, ?_⟩
  · intro t z
    rw [hcoord]
    exact (hT t z).1
  · intro t z
    rw [hcoord]
    exact (hT t z).2.1
  · intro z
    rw [H.apply_one]
    exact congrArg Prod.snd (hamiltonZeroTargetPhaseRetraction_coordinates theta (u z))

end PoincareConjecture.M76
