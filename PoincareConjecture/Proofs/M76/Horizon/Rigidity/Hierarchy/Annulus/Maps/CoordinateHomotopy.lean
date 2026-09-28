import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.NormalizedMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates









set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

noncomputable def hamiltonZeroAnnulusTargetMap (alpha beta : ℝ) (theta : C0) :
    C(unitInterval × C0, X0) :=
  ⟨fun z => (Q0).symm ((z.2, theta), (((beta - alpha) * (z.1 : ℝ) + alpha : ℝ) : C0)),
    (Q0).symm.continuous.comp
      ((continuous_snd.prodMk continuous_const).prodMk
        ((AddCircle.continuous_mk' p).comp
          ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).add continuous_const)))⟩

theorem hamiltonZeroAnnulusTargetMap_coordinates
    (alpha beta : ℝ) (theta : C0) (z : unitInterval × C0) :
    Q0 (hamiltonZeroAnnulusTargetMap alpha beta theta z) =
      ((z.2, theta), (((beta - alpha) * (z.1 : ℝ) + alpha : ℝ) : C0)) :=
  (Q0).apply_symm_apply _

theorem hamiltonZeroAnnulusTargetMap_mem_closedArc
    (alpha beta : ℝ) (theta : C0) (hab : alpha ≤ beta) (z : unitInterval × C0) :
    (Q0 (hamiltonZeroAnnulusTargetMap alpha beta theta z)).2 ∈
      AddCircle.closedIntervalArc p alpha beta := by
  rw [hamiltonZeroAnnulusTargetMap_coordinates]
  refine ⟨(beta - alpha) * (z.1 : ℝ) + alpha, ⟨?_, ?_⟩, rfl⟩
  · nlinarith [(z.1).property.1]
  · nlinarith [(z.1).property.2]

noncomputable def hamiltonZeroAnnulusCoordinateHomotopy
    {f c : C(Ann, unitInterval × C0)} (H : f.HomotopyRel c Dehn.annulusRims)
    (theta : C0) (alpha beta : ℝ) :
    ((hamiltonZeroAnnulusTargetMap alpha beta theta).comp f).HomotopyRel
      ((hamiltonZeroAnnulusTargetMap alpha beta theta).comp c) Dehn.annulusRims :=
  H.compContinuousMap (hamiltonZeroAnnulusTargetMap alpha beta theta)

theorem hamiltonZeroAnnulusCoordinateHomotopy_coordinates
    {f c : C(Ann, unitInterval × C0)} (H : f.HomotopyRel c Dehn.annulusRims)
    (theta : C0) (alpha beta : ℝ) (t : unitInterval) (z : Ann) :
    Q0 (hamiltonZeroAnnulusCoordinateHomotopy H theta alpha beta (t, z)) =
      (((H (t, z)).2, theta),
        (((beta - alpha) * ((H (t, z)).1 : ℝ) + alpha : ℝ) : C0)) :=
    hamiltonZeroAnnulusTargetMap_coordinates alpha beta theta (H (t, z))

theorem hamiltonZeroAnnulusCoordinateHomotopy_mem_closedArc
    {f c : C(Ann, unitInterval × C0)} (H : f.HomotopyRel c Dehn.annulusRims)
    (theta : C0) {alpha beta : ℝ} (hab : alpha ≤ beta) (t : unitInterval) (z : Ann) :
    (Q0 (hamiltonZeroAnnulusCoordinateHomotopy H theta alpha beta (t, z))).2 ∈
      AddCircle.closedIntervalArc p alpha beta :=
    hamiltonZeroAnnulusTargetMap_mem_closedArc alpha beta theta hab (H (t, z))

theorem hamiltonZeroAnnulusCoordinateHomotopy_zero
    {f c : C(Ann, unitInterval × C0)} (H : f.HomotopyRel c Dehn.annulusRims)
    (theta : C0) (alpha beta : ℝ) (z : Ann) :
    hamiltonZeroAnnulusCoordinateHomotopy H theta alpha beta (0, z) =
      (Q0).symm (((f z).2, theta),
        (((beta - alpha) * ((f z).1 : ℝ) + alpha : ℝ) : C0)) := by
  rw [(hamiltonZeroAnnulusCoordinateHomotopy H theta alpha beta).apply_zero]
  rfl

theorem hamiltonZeroAnnulusCoordinateHomotopy_one
    {f c : C(Ann, unitInterval × C0)} (H : f.HomotopyRel c Dehn.annulusRims)
    (theta : C0) (alpha beta : ℝ) (z : Ann) :
    hamiltonZeroAnnulusCoordinateHomotopy H theta alpha beta (1, z) =
      (Q0).symm (((c z).2, theta),
        (((beta - alpha) * ((c z).1 : ℝ) + alpha : ℝ) : C0)) := by
  rw [(hamiltonZeroAnnulusCoordinateHomotopy H theta alpha beta).apply_one]
  rfl

end PoincareConjecture.M76
