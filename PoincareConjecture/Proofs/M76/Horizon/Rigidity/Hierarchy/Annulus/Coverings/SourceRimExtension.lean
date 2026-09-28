import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.LiftedRimPL
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.HomotopicRimExtension









set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
local notation "I" => Icc (0 : ℝ) 1

theorem exists_hamiltonZero_source_annulus_rim_extension
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j : (ℝ × ℝ) → X0} (hj : PolyhedralPLInCharts e j Ann)
    {theta : C0} {alpha : ℝ}
    (hphase : ∀ z : Ann, (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2 = theta)
    (hlower : ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).2 =
        (alpha : C0))
    (hcover : IsCoveringMap (fun z : Circle =>
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).1.1))
    (Hrim : Circle ≃ₜ Circle)
    (hhom : (ContinuousMap.id Circle).Homotopy (Hrim : C(Circle, Circle)))
    (hlift : ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false (Hrim z))))).1.1 =
        (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint true z)))).1.1) :
    ∃ A : Ann ≃ₜ Ann, A.IsFinitePL ∧
      (∀ z : Circle, A (Dehn.annulusRimPoint false z) = Dehn.annulusRimPoint false z) ∧
      (∀ z : Circle, A (Dehn.annulusRimPoint true z) = Dehn.annulusRimPoint true (Hrim z)) := by
  let q : Bool → Circle ≃ₜ Circle := fun b => if b then Hrim else Homeomorph.refl Circle
  have hq : ∀ b, FinitePiecewiseAffineOn (fun s : ℝ =>
      annulusMap 8 (by norm_num) (q b ((32 * s : ℝ) : Circle), if b then 1 else -1)) I := by
    intro b
    cases b
    · simpa [q, Dehn.annulusRimPoint] using Dehn.finitePiecewiseAffineOn_annulus_rim_period false
    · have h := finitePiecewiseAffineOn_hamiltonZero_lifted_annulus_rims hd hphi hj
        hphase hlower hcover Hrim hlift true
      simpa [q] using h
  have hqhom : (⟨q false, (q false).continuous⟩ : C(Circle, Circle)).Homotopy
      ⟨q true, (q true).continuous⟩ := by
    convert hhom using 1 <;> ext z <;> rfl
  obtain ⟨A, hA, hArim⟩ := Dehn.exists_annulus_homotopic_rim_extension q hqhom hq
  refine ⟨A, hA, ?_, ?_⟩
  · simpa [q] using hArim false
  · simpa [q] using hArim true

end PoincareConjecture.M76
