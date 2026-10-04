import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.AnnulusDichotomy

/-!
# A marked circle-fibration representative of a folded annulus

Replace the auxiliary normal coordinate by the source cylinder height, then
straighten its tangential map using the actual rim lift. Realizing that
covering at a constant target normal gives a PL folded endpoint with both
original rims fixed. The preceding normal contraction supplies the relative
homotopy from the original source map.
-/

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
local notation "C" => Dehn.annulusCylinderHomeomorph

theorem exists_hamiltonZero_folded_marked_annulus_covering
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j : ℝ × ℝ → X0} (hj : PolyhedralPLInCharts e j Ann)
    {theta : C0} {cut alpha beta delta : ℝ}
    (hcut : cut < alpha) (hbeta : beta < cut + p) (hdelta : delta ∈ Icc alpha beta)
    (hphase : ∀ z : Ann, (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2 = theta)
    (hslab : ∀ z : Ann, (Q0 (hamiltonZeroAmbientMap phi (j z))).2 ∈
      AddCircle.closedIntervalArc p alpha beta)
    (hrim : ∀ side : Bool, ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint side z)))).2 = (delta : C0))
    (f : C(Ann, unitInterval × C0))
    (hf : ∀ z : Ann, (f z).2 = (Q0 (hamiltonZeroAmbientMap phi (j z))).1.1)
    (g : C(Circle, C0))
    (hg : ∀ z, g z = (Q0 (hamiltonZeroAmbientMap phi
      (j (Dehn.annulusRimPoint false z)))).1.1)
    (hgc : IsCoveringMap g) (Hrim : Circle ≃ₜ Circle)
    (L : (ContinuousMap.id Circle).Homotopy (Hrim : C(Circle, Circle)))
    (hlift : ∀ t z, g (L (t, z)) = (f ((C) (t, z))).2) :
    let u : C(Ann, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩
    ∃ c : C(Ann, unitInterval × C0), IsCoveringMap c ∧
      ∃ q : ℝ × ℝ → X0, PolyhedralPLInCharts d q Ann ∧
        (∀ z : Ann, q z = hamiltonZeroAnnulusTargetMap delta delta theta (c z)) ∧
        Nonempty (u.HomotopyRel
          ((hamiltonZeroAnnulusTargetMap delta delta theta).comp c) Dehn.annulusRims) := by
  intro u
  let liftedNormal : C(Ann, unitInterval × C0) :=
    ⟨fun z => (((C).symm z).1, (f z).2), by fun_prop⟩
  have hlift' (t : unitInterval) (z : Circle) :
      g (L (t, z)) = (liftedNormal ((C) (t, z))).2 := hlift t z
  have hnormal (side : Bool) (z : Circle) :
      (liftedNormal (Dehn.annulusRimPoint side z)).1 = if side then 1 else 0 := by
    cases side
    · change ((C).symm (Dehn.annulusRimPoint false z)).1 = 0
      rw [← Dehn.annulusCylinderHomeomorph_zero, Homeomorph.symm_apply_apply]
    · change ((C).symm (Dehn.annulusRimPoint true z)).1 = 1
      rw [← Dehn.annulusCylinderHomeomorph_one, Homeomorph.symm_apply_apply]
  have hcover : IsCoveringMap (fun z : Circle =>
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).1.1) := by
    convert hgc using 1
    funext z
    exact (hg z).symm
  have hupper (z : Circle) :
      (Q0 (hamiltonZeroAmbientMap phi
        (j (Dehn.annulusRimPoint false (Hrim z))))).1.1 =
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint true z)))).1.1 := by
    have h := hlift 1 z
    rw [L.apply_one, Dehn.annulusCylinderHomeomorph_one, hg, hf] at h
    exact h
  obtain ⟨A, hA, hA0, hA1⟩ := exists_hamiltonZero_source_annulus_rim_extension
    hd hphi hj hphase (hrim false) hcover Hrim L hupper
  obtain ⟨D, hD, c, hc, hcf, ⟨Hc⟩⟩ :=
    Dehn.exists_relative_annulus_covering_of_rim_extension liftedNormal g hgc Hrim L
      hlift' hnormal A hA hA0 hA1
  obtain ⟨q, hq, hqval⟩ := exists_hamiltonZero_marked_annulus_covering_PL
    (alpha := delta) (beta := delta) hd hphi hj (fun z => hphase _) (hrim false) D hD
  have hqtarget (z : Ann) : q z = hamiltonZeroAnnulusTargetMap delta delta theta (c z) := by
    rw [hqval, hcf]
    simp only [hamiltonZeroAnnulusTargetMap, ContinuousMap.coe_mk, hg]
  have hstart : (hamiltonZeroAnnulusTargetMap delta delta theta).comp liftedNormal =
      (hamiltonZeroTargetPhaseRetraction delta).comp u := by
    apply ContinuousMap.ext
    intro z
    apply (Q0).injective
    rw [ContinuousMap.comp_apply, hamiltonZeroAnnulusTargetMap_coordinates,
      ContinuousMap.comp_apply, hamiltonZeroTargetPhaseRetraction_coordinates]
    change (((f z).2, theta), (((delta - delta) * _ + delta : ℝ) : C0)) =
      ((Q0 (hamiltonZeroAmbientMap phi (j z))).1, (delta : C0))
    simp only [sub_self, zero_mul, zero_add]
    exact Prod.ext (Prod.ext (hf z) (hphase z).symm) rfl
  obtain ⟨_, T, _, _, _⟩ := hphi.exists_hamiltonZero_folded_annulus_contraction
    hd hcut hbeta hdelta j hj hslab hrim
  exact ⟨c, hc, q, hq, hqtarget,
    ⟨T.trans ((hamiltonZeroAnnulusCoordinateHomotopy Hc theta delta delta).cast hstart rfl)⟩⟩

end PoincareMT.M76
