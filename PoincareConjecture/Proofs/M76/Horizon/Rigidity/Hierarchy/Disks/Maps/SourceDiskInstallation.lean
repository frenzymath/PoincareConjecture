import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.Tangential
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.Displacement.RetainedRectangle

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "Disk" => Metric.closedBall (0 : V2) 1
local notation "Rim" => (Set.ofPred (fun z : Disk => (z : V2) ∈ Metric.sphere (0 : V2) 1))
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem ChartwisePLMap.exists_hamiltonZero_third_phase_adjustment
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (W : C(X0, V3))
    (hW : ∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target)
    (hWphase : ∀ x, W x 0 = 0)
    {B : Set X0} (hWzero : ∀ x ∈ B, W x = 0) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
      (∀ x, hamiltonZeroAmbientMap psi x =
        hamiltonZeroTargetVectorTranslation (W x, hamiltonZeroAmbientMap phi x)) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) B,
        ∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x := by
  let G : C(unitInterval × X0, X0) :=
    ⟨fun z => hamiltonZeroTargetVectorTranslation
      ((z.1 : ℝ) • W z.2, hamiltonZeroAmbientMap phi z.2),
      hamiltonZeroTargetVectorTranslation.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).smul
          (W.continuous.comp continuous_snd)).prodMk
          ((hamiltonZeroAmbientMap phi).continuous.comp continuous_snd))⟩
  have hGzero (x : X0) : G (0, x) = hamiltonZeroAmbientMap phi x := by
    change hamiltonZeroTargetVectorTranslation ((0 : ℝ) • W x, _) = _
    rw [zero_smul, hamiltonZeroTargetVectorTranslation_zero]
  have hGone (x : X0) : G (1, x) =
      hamiltonZeroTargetVectorTranslation (W x, hamiltonZeroAmbientMap phi x) := by
    change hamiltonZeroTargetVectorTranslation ((1 : ℝ) • W x, _) = _
    rw [one_smul]
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let psi := hamiltonZeroHandleMap g
  have hg (x : X0) : hamiltonZeroAmbientMap psi x = G (1, x) := by
    rw [hamiltonZeroAmbientMap_handle]
    rfl
  have hphase (t : unitInterval) (x : X0) :
      (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x := by
    change (Q0 (hamiltonZeroTargetVectorTranslation
      ((t : ℝ) • W x, hamiltonZeroAmbientMap phi x))).1.1 = _
    rw [hamiltonZeroTargetVectorTranslation_coordinates]
    simp only [Pi.smul_apply, smul_eq_mul, hWphase, mul_zero, AddCircle.coe_zero, add_zero]
    exact (hamiltonZeroThirdCircleMap_ambient phi x).symm
  refine ⟨psi, ?_, ⟨hamiltonZeroHandleHomotopy phi G hGzero⟩,
    ⟨F.trans (hamiltonZeroHandleHomotopy phi G hGzero)⟩, ?_,
    fun x => (hg x).trans (hGone x), ?_⟩
  · rw [hamiltonZeroHandleMap_domain]
    have heq : g = ⟨fun x => hamiltonZeroTargetVectorTranslation
        (W x, hamiltonZeroAmbientMap phi x),
      hamiltonZeroTargetVectorTranslation.continuous.comp
        (W.continuous.prodMk (hamiltonZeroAmbientMap phi).continuous)⟩ :=
      ContinuousMap.ext hGone
    rw [heq]
    exact chartwisePL_hamiltonZero_vector_translation hd hphi W hW
  · apply ContinuousMap.ext
    intro x
    rw [hamiltonZeroThirdCircleMap_ambient, hg]
    exact hphase 1 x
  · refine ⟨{
      toFun := G
      continuous_toFun := G.continuous
      map_zero_left := hGzero
      map_one_left := fun x => (hg x).symm
      prop' := ?_ }, hphase⟩
    intro t x hx
    change hamiltonZeroTargetVectorTranslation ((t : ℝ) • W x, _) = _
    rw [hWzero x hx, smul_zero, hamiltonZeroTargetVectorTranslation_zero]

theorem exists_hamiltonZero_retained_marked_disk_installation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
    {j q : V2 → X0} (hj : PolyhedralPLInCharts e j Disk)
    (hji : Topology.IsEmbedding (fun z : Disk => j z))
    (hjR : ∀ z : Disk, j z ∈ R)
    (hrim : ∀ z : Disk,
      (z : V2) ∈ Metric.sphere (0 : V2) 1 ↔ j z ∈ frontier R)
    (hq : PolyhedralPLInCharts d q Disk)
    {v : C(Disk, X0)} (hv : ∀ z : Disk, q z = v z)
    (hphase : ∀ z : Disk, (Q0 (v z)).1.1 =
      (Q0 (hamiltonZeroAmbientMap phi (j z))).1.1)
    (H : (⟨fun z : Disk => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩ :
      C(Disk, X0)).HomotopyRel v Rim)
    {cut alpha beta cut' a b : ℝ} (halpha : cut < alpha) (hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (horder : a ≤ b) (hb : b < cut' + p)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hvSecondArc : ∀ z : Disk, (Q0 (v z)).1.2 ∈ AddCircle.closedIntervalArc p a b)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hvArc : ∀ z : Disk, (Q0 (v z)).2 ∈ AddCircle.closedIntervalArc p alpha beta) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
      (∀ z : Disk, hamiltonZeroAmbientMap psi (j z) = v z) ∧
      (R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) ∧
      (R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x) ∧
        ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let : Fact (0 < p) := ⟨by norm_num⟩
  let u : C(Disk, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j z),
    (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩
  obtain ⟨w, hw, hwphase, hwrim, hwval⟩ :=
    exists_hamiltonZero_relative_disk_displacement hd hphi hj hq hv hphase H
  obtain ⟨W, hW, hWbase, hWzero, hWphase, hWoutside⟩ :=
    exists_original_retained_disk_displacement_extension e heR hj hji
      (fun x hx => hjR ⟨x, hx⟩) hrim
      w hw (fun z hz => hwphase ⟨z, hz⟩) hwrim
  have hWprotected (x : X0) (hx : x ∉ interior R) : W x = 0 := by
    by_cases hxR : x ∈ R
    · exact hWzero x ⟨subset_closure hxR, hx⟩
    · exact hWoutside x hxR
  let coord (k : Bool) : C(X0, C0) := ⟨fun x => if k then (Q0 x).1.2 else (Q0 x).2, by
    cases k <;> dsimp <;> fun_prop⟩
  let wn (i : Fin 3) : C(Disk, ℝ) := ⟨fun z => w z i,
    (continuous_apply i).comp hw.continuousOn.domRestrict⟩
  have hwn (k : Bool) (z : Disk) :
      (wn (if k then 1 else 2) z : C0) = coord k (v z) - coord k (u z) := by
    have h := congrArg (fun x : X0 => coord k x) ((hwval z).trans (hv z))
    cases k
    · change (Q0 (hamiltonZeroTargetVectorTranslation (_, _))).2 = _ at h
      rw [hamiltonZeroTargetVectorTranslation_coordinates] at h
      exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
    · change (Q0 (hamiltonZeroTargetVectorTranslation (_, _))).1.2 = _ at h
      rw [hamiltonZeroTargetVectorTranslation_coordinates] at h
      exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
  have hnBound := hamiltonZero_disk_coordinate_displacement_bound
    ((coord false).comp u) ((coord false).comp v) halpha hab hbeta
    (fun z => hR (hjR z)) hvArc (wn 2) (hwn false)
    (fun z hz => congrFun (hwrim z hz) 2)
  have hmBound := hamiltonZero_disk_coordinate_displacement_bound
    ((coord true).comp u) ((coord true).comp v) ha horder hb
    (fun z => hsecond (hjR z)) hvSecondArc (wn 1) (hwn true)
    (fun z hz => congrFun (hwrim z hz) 1)
  obtain ⟨V, hVPL, hVphase, hVzero, _, hVsame, hVarc⟩ :=
    exists_hamiltonZero_retained_rectangle_displacement hd hphi heR halpha hab hbeta
      ha horder hb hR hsecond W hW hWphase hWprotected
  have hVbase (z : Disk) : V (j z) = w z := by
    rw [hVsame (j z) (hjR z) (by
      rw [hWbase z]
      exact (hnBound z).2) (by
      rw [hWbase z]
      exact (hmBound z).2), hWbase z]
  obtain ⟨psi, hpsi, Hpsi, Fpsi, hsame, hformula, _, _⟩ :=
    hphi.exists_hamiltonZero_third_phase_adjustment hd F V hVPL hVphase hVzero
  let G : (hamiltonZeroAmbientMap phi).HomotopyRel
      (hamiltonZeroAmbientMap psi) (interior R)ᶜ := {
    toFun := fun z => hamiltonZeroTargetVectorTranslation
      ((z.1 : ℝ) • V z.2, hamiltonZeroAmbientMap phi z.2)
    continuous_toFun := hamiltonZeroTargetVectorTranslation.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).smul
        (V.continuous.comp continuous_snd)).prodMk
        ((hamiltonZeroAmbientMap phi).continuous.comp continuous_snd))
    map_zero_left := by
      intro x
      change hamiltonZeroTargetVectorTranslation ((0 : ℝ) • V x, _) = _
      rw [zero_smul, hamiltonZeroTargetVectorTranslation_zero]
    map_one_left := by
      intro x
      change hamiltonZeroTargetVectorTranslation ((1 : ℝ) • V x, _) = _
      rw [one_smul]
      exact (hformula x).symm
    prop' := by
      intro t x hx
      change hamiltonZeroTargetVectorTranslation ((t : ℝ) • V x, _) = _
      rw [hVzero x hx, smul_zero, hamiltonZeroTargetVectorTranslation_zero] }
  have hGarc (t : unitInterval) (x : X0) (hx : x ∈ R) :
      (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
      (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p a b := hVarc x hx t
  refine ⟨psi, hpsi, Hpsi, Fpsi, hsame, ?_, ?_, ?_, G, ?_, hGarc⟩
  · intro z
    rw [hformula, hVbase]
    exact (hwval z).trans (hv z)
  · intro x hx
    have h := hGarc 1 x hx
    rw [G.apply_one] at h
    exact h.1
  · intro x hx
    have h := hGarc 1 x hx
    rw [G.apply_one] at h
    exact h.2
  · intro t x
    change (Q0 (hamiltonZeroTargetVectorTranslation
      ((t : ℝ) • V x, hamiltonZeroAmbientMap phi x))).1.1 = _
    rw [hamiltonZeroTargetVectorTranslation_coordinates]
    simp only [Pi.smul_apply, smul_eq_mul, hVphase, mul_zero, AddCircle.coe_zero, add_zero]
    exact (hamiltonZeroThirdCircleMap_ambient phi x).symm

theorem exists_hamiltonZero_retained_source_disk_installation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
    (j : V2 → X0) (hj : PolyhedralPLInCharts e j Disk)
    (hji : Topology.IsEmbedding (fun z : Disk => j z))
    (hjR : ∀ z : Disk, j z ∈ R)
    (hrim : ∀ z : Disk, (z : V2) ∈ Metric.sphere (0 : V2) 1 ↔ j z ∈ frontier R)
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (horder : a ≤ b) (hb : b < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (theta : C0) (hthird : ∀ z : Disk, hamiltonZeroThirdCircleMap phi (j z) = theta) :
    ∃ (v w : V2 → ℝ) (q : V2 → X0) (psi : C(H0, H0)),
      FinitePiecewiseAffineOn v Disk ∧ FinitePiecewiseAffineOn w Disk ∧
      (∀ z ∈ Disk, v z ∈ Icc alpha beta ∧ w z ∈ Icc a b) ∧
      PolyhedralPLInCharts d q Disk ∧
      (∀ z ∈ Disk, Q0 (q z) = ((theta, (w z : C0)), (v z : C0))) ∧
      EqOn q (fun z => hamiltonZeroAmbientMap phi (j z)) (Metric.sphere (0 : V2) 1) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
      (∀ z : Disk, hamiltonZeroAmbientMap psi (j z) = q z) ∧
      (R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) ∧
      (R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x) ∧
        ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  obtain ⟨v, w, q, hv, hw, hrange, hq, hcoords, hboundary, qD, hqD, H, _⟩ :=
    exists_hamiltonZero_source_disk_rectangular_normal_form hd hphi j hj
      halpha hab hbeta ha horder hb
      (fun z hz => hfirst (hjR ⟨z, hz⟩)) (fun z hz => hsecond (hjR ⟨z, hz⟩))
      theta (fun z hz => hthird ⟨z, hz⟩)
  have hphase (z : Disk) : (Q0 (qD z)).1.1 =
      (Q0 (hamiltonZeroAmbientMap phi (j z))).1.1 := by
    rw [hqD, hcoords z z.property]
    exact (hthird z).symm
  have hfirstD (z : Disk) : (Q0 (qD z)).2 ∈ AddCircle.closedIntervalArc p alpha beta := by
    rw [hqD, hcoords z z.property]
    exact ⟨v z, (hrange z z.property).1, rfl⟩
  have hsecondD (z : Disk) : (Q0 (qD z)).1.2 ∈ AddCircle.closedIntervalArc p a b := by
    rw [hqD, hcoords z z.property]
    exact ⟨w z, (hrange z z.property).2, rfl⟩
  obtain ⟨psi, hpsi, Hpsi, Fpsi, hsame, hbase, hRfirst, hRsecond, G, hGphase, hGarc⟩ :=
    exists_hamiltonZero_retained_marked_disk_installation hd hphi F heR hj hji hjR hrim
      hq (fun z => (hqD z).symm) hphase H halpha hab hbeta ha horder hb
      hsecond hsecondD hfirst hfirstD
  exact ⟨v, w, q, psi, hv, hw, hrange, hq, hcoords, hboundary, hpsi, Hpsi, Fpsi,
    hsame, fun z => (hbase z).trans (hqD z), hRfirst, hRsecond, G, hGphase, hGarc⟩

end PoincareConjecture.M76
