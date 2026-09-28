import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.Displacement.FiniteExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceDiskInstallation









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "V2" => (Fin 2 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => (Set.ofPred (fun z : Disk => (z : V2) ∈ sphere (0 : V2) 1))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_finite_marked_disk_installation
    {ι κ η : Type*} [Fintype η]
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
    (j : η → V2 → X0) (hj : ∀ i, PolyhedralPLInCharts e (j i) Disk)
    (hji : ∀ i, Topology.IsEmbedding (fun z : Disk => j i z))
    (hjR : ∀ i, MapsTo (j i) Disk R)
    (hrim : ∀ i, ∀ z : Disk,
      (z : V2) ∈ sphere (0 : V2) 1 ↔ j i z ∈ frontier R)
    (hdis : Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)))
    (q : η → V2 → X0) (hq : ∀ i, PolyhedralPLInCharts d (q i) Disk)
    (v : η → C(Disk, X0)) (hv : ∀ i, ∀ z : Disk, q i z = v i z)
    (hphase : ∀ i, ∀ z : Disk, (Q0 (v i z)).1.1 =
      (Q0 (hamiltonZeroAmbientMap phi (j i z))).1.1)
    (H : ∀ i, (⟨fun z : Disk => hamiltonZeroAmbientMap phi (j i z),
      (hamiltonZeroAmbientMap phi).continuous.comp (hj i).continuousOn.domRestrict⟩ :
      C(Disk, X0)).HomotopyRel (v i) Rim)
    {cut alpha beta cut' a b : ℝ} (halpha : cut < alpha) (hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (horder : a ≤ b) (hb : b < cut' + p)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hvSecondArc : ∀ i, ∀ z : Disk, (Q0 (v i z)).1.2 ∈ AddCircle.closedIntervalArc p a b)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hvArc : ∀ i, ∀ z : Disk, (Q0 (v i z)).2 ∈ AddCircle.closedIntervalArc p alpha beta) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
      (∀ i, ∀ z : Disk, hamiltonZeroAmbientMap psi (j i z) = v i z) ∧
      (R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) ∧
      (R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x) ∧
        ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let : Fact (0 < p) := ⟨by norm_num⟩
  let u (i : η) : C(Disk, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j i z),
    (hamiltonZeroAmbientMap phi).continuous.comp (hj i).continuousOn.domRestrict⟩
  have hex (i : η) := exists_hamiltonZero_relative_disk_displacement
    hd hphi (hj i) (hq i) (hv i) (hphase i) (H i)
  choose w hw hwphase hwrim hwval using hex
  obtain ⟨W, hW, hWbase, hWprotected, hWphase⟩ :=
    exists_original_finite_disk_displacement_extension e heR j hj hji hjR hrim hdis
      w hw (fun i z hz => hwphase i ⟨z, hz⟩) hwrim
  let coord (k : Bool) : C(X0, C0) := ⟨fun x => if k then (Q0 x).1.2 else (Q0 x).2, by
    cases k <;> dsimp <;> fun_prop⟩
  let wn (i : η) (k : Fin 3) : C(Disk, ℝ) := ⟨fun z => w i z k,
    (continuous_apply k).comp (hw i).continuousOn.domRestrict⟩
  have hwn (i : η) (k : Bool) (z : Disk) :
      (wn i (if k then 1 else 2) z : C0) = coord k (v i z) - coord k (u i z) := by
    have h := congrArg (fun x : X0 => coord k x) ((hwval i z).trans (hv i z))
    cases k
    · change (Q0 (hamiltonZeroTargetVectorTranslation (_, _))).2 = _ at h
      rw [hamiltonZeroTargetVectorTranslation_coordinates] at h
      exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
    · change (Q0 (hamiltonZeroTargetVectorTranslation (_, _))).1.2 = _ at h
      rw [hamiltonZeroTargetVectorTranslation_coordinates] at h
      exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
  have hnBound (i : η) := hamiltonZero_disk_coordinate_displacement_bound
    ((coord false).comp (u i)) ((coord false).comp (v i)) halpha hab hbeta
    (fun z => hR (hjR i z.property)) (hvArc i) (wn i 2) (hwn i false)
    (fun z hz => congrFun (hwrim i z hz) 2)
  have hmBound (i : η) := hamiltonZero_disk_coordinate_displacement_bound
    ((coord true).comp (u i)) ((coord true).comp (v i)) ha horder hb
    (fun z => hsecond (hjR i z.property)) (hvSecondArc i) (wn i 1) (hwn i true)
    (fun z hz => congrFun (hwrim i z hz) 1)
  obtain ⟨V, hVPL, hVphase, hVzero, _, hVsame, hVarc⟩ :=
    exists_hamiltonZero_retained_rectangle_displacement hd hphi heR halpha hab hbeta
      ha horder hb hR hsecond W hW hWphase hWprotected
  have hVbase (i : η) (z : Disk) : V (j i z) = w i z := by
    rw [hVsame (j i z) (hjR i z.property) (by
      rw [hWbase i z]
      exact (hnBound i z).2) (by
      rw [hWbase i z]
      exact (hmBound i z).2), hWbase i z]
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
  · intro i z
    rw [hformula, hVbase]
    exact (hwval i z).trans (hv i z)
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




theorem exists_hamiltonZero_source_disk_family_installation
    {ι κ η : Type*} [Fintype η]
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
    (j : η → V2 → X0) (hj : ∀ i, PolyhedralPLInCharts e (j i) Disk)
    (hji : ∀ i, Topology.IsEmbedding (fun z : Disk => j i z))
    (hjR : ∀ i, MapsTo (j i) Disk R)
    (hrim : ∀ i, ∀ z : Disk, (z : V2) ∈ sphere (0 : V2) 1 ↔ j i z ∈ frontier R)
    (hdis : Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)))
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (horder : a ≤ b) (hb : b < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (theta : η → C0) (hthird : ∀ i, ∀ z : Disk, hamiltonZeroThirdCircleMap phi (j i z) = theta i) :
    ∃ (v w : η → V2 → ℝ) (q : η → V2 → X0) (psi : C(H0, H0)),
      (∀ i, FinitePiecewiseAffineOn (v i) Disk) ∧
      (∀ i, FinitePiecewiseAffineOn (w i) Disk) ∧
      (∀ i, ∀ z ∈ Disk, v i z ∈ Icc alpha beta ∧ w i z ∈ Icc a b) ∧
      (∀ i, PolyhedralPLInCharts d (q i) Disk) ∧
      (∀ i, ∀ z ∈ Disk, Q0 (q i z) = ((theta i, (w i z : C0)), (v i z : C0))) ∧
      (∀ i, EqOn (q i) (fun z => hamiltonZeroAmbientMap phi (j i z)) (sphere (0 : V2) 1)) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
      (∀ i, ∀ z : Disk, hamiltonZeroAmbientMap psi (j i z) = q i z) ∧
      (R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) ∧
      (R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x) ∧
        ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  classical
  have hex (i : η) := exists_hamiltonZero_source_disk_rectangular_normal_form
    hd hphi (j i) (hj i) halpha hab hbeta ha horder hb
      (fun z hz => hfirst (hjR i hz)) (fun z hz => hsecond (hjR i hz))
      (theta i) (fun z hz => hthird i ⟨z, hz⟩)
  choose v w q hv hw hrange hq hcoords hboundary qD hqD H hH using hex
  have hphase (i : η) (z : Disk) : (Q0 (qD i z)).1.1 =
      (Q0 (hamiltonZeroAmbientMap phi (j i z))).1.1 := by
    rw [hqD, hcoords i z z.property]
    exact (hthird i z).symm
  have hfirstD (i : η) (z : Disk) : (Q0 (qD i z)).2 ∈ AddCircle.closedIntervalArc p alpha beta := by
    rw [hqD, hcoords i z z.property]
    exact ⟨v i z, (hrange i z z.property).1, rfl⟩
  have hsecondD (i : η) (z : Disk) : (Q0 (qD i z)).1.2 ∈ AddCircle.closedIntervalArc p a b := by
    rw [hqD, hcoords i z z.property]
    exact ⟨w i z, (hrange i z z.property).2, rfl⟩
  obtain ⟨psi, hpsi, Hpsi, Fpsi, hsame, hbase, hRfirst, hRsecond, G, hGphase, hGarc⟩ :=
    exists_hamiltonZero_finite_marked_disk_installation hd hphi F heR
      j hj hji hjR hrim hdis q hq qD (fun i z => (hqD i z).symm) hphase H
      halpha hab hbeta ha horder hb hsecond hsecondD hfirst hfirstD
  exact ⟨v, w, q, psi, hv, hw, hrange, hq, hcoords, hboundary, hpsi, Hpsi, Fpsi,
    hsame, fun i z => (hbase i z).trans (hqD i z), hRfirst, hRsecond, G, hGphase, hGarc⟩

end PoincareConjecture.M76
