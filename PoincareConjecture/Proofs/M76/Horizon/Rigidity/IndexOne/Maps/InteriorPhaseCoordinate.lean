import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.SourcePhaseCharts
import PoincareConjecture.Proofs.M76.Mathlib.AddCirclePLCharts










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

open Classical in
noncomputable def ambientSourcePhase (phi : C(H, H)) (x : X) : C :=
  if hx : x ∈ R then
    sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L ⟨x, hx⟩) else 0

theorem ambientSourcePhase_domain (phi : C(H, H)) (x : R) :
    ambientSourcePhase phi x =
      sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) := by
  simp only [ambientSourcePhase, dif_pos x.property]

theorem continuousOn_ambientSourcePhase (phi : C(H, H)) :
    ContinuousOn (ambientSourcePhase phi) R := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (fun x : R => ambientSourcePhase phi x) =
      fun x : R => sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) :=
    funext (ambientSourcePhase_domain phi)
  change Continuous (fun x : R => ambientSourcePhase phi x)
  rw [heq]
  exact (sourcePhase phi).continuous.comp (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem locallyPL_interior_circle_coordinate
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (c : ℝ) (i : α) :
    let A := AddCircle.openPartialHomeomorphCoe p c
    let q := ambientSourcePhase phi
    LocallyPiecewiseAffineOn ((A.symm ∘ q) ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (interior R ∩ q ⁻¹' A.target)) := by
  intro A q
  have hW : IsOpen (interior R ∩ q ⁻¹' A.target) :=
    ((continuousOn_ambientSourcePhase phi).mono interior_subset).isOpen_inter_preimage
      isOpen_interior A.open_target
  let U := (e i).target ∩ (e i).symm ⁻¹' (interior R ∩ q ⁻¹' A.target)
  have hU : IsOpen U := (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hW
  let B : Set ℝ := ((↑) : ℝ → C) ⁻¹' {(c : C)}ᶜ
  have hB : IsOpen B := isClosed_singleton.isOpen_compl.preimage (AddCircle.continuous_mk' _)
  have hmod : LocallyPiecewiseAffineOn (toIcoMod (by norm_num : 0 < p) c) B :=
    locallyPiecewiseAffineOn_toIcoMod _ c hB (fun _ h => h)
  apply LocallyPiecewiseAffineOn.locality
  intro z hz
  let x : R := ⟨(e i).symm z, interior_subset hz.2.1⟩
  obtain ⟨K, w, hK, hxK, _, hw, hlift⟩ :=
    exists_sourcePhase_lift_in_compatible_chart e d hd phi hphi x (e i)
      (fun j => hphi.source_domain.compatible j i) ((e i).map_target hz.1)
  have hzK : z ∈ interior K.space := by
    change e i ((e i).symm z) ∈ interior K.space at hxK
    rwa [(e i).right_inv hz.1] at hxK
  let V := interior K.space ∩ U
  have hV : IsOpen V := isOpen_interior.inter hU
  have hwV : LocallyPiecewiseAffineOn w V :=
    (hw.finitePiecewiseAffineOn hK).locallyPiecewiseAffineOn_of_subset_interior hV inter_subset_left
  have hqformula (y : V3) (hy : y ∈ V) : q ((e i).symm y) = (w y : C) := by
    let yR : R := ⟨(e i).symm y, interior_subset hy.2.2.1⟩
    have hyi : e i yR = y := (e i).right_inv hy.2.1
    have h := hlift yR ((e i).map_target hy.2.1)
      (hyi.symm ▸ interior_subset hy.1)
    rw [hyi] at h
    exact (ambientSourcePhase_domain phi yR).trans h
  have hwB : MapsTo w V B := by
    intro y hy
    change (w y : C) ≠ (c : C)
    rw [← hqformula y hy]
    exact hy.2.2.2
  have hlocal : LocallyPiecewiseAffineOn ((A.symm ∘ q) ∘ (e i).symm) V := by
    apply ((hmod.comp hwV).mono hV (fun y hy => ⟨hy, hwB hy⟩)).congr
    intro y hy
    change toIcoMod (by norm_num : 0 < p) c (w y) = A.symm (q ((e i).symm y))
    rw [hqformula y hy]
    rfl
  exact ⟨V, ⟨hzK, hz⟩, hlocal.mono (hU.inter hV) inter_subset_right⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
