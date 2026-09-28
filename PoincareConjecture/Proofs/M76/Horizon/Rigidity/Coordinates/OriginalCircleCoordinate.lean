import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleLifts
import PoincareConjecture.Proofs.M76.Mathlib.AddCirclePLCharts

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩

theorem ChartwisePLMap.locallyPL_hamiltonZero_circle_coordinate {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (c : ℝ) (i : ι) :
    let C := AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) c
    let q := hamiltonZeroCircleMap phi
    LocallyPiecewiseAffineOn ((C.symm ∘ q) ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (q ⁻¹' C.target)) := by
  intro C q
  let U := (e i).target ∩ (e i).symm ⁻¹' (q ⁻¹' C.target)
  have hU : IsOpen U := (e i).symm.continuousOn.isOpen_inter_preimage
    (e i).open_target (C.open_target.preimage q.continuous)
  let B : Set ℝ := ((↑) : ℝ → C0) ⁻¹' {(c : C0)}ᶜ
  have hB : IsOpen B := isClosed_singleton.isOpen_compl.preimage (AddCircle.continuous_mk' _)
  have hmod : LocallyPiecewiseAffineOn (toIcoMod (by norm_num : 0 < 4 * (16 : ℝ)) c) B :=
    locallyPiecewiseAffineOn_toIcoMod _ c hB (fun _ h => h)
  apply LocallyPiecewiseAffineOn.locality
  intro z hz
  obtain ⟨j, K, w, hK, hxj, hxK, hKt, hw, hproj⟩ :=
    exists_hamiltonZeroCircleMap_lift e d hd phi hphi ((e i).symm z)
  let T := (e i).symm.trans (e j)
  have hT : LocallyPiecewiseAffineOn (T : V3 → V3) T.source :=
    ((mem_piecewiseAffineGroupoid_iff V3 T).mp (hphi.source_domain.compatible i j)).1
  let V := (T.source ∩ T ⁻¹' interior K.space) ∩ U
  have hV : IsOpen V := (T.continuousOn.isOpen_inter_preimage T.open_source isOpen_interior).inter hU
  have hzV : z ∈ V := ⟨⟨⟨hz.1, hxj⟩, hxK⟩, hz⟩
  have hwlocal := (hw.finitePiecewiseAffineOn hK).locallyPiecewiseAffineOn_of_subset_interior
    isOpen_interior (Subset.rfl : interior K.space ⊆ interior K.space)
  have hwT : LocallyPiecewiseAffineOn (w ∘ T) V :=
    (hwlocal.comp hT).mono hV inter_subset_left
  have hqformula (y : V3) (hy : y ∈ V) : q ((e i).symm y) = (w (T y) : C0) := by
    have h := hproj (T y) (interior_subset hy.1.2)
    change q ((e j).symm ((e j) ((e i).symm y))) = (w (T y) : C0) at h
    have hyj : (e i).symm y ∈ (e j).source := hy.1.1.2
    rwa [(e j).left_inv hyj] at h
  have hwB : MapsTo (w ∘ T) V B := by
    intro y hy
    change (w (T y) : C0) ≠ (c : C0)
    rw [← hqformula y hy]
    exact hy.2.2
  have hformula : LocallyPiecewiseAffineOn ((C.symm ∘ q) ∘ (e i).symm) V := by
    apply ((hmod.comp hwT).mono hV (fun y hy => ⟨hy, hwB hy⟩)).congr
    intro y hy
    change toIcoMod (by norm_num : 0 < 4 * (16 : ℝ)) c (w (T y)) = C.symm (q ((e i).symm y))
    rw [hqformula y hy]
    rfl
  exact ⟨V, hzV, hformula.mono (hU.inter hV) inter_subset_right⟩

end PoincareConjecture.M76
