import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapClassicalJets
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapForcingSecond

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Euclidean BoundaryTangential

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2

variable {n : ℕ}
local notation "Target" => EuclideanSpace ℝ (Fin n)

local instance : NormedAddCommGroup (Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup
    (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ
    (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem vector_partial_smooth {O : Set Plane} (hO : IsOpen O)
    {u : Plane → Target} (hu : ContDiffOn ℝ ∞ u O) (i : Fin 2) :
    ContDiffOn ℝ ∞ (boundaryVectorPartial i u) O :=
  (hu.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

theorem coordinate_quadraticForcing_memWkp_one
    {O : Set Plane} {T : Set Target} (hO : IsOpen O)
    (hfinite : volume O < ⊤) (hT : IsOpen T)
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ} {u : Plane → Target}
    (hB : ContDiffOn ℝ 1 B T) (hs : ContDiffOn ℝ ∞ u O)
    (hu : ∀ j, MemWkp 2 2 (fun z => u z j) O) (huT : MapsTo u O T)
    {C0 C1 A : ℝ} (hBb : ∀ z ∈ O, ‖B (u z)‖ ≤ C0)
    (hDBb : ∀ z ∈ O, ‖fderiv ℝ B (u z)‖ ≤ C1)
    (hVb : ∀ i z, z ∈ O → ‖boundaryVectorPartial i u z‖ ≤ A) :
    MemWkp 1 2 (quadraticForcing B u (fun i => boundaryVectorPartial i u)) O := by
  let V := fun i => boundaryVectorPartial i u
  let W := fun a i => boundaryVectorPartial a (V i)
  have hVs (i : Fin 2) : ContDiffOn ℝ ∞ (V i) O := vector_partial_smooth hO hs i
  have hV (i : Fin 2) (j : Fin n) : MemWkp 1 2 (fun z => V i z j) O :=
    boundaryVectorPartial_coordinate_memWkp 1 hO (hs.of_le (by simp)) hu i j
  have hW (a i : Fin 2) : MemLp (W a i) 2 (volume.restrict O) := by
    apply MemLp.of_eval_piLp
    intro j
    exact boundaryVectorPartial_coordinate_memWkp 0 hO ((hVs i).of_le (by simp)) (hV i) a j
  exact (quadraticForcing_memWkp_one hO hfinite hT hB (hs.of_le (by simp))
    (fun i => (hVs i).of_le (by simp)) huT (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) hBb hDBb hVb hW).1

theorem coordinate_quadraticForcing_memWkp_two_local
    {W O : Set Plane} {T : Set Target}
    (hW : IsOpen W) (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOW : closure O ⊆ W) (hT : IsOpen T)
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ} {u : Plane → Target}
    (hB : ContDiffOn ℝ 2 B T) (hs : ContDiffOn ℝ ∞ u (W ∩ Half))
    (hu : ∀ j, MemWkp 3 2 (fun z => u z j) (W ∩ Half))
    (huT : MapsTo u (O ∩ Half) T)
    {C0 C1 C2 A : ℝ} (hBb : ∀ z ∈ O ∩ Half, ‖B (u z)‖ ≤ C0)
    (hDBb : ∀ z ∈ O ∩ Half, ‖fderiv ℝ B (u z)‖ ≤ C1)
    (hDDBb : ∀ z ∈ O ∩ Half, ‖fderiv ℝ (fderiv ℝ B) (u z)‖ ≤ C2)
    (hVb : ∀ i z, z ∈ O ∩ Half → ‖boundaryVectorPartial i u z‖ ≤ A) :
    MemWkp 2 2 (quadraticForcing B u (fun i => boundaryVectorPartial i u)) (O ∩ Half) := by
  have hWH : IsOpen (W ∩ Half) := hW.inter isOpen_halfSpace
  have hOH : IsOpen (O ∩ Half) := hO.inter isOpen_halfSpace
  have hsub : O ∩ Half ⊆ W ∩ Half := inter_subset_inter_left _ (subset_closure.trans hOW)
  have hfinite : volume (O ∩ Half) < ⊤ :=
    lt_of_le_of_lt (measure_mono (inter_subset_left.trans subset_closure)) hOc.measure_lt_top
  let V := fun i => boundaryVectorPartial i u
  let Q := fun a i => boundaryVectorPartial a (V i)
  let R := fun b a i => boundaryVectorPartial b (Q a i)
  have hVs (i : Fin 2) : ContDiffOn ℝ ∞ (V i) (W ∩ Half) :=
    vector_partial_smooth hWH hs i
  have hQs (a i : Fin 2) : ContDiffOn ℝ ∞ (Q a i) (W ∩ Half) :=
    vector_partial_smooth hWH (hVs i) a
  have hV (i : Fin 2) (j : Fin n) : MemWkp 2 2 (fun z => V i z j) (W ∩ Half) :=
    boundaryVectorPartial_coordinate_memWkp 2 hWH (hs.of_le (by simp)) hu i j
  have hQ (a i : Fin 2) (j : Fin n) : MemWkp 1 2 (fun z => Q a i z j) (W ∩ Half) :=
    boundaryVectorPartial_coordinate_memWkp 1 hWH ((hVs i).of_le (by simp)) (hV i) a j
  have hQ4 (a i : Fin 2) : MemLp (Q a i) 4 (volume.restrict (O ∩ Half)) := by
    apply MemLp.of_eval_piLp
    intro j
    exact local_halfSpace_H1_memLp_four hW hO hOc hOW (hQ a i j)
  have hR2 (b a i : Fin 2) : MemLp (R b a i) 2 (volume.restrict (O ∩ Half)) := by
    apply MemLp.of_eval_piLp
    intro j
    have h : MemLp (fun z => R b a i z j) 2 (volume.restrict (W ∩ Half)) :=
      boundaryVectorPartial_coordinate_memWkp 0 hWH ((hQs a i).of_le (by simp)) (hQ a i) b j
    exact h.mono_measure (Measure.restrict_mono_set volume hsub)
  exact quadraticForcing_memWkp_two hOH hfinite hT hB
    ((hs.mono hsub).of_le (by simp))
    (fun i => ((hVs i).mono hsub).of_le (by simp))
    (fun a i => ((hQs a i).mono hsub).of_le (by simp)) huT
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    hBb hDBb hDDBb hVb hQ4 hR2

end PoincareConjecture.M64.RampTransport
