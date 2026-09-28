import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapClassicalJets
import Mathlib.MeasureTheory.Function.Holder











set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev.Euclidean

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {m n : ℕ}
local notation "Source" => EuclideanSpace ℝ (Fin m)
local notation "Target" => EuclideanSpace ℝ (Fin n)

local instance coordinateChangeLinearNorm : NormedAddCommGroup (Source →L[ℝ] Target) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance coordinateChangeLinearSpace : NormedSpace ℝ (Source →L[ℝ] Target) :=
  ContinuousLinearMap.toNormedSpace
local instance coordinateChangeBilinearNorm :
    NormedAddCommGroup (Source →L[ℝ] Source →L[ℝ] Target) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance coordinateChangeBilinearSpace :
    NormedSpace ℝ (Source →L[ℝ] Source →L[ℝ] Target) :=
  ContinuousLinearMap.toNormedSpace






theorem coordinate_change_memWkp_two
    {O : Set Plane} {T : Set Source} (hO : IsOpen O) (hfinite : volume O < ⊤)
    (hT : IsOpen T) {u : Plane → Source} {F : Source → Target}
    (hs : ContDiffOn ℝ ∞ u O) (hu : ∀ j, MemWkp 2 2 (fun z => u z j) O)
    (hF : ContDiffOn ℝ ∞ F T) (huT : MapsTo u O T)
    {C0 C1 C2 A : ℝ} (hval : ∀ z ∈ O, ‖F (u z)‖ ≤ C0)
    (hd1 : ∀ z ∈ O, ‖fderiv ℝ F (u z)‖ ≤ C1)
    (hd2 : ∀ z ∈ O, ‖fderiv ℝ (fderiv ℝ F) (u z)‖ ≤ C2)
    (hgrad : ∀ i z, z ∈ O → ‖boundaryVectorPartial i u z‖ ≤ A) :
    ∀ j, MemWkp 2 2 (fun z => (F (u z)) j) O := by
  let : IsFiniteMeasure (volume.restrict O) := isFiniteMeasure_restrict.mpr hfinite.ne
  let V := fun i => boundaryVectorPartial i u
  have hcomp : ContDiffOn ℝ ∞ (F ∘ u) O := hF.comp hs huT
  have hFc : ContinuousOn (fun z => F (u z)) O := hcomp.continuousOn
  have hD1c : ContinuousOn (fun z => fderiv ℝ F (u z)) O :=
    (hF.continuousOn_fderiv_of_isOpen hT (by simp)).comp hs.continuousOn huT
  have hD2c : ContinuousOn (fun z => fderiv ℝ (fderiv ℝ F) (u z)) O :=
    ((hF.fderiv_of_isOpen hT (m := 1)
      (WithTop.coe_le_coe.mpr le_top)).continuousOn_fderiv_of_isOpen hT
      le_rfl).comp hs.continuousOn huT
  have hD1 : MemLp (fun z => fderiv ℝ F (u z)) ⊤ (volume.restrict O) :=
    memLp_top_of_bound (hD1c.aestronglyMeasurable hO.measurableSet) C1 (by
      filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
      exact hd1 z hz)
  have hD2 : MemLp (fun z => fderiv ℝ (fderiv ℝ F) (u z)) ⊤ (volume.restrict O) :=
    memLp_top_of_bound (hD2c.aestronglyMeasurable hO.measurableSet) C2 (by
      filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
      exact hd2 z hz)
  have hV (i : Fin 2) : MemLp (V i) ⊤ (volume.restrict O) := by
    have hVc : ContinuousOn (V i) O :=
      (hs.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const
    apply memLp_top_of_bound (hVc.aestronglyMeasurable hO.measurableSet) A
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    exact hgrad i z hz
  apply vector_memWkp_two_of_classical_hessian hO hcomp
  · apply MemLp.mono_exponent (q := ⊤) _ le_top
    apply memLp_top_of_bound (hFc.aestronglyMeasurable hO.measurableSet) C0
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    exact hval z hz
  · intro i
    have hraw : MemLp (fun z => fderiv ℝ F (u z) (V i z)) ⊤ (volume.restrict O) :=
      (ContinuousLinearMap.apply ℝ Target («E» := Source)).memLp_of_bilin
        (p := ⊤) (q := ⊤) ⊤ (hV i) hD1
    apply MemLp.ae_eq ?_ (hraw.mono_exponent le_top)
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    rw [fderiv_comp z ((hF.contDiffAt (hT.mem_nhds (huT hz))).differentiableAt (by simp))
      ((hs.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))]
    rfl
  · intro a b
    have hD2V : MemLp (fun z => fderiv ℝ (fderiv ℝ F) (u z) (V a z))
        ⊤ (volume.restrict O) :=
      (ContinuousLinearMap.apply ℝ (Source →L[ℝ] Target) («E» := Source)).memLp_of_bilin
        (p := ⊤) (q := ⊤) ⊤ (hV a) hD2
    have hD2VV : MemLp (fun z => fderiv ℝ (fderiv ℝ F) (u z) (V a z) (V b z))
        2 (volume.restrict O) :=
      ((ContinuousLinearMap.apply ℝ Target («E» := Source)).memLp_of_bilin
        (p := ⊤) (q := ⊤) ⊤ (hV b) hD2V).mono_exponent le_top
    have hHess := hessian_memLp_of_coordinate_memWkp_two hO hs hu a b
    have hD1H : MemLp (fun z => fderiv ℝ F (u z)
        (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)))
        2 (volume.restrict O) :=
      (ContinuousLinearMap.apply ℝ Target («E» := Source)).memLp_of_bilin
        (p := 2) (q := ⊤) 2 hHess hD1
    apply MemLp.ae_eq ?_ (hD2VV.add hD1H)
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    exact (M60.second_fderiv_comp
      ((hF.contDiffAt (hT.mem_nhds (huT hz))).of_le (WithTop.coe_le_coe.mpr le_top))
      ((hs.contDiffAt (hO.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top))
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)).symm

end PoincareConjecture.M64.RampTransport
