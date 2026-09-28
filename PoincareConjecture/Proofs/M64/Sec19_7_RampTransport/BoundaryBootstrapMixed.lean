import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapNonlinear
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapWeakEquation
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapHigher
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapClosedC2

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
local notation "Target" => EuclideanSpace ℝ (Fin (n + 1))

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

theorem local_mixed_memWkp_add_three
    (k : ℕ) {W V : Set Plane} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u : Plane → Target} {f : Fin (n + 1) → Plane → ℝ} {v : Plane → ℝ}
    (huc : Continuous u) (hus : ContDiffOn ℝ 1 u (W ∩ Half))
    (hu : ∀ j, MemWkp (k + 2) 2 (fun z => u z j) (W ∩ Half))
    (hf : ∀ j, MemWkp (k + 1) 2 (f j) (W ∩ Half))
    (hvc : Continuous v) (hn : ∀ z ∈ W, z 0 = 0 → v z = 0)
    (hv : ∀ z ∈ W ∩ Half, v z = boundaryVectorPartial 0 u z 0)
    (ht : ∀ j : Fin (n + 1), j ≠ 0 → ∀ z ∈ W, z 0 = 0 → u z j = 0)
    (heq : ∀ j, ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ W ∩ Half →
      (∫ z in W ∩ Half, ∑ i, chosenWeakPartial' 2 i (fun p => u p j) (W ∩ Half) z *
        fderiv ℝ phi z (EuclideanSpace.single i 1)) =
          ∫ z in W ∩ Half, f j z * phi z) :
    ∀ j, MemWkp (k + 3) 2 (fun z => u z j) (V ∩ Half) := by
  intro j
  by_cases hj : j = 0
  · subst j
    apply local_neumann_memWkp_add_three k hW hWc hV hVc hVW (hu 0)
      ((contDiffOn_piLp 2).mp hus 0) (hf 0) hvc hn
    · intro z hz
      exact (hv z hz).trans (boundaryClassicalPartial_coordinate
        ((hus.contDiffAt ((hW.inter isOpen_halfSpace).mem_nhds hz)).differentiableAt
          (by simp)) 0 0).symm
    · exact heq 0
  · apply local_memWkp_add_two_of_continuous_zero_trace (k + 1) flatBoundaryForm
      hW hWc hV hVc hVW
      (show Continuous (fun z => u z j) from
        (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp huc) (ht j hj)
      (hu j).memW1p (hf j)
    intro phi hphi hc hsupp
    simpa [flatBoundaryForm, Matrix.one_apply] using heq j phi hphi hc hsupp

theorem mixed_quadratic_system_contDiffOn_closure
    {W0 W1 W2 W3 O : Set Plane} {T : Set Target}
    (hW0 : IsOpen W0) (hW0c : IsCompact (closure W0))
    (hW1 : IsOpen W1) (hW1c : IsCompact (closure W1)) (h10 : closure W1 ⊆ W0)
    (hW2 : IsOpen W2) (hW2c : IsCompact (closure W2)) (h21 : closure W2 ⊆ W1)
    (hW3 : IsOpen W3) (hW3c : IsCompact (closure W3)) (h32 : closure W3 ⊆ W2)
    (hO : IsOpen O) (hOc : IsCompact (closure O)) (hconv : Convex ℝ O)
    (hOH : O ⊆ Half) (hO3 : closure O ⊆ W3) (hT : IsOpen T)
    {u : Plane → Target} {v : Plane → ℝ}
    {B : Fin (n + 1) → Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    (huc : Continuous u) (hs : ContDiffOn ℝ ∞ u (W0 ∩ Half))
    (hu : ∀ j, MemWkp 2 2 (fun z => u z j) (W0 ∩ Half))
    (hB : ∀ j, ContDiffOn ℝ 2 (B j) T) (huT : MapsTo u (W0 ∩ Half) T)
    {C0 C1 C2 A : ℝ}
    (hBb : ∀ j z, z ∈ W0 ∩ Half → ‖B j (u z)‖ ≤ C0)
    (hDBb : ∀ j z, z ∈ W0 ∩ Half → ‖fderiv ℝ (B j) (u z)‖ ≤ C1)
    (hDDBb : ∀ j z, z ∈ W0 ∩ Half → ‖fderiv ℝ (fderiv ℝ (B j)) (u z)‖ ≤ C2)
    (hVb : ∀ i z, z ∈ W0 ∩ Half → ‖boundaryVectorPartial i u z‖ ≤ A)
    (hvc : Continuous v) (hn : ∀ z ∈ W0, z 0 = 0 → v z = 0)
    (hv : ∀ z ∈ W0 ∩ Half, v z = boundaryVectorPartial 0 u z 0)
    (ht : ∀ j : Fin (n + 1), j ≠ 0 → ∀ z ∈ W0, z 0 = 0 → u z j = 0)
    (heq : ∀ j z, z ∈ W0 ∩ Half →
      -(∑ i : Fin 2, (fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) j) =
      quadraticForcing (B j) u (fun i => boundaryVectorPartial i u) z) :
    ContDiffOn ℝ 2 u (closure O) := by
  have hS0 := hW0.inter isOpen_halfSpace
  have hS1 := hW1.inter isOpen_halfSpace
  have hS2 := hW2.inter isOpen_halfSpace
  have h10' : W1 ⊆ W0 := subset_closure.trans h10
  have h21' : W2 ⊆ W1 := subset_closure.trans h21
  have h32' : W3 ⊆ W2 := subset_closure.trans h32
  have h20 : W2 ⊆ W0 := h21'.trans h10'
  have hS10 : W1 ∩ Half ⊆ W0 ∩ Half := inter_subset_inter_left _ h10'
  have hS20 : W2 ∩ Half ⊆ W0 ∩ Half := inter_subset_inter_left _ h20
  have hS21 : W2 ∩ Half ⊆ W1 ∩ Half := inter_subset_inter_left _ h21'
  let F := fun j => quadraticForcing (B j) u (fun i => boundaryVectorPartial i u)
  have hfinite : volume (W0 ∩ Half) < ⊤ :=
    lt_of_le_of_lt (measure_mono (inter_subset_left.trans subset_closure)) hW0c.measure_lt_top
  have hF1 (j : Fin (n + 1)) : MemWkp 1 2 (F j) (W0 ∩ Half) :=
    coordinate_quadraticForcing_memWkp_one hS0 hfinite hT ((hB j).of_le (by norm_num))
      hs hu huT (hBb j) (hDBb j) hVb
  have hweak0 := fun j => weak_coordinate_flat_equation_of_classical hS0 hs j (hu j) (heq j)
  have hu3 : ∀ j, MemWkp 3 2 (fun z => u z j) (W1 ∩ Half) :=
    local_mixed_memWkp_add_three 0 hW0 hW0c hW1 hW1c h10 huc
      (hs.of_le (by simp)) hu hF1 hvc hn hv ht hweak0
  have hF2 (j : Fin (n + 1)) : MemWkp 2 2 (F j) (W2 ∩ Half) :=
    coordinate_quadraticForcing_memWkp_two_local hW1 hW2 hW2c h21 hT (hB j)
      (hs.mono hS10) hu3 (fun _ hz => huT (hS20 hz))
      (fun z hz => hBb j z (hS20 hz)) (fun z hz => hDBb j z (hS20 hz))
      (fun z hz => hDDBb j z (hS20 hz)) (fun i z hz => hVb i z (hS20 hz))
  have hu3' (j : Fin (n + 1)) : MemWkp 3 2 (fun z => u z j) (W2 ∩ Half) :=
    (hu3 j).mono_set (by norm_num) hS2 hS21
  have hweak2 := fun j => weak_coordinate_flat_equation_of_classical hS2 (hs.mono hS20)
    j (hu3' j).le_succ (fun z hz => heq j z (hS20 hz))
  have hu4 : ∀ j, MemWkp 4 2 (fun z => u z j) (W3 ∩ Half) :=
    local_mixed_memWkp_add_three 1 hW2 hW2c hW3 hW3c h32 huc
      ((hs.mono hS20).of_le (by simp)) hu3' hF2 hvc
      (fun z hz => hn z (h20 hz)) (fun z hz => hv z (hS20 hz))
      (fun j hj z hz => ht j hj z (h20 hz)) hweak2
  apply local_halfSpace_H4_vector_contDiffOn_closure hW3 hO hOc hconv hOH hO3 hu4
  · apply hs.mono
    intro z hz
    exact ⟨h20 (h32' (hO3 (subset_closure hz))), hOH hz⟩
  · exact huc.continuousOn

end PoincareConjecture.M64.RampTransport
