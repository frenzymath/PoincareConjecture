import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit
import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean WeakCompactness

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

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

def quadraticForcing (B : Target → Target →L[ℝ] Target →L[ℝ] ℝ)
    (u : Plane → Target) (V : Fin 2 → Plane → Target) : Plane → ℝ :=
  fun z => ∑ i, B (u z) (V i z) (V i z)

def quadraticForcingPartial (B : Target → Target →L[ℝ] Target →L[ℝ] ℝ)
    (u : Plane → Target) (V : Fin 2 → Plane → Target)
    (W : Fin 2 → Fin 2 → Plane → Target) (a : Fin 2) : Plane → ℝ :=
  fun z => ∑ i, (fderiv ℝ B (u z) (V a z) (V i z) (V i z) +
    B (u z) (W a i z) (V i z) + B (u z) (V i z) (W a i z))

private theorem quadratic_term_fderiv_apply
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    {u v : Plane → Target} {z : Plane}
    (hB : DifferentiableAt ℝ B (u z))
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (a : Plane) :
    fderiv ℝ (fun p => B (u p) (v p) (v p)) z a =
      fderiv ℝ B (u z) (fderiv ℝ u z a) (v z) (v z) +
        B (u z) (fderiv ℝ v z a) (v z) + B (u z) (v z) (fderiv ℝ v z a) := by
  have h := ((hB.hasFDerivAt.comp z hu.hasFDerivAt).clm_apply
    hv.hasFDerivAt).clm_apply hv.hasFDerivAt
  simp only [Function.comp_def] at h
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

theorem quadraticForcing_fderiv_apply
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    {u : Plane → Target} {V : Fin 2 → Plane → Target}
    {W : Fin 2 → Fin 2 → Plane → Target} {z : Plane} (a : Fin 2)
    (hB : DifferentiableAt ℝ B (u z)) (hu : DifferentiableAt ℝ u z)
    (hV : ∀ i, DifferentiableAt ℝ (V i) z)
    (hdu : fderiv ℝ u z (EuclideanSpace.single a 1) = V a z)
    (hdV : ∀ i, fderiv ℝ (V i) z (EuclideanSpace.single a 1) = W a i z) :
    fderiv ℝ (quadraticForcing B u V) z (EuclideanSpace.single a 1) =
      quadraticForcingPartial B u V W a z := by
  have hd (i : Fin 2) : DifferentiableAt ℝ
      (fun p => B (u p) (V i p) (V i p)) z :=
    (((hB.comp z hu).clm_apply (hV i)).clm_apply (hV i))
  change fderiv ℝ (fun p : Plane => ∑ i : Fin 2, B (u p) (V i p) (V i p)) z
    (EuclideanSpace.single a 1) = _
  rw [fderiv_fun_sum (fun i _ => hd i)]
  simp only [sum_apply, quadraticForcingPartial]
  apply Finset.sum_congr rfl
  intro i _
  rw [quadratic_term_fderiv_apply hB hu (hV i), hdu, hdV i]

private theorem quadratic_forcing_memLp
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    {u : Plane → Target} {V : Fin 2 → Plane → Target}
    {W : Fin 2 → Fin 2 → Plane → Target} {mu : Measure Plane}
    [IsFiniteMeasure mu]
    (hB : MemLp (fun z => B (u z)) ⊤ mu)
    (hDB : MemLp (fun z => fderiv ℝ B (u z)) ⊤ mu)
    (hV : ∀ i, MemLp (V i) ⊤ mu) (hW : ∀ a i, MemLp (W a i) 2 mu) :
    MemLp (quadraticForcing B u V) 2 mu ∧
      ∀ a, MemLp (quadraticForcingPartial B u V W a) 2 mu := by
  have hBV (i : Fin 2) : MemLp (fun z => B (u z) (V i z)) ⊤ mu :=
    (ContinuousLinearMap.apply ℝ (Target →L[ℝ] ℝ) («E» := Target)).memLp_of_bilin
      (p := ⊤) (q := ⊤) ⊤ (hV i) hB
  have hterm (i : Fin 2) : MemLp (fun z => B (u z) (V i z) (V i z)) 2 mu :=
    ((ContinuousLinearMap.apply ℝ ℝ («E» := Target)).memLp_of_bilin
      (p := ⊤) (q := ⊤) ⊤ (hV i) (hBV i)).mono_exponent le_top
  refine ⟨memLp_finsetSum _ (fun i _ => hterm i), ?_⟩
  intro a
  apply memLp_finsetSum
  intro i _
  have hDBV : MemLp (fun z => fderiv ℝ B (u z) (V a z)) ⊤ mu :=
    (ContinuousLinearMap.apply ℝ (Target →L[ℝ] Target →L[ℝ] ℝ)
      («E» := Target)).memLp_of_bilin (p := ⊤) (q := ⊤) ⊤ (hV a) hDB
  have hDBVV : MemLp (fun z => fderiv ℝ B (u z) (V a z) (V i z)) ⊤ mu :=
    (ContinuousLinearMap.apply ℝ (Target →L[ℝ] ℝ) («E» := Target)).memLp_of_bilin
      (p := ⊤) (q := ⊤) ⊤ (hV i) hDBV
  have h0 : MemLp (fun z => fderiv ℝ B (u z) (V a z) (V i z) (V i z)) 2 mu :=
    ((ContinuousLinearMap.apply ℝ ℝ («E» := Target)).memLp_of_bilin
      (p := ⊤) (q := ⊤) ⊤ (hV i) hDBVV).mono_exponent le_top
  have hBW : MemLp (fun z => B (u z) (W a i z)) 2 mu :=
    (ContinuousLinearMap.apply ℝ (Target →L[ℝ] ℝ) («E» := Target)).memLp_of_bilin
      (p := 2) (q := ⊤) 2 (hW a i) hB
  have h1 : MemLp (fun z => B (u z) (W a i z) (V i z)) 2 mu :=
    (ContinuousLinearMap.apply ℝ ℝ («E» := Target)).memLp_of_bilin
      (p := ⊤) (q := 2) 2 (hV i) hBW
  have h2 : MemLp (fun z => B (u z) (V i z) (W a i z)) 2 mu :=
    (ContinuousLinearMap.apply ℝ ℝ («E» := Target)).memLp_of_bilin
      (p := 2) (q := ⊤) 2 (hW a i) (hBV i)
  exact (h0.add h1).add h2

theorem quadraticForcing_memWkp_one
    {U : Set Plane} {T : Set Target} (hU : IsOpen U)
    (hfinite : volume U < ⊤) (hT : IsOpen T)
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    {u : Plane → Target} {V : Fin 2 → Plane → Target}
    {W : Fin 2 → Fin 2 → Plane → Target}
    (hB : ContDiffOn ℝ 1 B T) (hu : ContDiffOn ℝ 1 u U)
    (hV : ∀ i, ContDiffOn ℝ 1 (V i) U) (huT : MapsTo u U T)
    (hdu : ∀ a z, z ∈ U → fderiv ℝ u z (EuclideanSpace.single a 1) = V a z)
    (hdV : ∀ a i z, z ∈ U →
      fderiv ℝ (V i) z (EuclideanSpace.single a 1) = W a i z)
    {C0 C1 A : ℝ} (hBb : ∀ z ∈ U, ‖B (u z)‖ ≤ C0)
    (hDBb : ∀ z ∈ U, ‖fderiv ℝ B (u z)‖ ≤ C1)
    (hVb : ∀ i z, z ∈ U → ‖V i z‖ ≤ A)
    (hW : ∀ a i, MemLp (W a i) 2 (volume.restrict U)) :
    MemWkp 1 2 (quadraticForcing B u V) U ∧
      ∀ a, MemLp (quadraticForcingPartial B u V W a) 2 (volume.restrict U) ∧
        HasWeakPartialDeriv a (quadraticForcingPartial B u V W a)
          (quadraticForcing B u V) U := by
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hfinite.ne
  have hBc : ContinuousOn (fun z => B (u z)) U := hB.continuousOn.comp hu.continuousOn huT
  have hDBc : ContinuousOn (fun z => fderiv ℝ B (u z)) U :=
    (hB.continuousOn_fderiv_of_isOpen hT le_rfl).comp hu.continuousOn huT
  have hBM : MemLp (fun z => B (u z)) ⊤ (volume.restrict U) :=
    memLp_top_of_bound (hBc.aestronglyMeasurable hU.measurableSet) C0 (by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      exact hBb z hz)
  have hDBM : MemLp (fun z => fderiv ℝ B (u z)) ⊤ (volume.restrict U) :=
    memLp_top_of_bound (hDBc.aestronglyMeasurable hU.measurableSet) C1 (by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      exact hDBb z hz)
  have hVM (i : Fin 2) : MemLp (V i) ⊤ (volume.restrict U) :=
    memLp_top_of_bound ((hV i).continuousOn.aestronglyMeasurable hU.measurableSet) A (by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      exact hVb i z hz)
  obtain ⟨hFM, hDM⟩ := quadratic_forcing_memLp hBM hDBM hVM hW
  have hFs : ContDiffOn ℝ 1 (quadraticForcing B u V) U :=
    ContDiffOn.sum (fun i _ => ((hB.comp hu huT).clm_apply (hV i)).clm_apply (hV i))
  have hD (a : Fin 2) (z : Plane) (hz : z ∈ U) :
      fderiv ℝ (quadraticForcing B u V) z (EuclideanSpace.single a 1) =
        quadraticForcingPartial B u V W a z :=
    quadraticForcing_fderiv_apply a
      ((hB.contDiffAt (hT.mem_nhds (huT hz))).differentiableAt one_ne_zero)
      ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
      (fun i => ((hV i).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
      (hdu a z hz) (fun i => hdV a i z hz)
  have hw (a : Fin 2) : HasWeakPartialDeriv a
      (quadraticForcingPartial B u V W a) (quadraticForcing B u V) U := by
    intro phi hp hc hs
    have h := setIntegral_test_fderiv hU hFs hp hc hs (EuclideanSpace.single a 1)
    have heq : (∫ z in U, phi z *
        fderiv ℝ (quadraticForcing B u V) z (EuclideanSpace.single a 1)) =
        ∫ z in U, quadraticForcingPartial B u V W a z * phi z := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      rw [hD a z hz, mul_comm]
    simp only [smul_eq_mul] at h
    rw [heq] at h
    simp only [mul_comm (fderiv ℝ phi _ _)] at h
    linarith
  refine ⟨MemWkp.one_iff_memW1p.mpr ⟨hFM, ?_⟩, fun a => ⟨hDM a, hw a⟩⟩
  intro a
  exact ⟨quadraticForcingPartial B u V W a, hDM a, hw a⟩

end PoincareConjecture.M64.RampTransport
