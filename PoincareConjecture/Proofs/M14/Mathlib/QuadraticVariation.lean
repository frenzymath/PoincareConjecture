import PoincareConjecture.Proofs.M14.Mathlib.ContinuousParameterIntegral
import PoincareConjecture.Proofs.M08.ChartStationarity









set_option autoImplicit false

set_option synthInstance.maxSize 2048

open Set Filter MeasureTheory
open scoped ContDiff Topology intervalIntegral

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable local instance dualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance bilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance bilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

private noncomputable local instance trilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup




theorem hasDerivAt_quadratic_variation {a b : ℝ} (hab : a ≤ b)
    {Ω : Set (ℝ × E)} {P : Set ℝ} (hP : IsOpen P) (hzero : (0 : ℝ) ∈ P)
    (B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (DB : ℝ × E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : ℝ × E → E →L[ℝ] ℝ)
    (hB : ContinuousOn B Ω) (hV : ContinuousOn V Ω)
    (hDB : ContinuousOn DB Ω) (hDV : ContinuousOn DV Ω)
    (hBd : ∀ z ∈ Ω, HasFDerivAt (fun x => B (z.1, x)) (DB z) z.2)
    (hVd : ∀ z ∈ Ω, HasFDerivAt (fun x => V (z.1, x)) (DV z) z.2)
    (hsym : ∀ z ∈ Ω, ∀ v w : E, B z v w = B z w v)
    (u w η ν : ℝ → E) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hη : ContinuousOn η (Icc a b)) (hν : ContinuousOn ν (Icc a b))
    (hmem : ∀ s ∈ Icc a b, ∀ v ∈ P, (s, u s + v • η s) ∈ Ω) :
    IntervalIntegrable (fun s => DB (s, u s) (η s) (w s) (w s) / 2 +
      B (s, u s) (w s) (ν s) + DV (s, u s) (η s)) volume a b ∧
      HasDerivAt (fun v : ℝ => ∫ s in a..b,
        B (s, u s + v • η s) (w s + v • ν s) (w s + v • ν s) / 2 +
          V (s, u s + v • η s))
        (∫ s in a..b, DB (s, u s) (η s) (w s) (w s) / 2 +
          B (s, u s) (w s) (ν s) + DV (s, u s) (η s)) 0 := by
  let C := Icc a b ×ˢ P
  let Γ := fun z : ℝ × ℝ => (z.1, u z.1 + z.2 • η z.1)
  let W := fun z : ℝ × ℝ => w z.1 + z.2 • ν z.1
  have hu' : ContinuousOn (fun z : ℝ × ℝ => u z.1) C :=
    hu.comp continuousOn_fst (fun _ hz => hz.1)
  have hw' : ContinuousOn (fun z : ℝ × ℝ => w z.1) C :=
    hw.comp continuousOn_fst (fun _ hz => hz.1)
  have hη' : ContinuousOn (fun z : ℝ × ℝ => η z.1) C :=
    hη.comp continuousOn_fst (fun _ hz => hz.1)
  have hν' : ContinuousOn (fun z : ℝ × ℝ => ν z.1) C :=
    hν.comp continuousOn_fst (fun _ hz => hz.1)
  have hΓ : ContinuousOn Γ C := continuousOn_fst.prodMk (hu'.add (continuousOn_snd.smul hη'))
  have hW : ContinuousOn W C := hw'.add (continuousOn_snd.smul hν')
  have hmap : MapsTo Γ C Ω := fun z hz => hmem z.1 hz.1 z.2 hz.2
  let L := fun z : ℝ × ℝ => B (Γ z) (W z) (W z) / 2 + V (Γ z)
  let L' := fun z : ℝ × ℝ => DB (Γ z) (η z.1) (W z) (W z) / 2 +
    B (Γ z) (W z) (ν z.1) + DV (Γ z) (η z.1)
  have hL : ContinuousOn L C :=
    ((((hB.comp hΓ hmap).clm_apply hW).clm_apply hW).div_const 2).add (hV.comp hΓ hmap)
  have hL' : ContinuousOn L' C :=
    ((((((hDB.comp hΓ hmap).clm_apply hη').clm_apply hW).clm_apply hW).div_const 2).add
      (((hB.comp hΓ hmap).clm_apply hW).clm_apply hν')).add ((hDV.comp hΓ hmap).clm_apply hη')
  have hd (s : ℝ) (hs : s ∈ Icc a b) (v : ℝ) (hv : v ∈ P) :
      HasDerivAt (fun e => L (s, e)) (L' (s, v)) v :=
    PoincareConjecture.M08.affine_chart_density_hasDerivAt (fun x => B (s, x)) (fun x => V (s, x))
      (DB (s, u s + v • η s)) (DV (s, u s + v • η s)) (u s) (η s) (w s) (ν s) v
      (hBd _ (hmem s hs v hv)) (hVd _ (hmem s hs v hv)) (hsym _ (hmem s hs v hv))
  simpa only [L, L', Γ, W, zero_smul, add_zero] using
    hasDerivAt_integral_of_continuousOn_parameter (μ := volume) hab hP L L' hL hL' hd hzero

end intervalIntegral
