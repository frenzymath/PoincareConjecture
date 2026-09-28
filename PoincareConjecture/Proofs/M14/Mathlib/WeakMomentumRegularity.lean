import PoincareConjecture.Proofs.M08.WeakVelocity
import PoincareConjecture.Proofs.M08.ChartRegularity
import Mathlib.Analysis.ODE.PicardLindelof

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology intervalIntegral

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem contDiffOn_of_weak_linear_momentum {a b : ℝ} (hab : a < b)
    {S : Set E} (A : ℝ × E → E →L[ℝ] E) (F : ℝ → E × E → E)
    (hA : ContDiffOn ℝ ∞ A (Icc a b ×ˢ S))
    (hunit : ∀ z ∈ Icc a b ×ˢ S, IsUnit (A z))
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc a b ×ˢ (S ×ˢ univ)))
    (u : ℝ → E) (hu : ContDiffOn ℝ 1 u (Icc a b)) (hmem : MapsTo u (Icc a b) S)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ s in a..b, deriv φ s • A (s, u s) (derivWithin u (Icc a b) s)) =
        -(∫ s in a..b, φ s • F s (u s, derivWithin u (Icc a b) s))) :
    ContDiffOn ℝ ∞ u (Icc a b) ∧ ∀ s ∈ Icc a b,
      HasDerivWithinAt (fun t => A (t, u t) (derivWithin u (Icc a b) t))
        (F s (u s, derivWithin u (Icc a b) s)) (Icc a b) s := by
  let C := Icc a b
  let q := derivWithin u C
  let P := fun s => A (s, u s) (q s)
  let Q := fun s => F s (u s, q s)
  have hq : ContinuousOn q C := hu.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hud (s : ℝ) (hs : s ∈ C) : HasDerivWithinAt u (q s) C s :=
    ((hu.differentiableOn (by simp)) s hs).hasDerivWithinAt
  have hgraph : ContinuousOn (fun s => (s, u s)) C :=
    continuousOn_id.prodMk hu.continuousOn
  have hgraphmem : MapsTo (fun s => (s, u s)) C (C ×ˢ S) :=
    fun _ hs => ⟨hs, hmem hs⟩
  have hP : ContinuousOn P C := (hA.continuousOn.comp hgraph hgraphmem).clm_apply hq
  have hQ : ContinuousOn Q C := hF.continuousOn.comp
    (continuousOn_id.prodMk (hu.continuousOn.prodMk hq))
    (fun _ hs => ⟨hs, hmem hs, mem_univ _⟩)
  have hPint : IntervalIntegrable P volume a b := hP.intervalIntegrable_of_Icc hab.le
  have hQint : IntervalIntegrable Q volume a b := hQ.intervalIntegrable_of_Icc hab.le
  obtain ⟨c, hc⟩ := PoincareConjecture.M08.weak_momentum_primitive hab P Q hPint hQint hweak
  have hprimitive (s : ℝ) (hs : s ∈ C) : P s = c + ∫ r in a..s, Q r := by
    have h := intervalIntegral.continuousOn_primitive_interval' hQint left_mem_uIcc
    rw [uIcc_of_le hab.le] at h
    exact (Measure.eqOn_Icc_of_ae_eq volume hab.ne hc hP (continuousOn_const.add h)) hs
  have hca : c = P a := by
    simpa only [intervalIntegral.integral_same, add_zero] using
      (hprimitive a ⟨le_rfl, hab.le⟩).symm
  have hPprimitive (s : ℝ) (hs : s ∈ C) : P s = P a + ∫ r in a..s, Q r := by
    rw [hprimitive s hs, hca]
  obtain ⟨hPd, _⟩ := PoincareConjecture.M08.continuous_primitive_regular hab P Q hQ hPprimitive
  let phase := fun t (z : E × E) =>
    let v := Ring.inverse (A (t, z.1)) z.2
    (v, F t (z.1, v))
  let Ω := C ×ˢ (S ×ˢ (univ : Set E))
  let k := fun z : ℝ × (E × E) => (z.1, z.2.1)
  have hk : ContDiffOn ℝ ∞ k Ω := contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hmap : MapsTo k Ω (C ×ˢ S) := fun _ hz => ⟨hz.1, hz.2.1⟩
  have hB := (PoincareConjecture.M08.contDiffOn_inverse_operator A hA hunit).comp hk hmap
  have hv := hB.clm_apply contDiffOn_snd.snd
  have hforce := hF.comp (contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk hv))
    (fun _ hz => ⟨hz.1, hz.2.1, mem_univ _⟩)
  have hphase : ContDiffOn ℝ ∞ (Function.uncurry phase) Ω := hv.prodMk hforce
  have hinv (s : ℝ) (hs : s ∈ C) : Ring.inverse (A (s, u s)) (P s) = q s :=
    PoincareConjecture.M08.inverse_operator_apply _ (hunit _ (hgraphmem hs)) (q s)
  have hphaseDeriv (s : ℝ) (hs : s ∈ C) :
      HasDerivWithinAt (fun t => (u t, P t)) (phase s (u s, P s)) C s := by
    simpa only [phase, hinv s hs] using (hud s hs).prodMk (hPd s hs)
  have hphaseMem : MapsTo (fun s => (u s, P s)) C (S ×ˢ univ) :=
    fun _ hs => ⟨hmem hs, mem_univ _⟩
  have hsmooth := contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤) hphase hphaseDeriv hphaseMem
  exact ⟨hsmooth.fst, hPd⟩

end ODE
