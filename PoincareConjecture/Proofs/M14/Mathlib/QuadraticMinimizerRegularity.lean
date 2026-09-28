import PoincareConjecture.Proofs.M14.Mathlib.QuadraticVariation
import PoincareConjecture.Proofs.M14.Mathlib.WeakMomentumRegularity
import PoincareConjecture.Proofs.M08.ChartEulerRegularity
import Mathlib.Analysis.Calculus.LocalExtr.Basic










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048

open Set Filter MeasureTheory
open scoped ContDiff Topology intervalIntegral

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

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

private noncomputable local instance trilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace




theorem contDiffOn_of_quadratic_local_minima {a b : ℝ} (hab : a < b) {S : Set E}
    (B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (DB : ℝ × E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : ℝ × E → E →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Icc a b ×ˢ S)) (hV : ContinuousOn V (Icc a b ×ˢ S))
    (hDB : ContDiffOn ℝ ∞ DB (Icc a b ×ˢ S))
    (hDV : ContDiffOn ℝ ∞ DV (Icc a b ×ˢ S))
    (hBd : ∀ z ∈ Icc a b ×ˢ S, HasFDerivAt (fun x => B (z.1, x)) (DB z) z.2)
    (hVd : ∀ z ∈ Icc a b ×ˢ S, HasFDerivAt (fun x => V (z.1, x)) (DV z) z.2)
    (hsym : ∀ z ∈ Icc a b ×ˢ S, ∀ v w : E, B z v w = B z w v)
    (hpos : ∀ z ∈ Icc a b ×ˢ S, ∀ v : E, v ≠ 0 → 0 < B z v v)
    (u : ℝ → E) (hu : ContDiffOn ℝ 1 u (Icc a b)) (hmem : MapsTo u (Icc a b) S)
    (hmin : ∀ η : ℝ → E, ContDiff ℝ ∞ η → tsupport η ⊆ Ioo a b →
      ∃ r : ℝ, 0 < r ∧
        (∀ s ∈ Icc a b, ∀ v ∈ Ioo (-r) r, u s + v • η s ∈ S) ∧
        IsLocalMin (fun v : ℝ => ∫ s in a..b,
          B (s, u s + v • η s)
            (derivWithin u (Icc a b) s + v • deriv η s)
            (derivWithin u (Icc a b) s + v • deriv η s) / 2 +
              V (s, u s + v • η s)) 0) :
    ContDiffOn ℝ ∞ u (Icc a b) ∧ ∀ s ∈ Icc a b,
      HasDerivWithinAt
        (fun t => PoincareConjecture.M08.chartMomentumVector (B (t, u t)) (derivWithin u (Icc a b) t))
        (PoincareConjecture.M08.chartForceVector (DB (s, u s)) (DV (s, u s))
          (derivWithin u (Icc a b) s)) (Icc a b) s := by
  let C := Icc a b
  let q := derivWithin u C
  let A := fun z : ℝ × E => InnerProductSpace.continuousLinearMapOfBilin (B z)
  let F := fun t (z : E × E) => PoincareConjecture.M08.chartForceVector (DB (t, z.1)) (DV (t, z.1)) z.2
  have hA : ContDiffOn ℝ ∞ A (C ×ˢ S) :=
    contDiffOn_const.clm_comp hB
  have hunit : ∀ z ∈ C ×ˢ S, IsUnit (A z) :=
    fun z hz => PoincareConjecture.M08.positive_form_operator_isUnit (B z) (hpos z hz)
  let Ω := C ×ˢ (S ×ˢ (univ : Set E))
  let k := fun z : ℝ × (E × E) => (z.1, z.2.1)
  have hk : ContDiffOn ℝ ∞ k Ω := contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hkmap : MapsTo k Ω (C ×ˢ S) := fun _ hz => ⟨hz.1, hz.2.1⟩
  have hargs : ContDiffOn ℝ ∞
      (fun z : ℝ × (E × E) => ((DB (z.1, z.2.1), DV (z.1, z.2.1)), z.2.2)) Ω :=
    ((hDB.comp hk hkmap).prodMk (hDV.comp hk hkmap)).prodMk contDiffOn_snd.snd
  have hforce := (PoincareConjecture.M08.chartForceVector_contDiff (E := E)).comp_contDiffOn hargs
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) Ω := by
    apply hforce.congr
    intro z _
    rfl
  have hq : ContinuousOn q C := hu.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  let P := fun s => A (s, u s) (q s)
  let Q := fun s => F s (u s, q s)
  have hgraph : ContinuousOn (fun s => (s, u s)) C :=
    continuousOn_id.prodMk hu.continuousOn
  have hgraphmem : MapsTo (fun s => (s, u s)) C (C ×ˢ S) :=
    fun _ hs => ⟨hs, hmem hs⟩
  have hP : ContinuousOn P C := (hA.continuousOn.comp hgraph hgraphmem).clm_apply hq
  have hQraw := PoincareConjecture.M08.chartForceVector_continuousOn
    (hDB.continuousOn.comp hgraph hgraphmem) (hDV.continuousOn.comp hgraph hgraphmem) hq
  have hQ : ContinuousOn Q C := by
    apply hQraw.congr
    intro s _
    rfl
  have hPint : IntervalIntegrable P volume a b := hP.intervalIntegrable_of_Icc hab.le
  have hQint : IntervalIntegrable Q volume a b := hQ.intervalIntegrable_of_Icc hab.le
  have hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ s in a..b, deriv φ s • P s) =
        -(∫ s in a..b, φ s • Q s) := by
    intro φ hφ _ hsupp
    apply PoincareConjecture.M08.weak_momentum_of_scalar_stationarity P Q hPint hQint φ hφ
    intro z
    let η := fun s => φ s • z
    have hη : ContDiff ℝ ∞ η := hφ.smul contDiff_const
    have hηsupp : tsupport η ⊆ Ioo a b :=
      (tsupport_smul_subset_left φ (fun _ : ℝ => z)).trans hsupp
    obtain ⟨r, hr, hshift, hlocal⟩ := hmin η hη hηsupp
    have hd := intervalIntegral.hasDerivAt_quadratic_variation hab.le isOpen_Ioo
      (show (0 : ℝ) ∈ Ioo (-r) r from ⟨neg_lt_zero.mpr hr, hr⟩)
      B V DB DV hB.continuousOn hV hDB.continuousOn hDV.continuousOn hBd hVd hsym
      u q η (deriv η) hu.continuousOn hq hη.continuous.continuousOn
      (hη.continuous_deriv (by simp)).continuousOn
      (fun s hs v hv => ⟨hs, hshift s hs v hv⟩)
    have hz : (∫ s in a..b, DB (s, u s) (η s) (q s) (q s) / 2 +
        B (s, u s) (q s) (deriv η s) + DV (s, u s) (η s)) = 0 :=
      hd.2.deriv.symm.trans hlocal.deriv_eq_zero
    rw [← hz]
    apply intervalIntegral.integral_congr
    intro s _
    have hηd : deriv η s = deriv φ s • z := deriv_smul_const ((hφ.differentiable (by simp)) s) z
    change deriv φ s * inner ℝ z (PoincareConjecture.M08.chartMomentumVector (B (s, u s)) (q s)) +
      φ s * inner ℝ z (PoincareConjecture.M08.chartForceVector (DB (s, u s)) (DV (s, u s)) (q s)) = _
    dsimp only
    rw [PoincareConjecture.M08.chartMomentumVector_inner, PoincareConjecture.M08.chartForceVector_inner, hηd]
    simp only [η, map_smul, smul_apply, smul_eq_mul]
    ring
  exact contDiffOn_of_weak_linear_momentum hab A F hA hunit hF u hu hmem hweak

end ODE
