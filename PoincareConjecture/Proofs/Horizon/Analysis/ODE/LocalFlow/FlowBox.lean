import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.Smooth
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace Poincare.ODE.LocalFlow

open Set Filter
open scoped ContDiff Topology

private theorem exists_flowBox_of_transverse_equiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {V : E → E} (hV : ContDiffOn ℝ ∞ V U)
    {p : E} (hp : p ∈ U) (A : (F × ℝ) ≃L[ℝ] E) (hA : A (0, 1) = V p) :
    ∃ e : OpenPartialHomeomorph (F × ℝ) E,
      (0, 0) ∈ e.source ∧ e (0, 0) = p ∧ e.target ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ s, (s, 0) ∈ e.source → e (s, 0) = p + A (s, 0)) ∧
      ∀ s t, (s, t) ∈ e.source →
        HasDerivAt (fun r => e (s, r)) (V (e (s, t))) t := by
  obtain ⟨W, δ, Φ, hW, hpW, _, hδ, hΦ, hinit, hmaps, hderiv⟩ :=
    exists_smooth_localFlow hU hV hp
  let B : F × ℝ → E × ℝ := fun z => (p + A (z.1, 0), z.2)
  let f : F × ℝ → E := fun z => Φ (B z)
  let D : Set (F × ℝ) := B ⁻¹' (W ×ˢ Ioo (-δ) δ)
  have hB : ContDiff ℝ ∞ B :=
    (contDiff_const.add (A.contDiff.comp (contDiff_fst.prodMk contDiff_const))).prodMk
      contDiff_snd
  have hD : IsOpen D := (hW.prod isOpen_Ioo).preimage hB.continuous
  have hA0 : A (0, 0) = 0 := map_zero A
  have h0D : (0, 0) ∈ D := by
    change (p + A (0, 0), (0 : ℝ)) ∈ W ×ˢ Ioo (-δ) δ
    rw [hA0, add_zero]
    exact ⟨hpW, by linarith, hδ⟩
  have hf : ContDiffOn ℝ ∞ f D := hΦ.comp hB.contDiffOn (fun _ h => h)
  have hf0 : ContDiffAt ℝ ∞ f (0, 0) := hf.contDiffAt (hD.mem_nhds h0D)
  have hfzero : f (0, 0) = p := by
    simpa [f, B, hA0] using hinit p hpW
  have hleft : (fun s : F => f (s, 0)) =ᶠ[𝓝 0] (fun s => p + A (s, 0)) := by
    have ht : Tendsto (fun s : F => (s, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) := by
      exact (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [ht.eventually (hD.mem_nhds h0D)] with s hs
    exact hinit _ hs.1
  have hdleft : HasFDerivAt (fun s : F => f (s, 0))
      (A.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ F ℝ)) 0 :=
    ((A.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ F ℝ)).hasFDerivAt.const_add p)
      |>.congr_of_eventuallyEq hleft
  have hdright : HasDerivAt (fun t : ℝ => f (0, t)) (V p) 0 := by
    simpa [f, B, hA0, hinit p hpW] using hderiv p hpW 0 h0D.2
  have hd : HasFDerivAt f A.toContinuousLinearMap (0, 0) := by
    have hdf := (hf0.differentiableAt (by simp)).hasFDerivAt
    have heq : fderiv ℝ f (0, 0) = A.toContinuousLinearMap := by
      apply ContinuousLinearMap.prod_ext
      · have hc : HasFDerivAt (fun s : F => f (s, 0))
            ((fderiv ℝ f (0, 0)).comp (ContinuousLinearMap.inl ℝ F ℝ)) 0 :=
          hdf.comp (f := fun s : F => (s, (0 : ℝ))) (0 : F)
            (hasFDerivAt_prodMk_left (0 : F) (0 : ℝ))
        exact hc.unique hdleft
      · have he := (hdf.comp (0 : ℝ) (hasFDerivAt_prodMk_right (0 : F) (0 : ℝ))).unique
          hdright.hasFDerivAt
        rw [he]
        apply ContinuousLinearMap.ext
        intro t
        change t • V p = A (0, t)
        rw [← hA, ← map_smul]
        simp
    rwa [heq] at hdf
  let Q := hf0.toOpenPartialHomeomorph f hd (by simp)
  let N : Set (F × ℝ) := D ∩ (fderiv ℝ f) ⁻¹'
    range ((↑) : ((F × ℝ) ≃L[ℝ] E) → (F × ℝ) →L[ℝ] E)
  have hN : IsOpen N :=
    (hf.continuousOn_fderiv_of_isOpen hD (by simp)).isOpen_inter_preimage hD
      ContinuousLinearEquiv.isOpen
  have h0N : (0, 0) ∈ N := ⟨h0D, A, hd.fderiv.symm⟩
  let e := Q.restrOpen N hN
  have hsource : e.source ⊆ D := fun _ h => h.2.1
  have hecoe : (e : F × ℝ → E) = f := rfl
  refine ⟨e, ⟨hf0.mem_toOpenPartialHomeomorph_source hd (by simp), h0N⟩,
    hfzero, ?_, hf.mono hsource, ?_, ?_, ?_⟩
  · intro y hy
    have hx := hsource (e.map_target hy)
    have hm := hmaps _ hx.1 _ hx.2
    change f (e.symm y) ∈ U at hm
    simpa only [← hecoe, e.right_inv hy] using hm
  · intro y hy
    have hx := e.map_target hy
    obtain ⟨C, hC⟩ := hx.2.2
    have hfat := hf.contDiffAt (hD.mem_nhds (hsource hx))
    apply (e.contDiffAt_symm hy (f₀' := C) ?_ hfat).contDiffWithinAt
    rw [hecoe, hC]
    exact (hfat.differentiableAt (by simp)).hasFDerivAt
  · intro s hs
    exact hinit _ (hsource hs).1
  · intro s t hst
    exact hderiv _ (hsource hst).1 _ (hsource hst).2

private theorem exists_planar_transverse_equiv
    (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0) :
    ∃ A : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2), A (0, 1) = v := by
  let w : EuclideanSpace ℝ (Fin 2) := !₂[-v 1, v 0]
  let L : (ℝ × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) := {
    toFun := fun z => z.1 • w + z.2 • v
    map_add' := by intro a b; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
    map_smul' := by intro c a; simp [smul_add, mul_smul] }
  have hn : v 0 ^ 2 + v 1 ^ 2 ≠ 0 := by
    intro h
    apply hv
    ext i
    fin_cases i
    · change v 0 = 0
      exact sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (v 1)])
    · change v 1 = 0
      exact sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (v 0)])
  have hker : ∀ z, L z = 0 → z = 0 := by
    rintro ⟨s, t⟩ hz
    have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hz
    have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hz
    change s * (-v 1) + t * v 0 = 0 at h0
    change s * v 0 + t * v 1 = 0 at h1
    have hs : s * (v 0 ^ 2 + v 1 ^ 2) = 0 := by
      linear_combination v 0 * h1 - v 1 * h0
    have ht : t * (v 0 ^ 2 + v 1 ^ 2) = 0 := by
      linear_combination v 0 * h0 + v 1 * h1
    exact Prod.ext ((mul_eq_zero.mp hs).resolve_right hn) ((mul_eq_zero.mp ht).resolve_right hn)
  have hi : Function.Injective L := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hxy, sub_self]
  let A := (LinearEquiv.ofInjectiveOfFinrankEq L hi (by simp [Module.finrank_prod])).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  change L (0, 1) = v
  simp [L]

theorem exists_smooth_planar_flowBox
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hV : ContDiffOn ℝ ∞ V U) {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ U) (hne : V p ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
      (0, 0) ∈ e.source ∧ e (0, 0) = p ∧ e.target ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ s t, (s, t) ∈ e.source →
        HasDerivAt (fun r => e (s, r)) (V (e (s, t))) t := by
  obtain ⟨A, hA⟩ := exists_planar_transverse_equiv (V p) hne
  obtain ⟨e, h0, he0, htarget, he, hi, _, ht⟩ :=
    exists_flowBox_of_transverse_equiv hU hV hp A hA
  exact ⟨e, h0, he0, htarget, he, hi, ht⟩

end Poincare.ODE.LocalFlow
