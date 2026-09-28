import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSupportedHessian









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "D[" i "]" f => fun x : Plane => fderiv ℝ f x (EuclideanSpace.single i 1)

private theorem weak_add {i : Fin 2} {u v p q : Plane → ℝ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hp : MemLp p 2 volume) (hq : MemLp q 2 volume)
    (hw : HasWeakPartialDeriv i p u univ) (hvq : HasWeakPartialDeriv i q v univ) :
    HasWeakPartialDeriv i (fun x => p x + q x) (fun x => u x + v x) univ := by
  intro φ hφ hc hs
  have hφm := hφ.continuous.memLp_of_hasCompactSupport
    (μ := volume) (p := (2 : ℝ≥0∞)) hc
  have hDm := ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    ).memLp_of_hasCompactSupport (μ := volume) (p := (2 : ℝ≥0∞))
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have h1 := hw φ hφ hc hs
  have h2 := hvq φ hφ hc hs
  simp only [Measure.restrict_univ] at h1 h2 ⊢
  simp only [add_mul]
  have hl := integral_add (hu.integrable_mul hDm) (hv.integrable_mul hDm)
  have hr := integral_add (hp.integrable_mul hφm) (hq.integrable_mul hφm)
  simp only [Pi.mul_apply] at hl hr
  rw [hl, hr, h1, h2]
  ring



def suCutoffColumn {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : Plane → ℝ) (u : Plane → E) (p : Fin 2 → Plane → E)
    (i : Fin 2) (x : Plane) : E :=
  χ x • p i x + fderiv ℝ χ x (EuclideanSpace.single i 1) • u x



def suCutoffHessian {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : Plane → ℝ) (u : Plane → E) (p : Fin 2 → Plane → E)
    (H : Fin 2 → Fin 2 → Plane → E) (i j : Fin 2) (x : Plane) : E :=
  (χ x • H i j x + fderiv ℝ χ x (EuclideanSpace.single j 1) • p i x) +
    (fderiv ℝ χ x (EuclideanSpace.single i 1) • p j x +
      fderiv ℝ (D[i] χ) x (EuclideanSpace.single j 1) • u x)



theorem suCutoff_weak_jet {m : ℕ} {O : Set Plane}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    {H : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hu : MemLp u 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun x => p i x b) (fun x => u x b) O)
    (hH : ∀ i j, MemLp (H i j) 2 (volume.restrict O))
    (hwH : ∀ i j b, HasWeakPartialDeriv j (fun x => H i j x b) (fun x => p i x b) O)
    {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ O) :
    MemLp (fun x => χ x • u x) 2 volume ∧
    (∀ i, MemLp (suCutoffColumn χ u p i) 2 volume) ∧
    (∀ i b, HasWeakPartialDeriv i (fun x => suCutoffColumn χ u p i x b)
      (fun x => (χ x • u x) b) univ) ∧
    (∀ i j, MemLp (suCutoffHessian χ u p H i j) 2 volume) ∧
    ∀ i j b, HasWeakPartialDeriv j (fun x => suCutoffHessian χ u p H i j x b)
      (fun x => suCutoffColumn χ u p i x b) univ := by
  have hm {v : Plane → EuclideanSpace ℝ (Fin m)}
      (hv : MemLp v 2 (volume.restrict O)) (b : Fin m)
      (K : Set Plane) (_ : IsCompact K) (hKO : K ⊆ O) :
      MemLp (fun x => v x b) 2 (volume.restrict K) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) b).comp_memLp' hv).mono_measure
      (Measure.restrict_mono hKO le_rfl)
  have hd (i : Fin 2) : ContDiff ℝ ∞ (D[i] χ) :=
    hχ.fderiv_right (by simp) |>.clm_apply contDiff_const
  have hdc (i : Fin 2) : HasCompactSupport (D[i] χ) :=
    hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hds (i : Fin 2) : tsupport (D[i] χ) ⊆ O :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hs
  have h1 (i : Fin 2) (b : Fin m) :=
    Poincare.Analysis.Elliptic.memLp_cutoff_weakPartial i (hm hu b) (hm (hp i) b) hχ hc hs
  have h2 (i j : Fin 2) (b : Fin m) :=
    Poincare.Analysis.Elliptic.memLp_cutoff_weakPartial j
      (hm (hp i) b) (hm (hH i j) b) hχ hc hs
  have h3 (i j : Fin 2) (b : Fin m) :=
    Poincare.Analysis.Elliptic.memLp_cutoff_weakPartial j
      (hm hu b) (hm (hp j) b) (hd i) (hdc i) (hds i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply memLp_piLp_iff.mpr
    intro b
    exact Poincare.Analysis.Elliptic.memLp_mul_of_compact_memLp
      (hm hu b) hχ.continuous hc hs
  · intro i
    exact memLp_piLp_iff.mpr fun b => h1 i b
  · intro i b
    exact Poincare.Analysis.Elliptic.hasWeakPartialDeriv_cutoff i
      (hm hu b) (hm (hp i) b) (hw i b) hχ hc hs
  · intro i j
    exact memLp_piLp_iff.mpr fun b => (h2 i j b).add (h3 i j b)
  · intro i j b
    have hw1 := Poincare.Analysis.Elliptic.hasWeakPartialDeriv_cutoff j
      (hm (hp i) b) (hm (hH i j) b) (hwH i j b) hχ hc hs
    have hw2 := Poincare.Analysis.Elliptic.hasWeakPartialDeriv_cutoff j
      (hm hu b) (hm (hp j) b) (hw j b) (hd i) (hdc i) (hds i)
    exact weak_add
      (Poincare.Analysis.Elliptic.memLp_mul_of_compact_memLp (hm (hp i) b)
        hχ.continuous hc hs)
      (Poincare.Analysis.Elliptic.memLp_mul_of_compact_memLp (hm hu b)
        (hd i).continuous (hdc i) (hds i)) (h2 i j b) (h3 i j b) hw1 hw2



theorem suCutoffHessian_eq_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : Plane → ℝ) (u : Plane → E) (p : Fin 2 → Plane → E)
    (H : Fin 2 → Fin 2 → Plane → E) (i j : Fin 2) (x : Plane)
    (hx : x ∉ tsupport χ) : suCutoffHessian χ u p H i j x = 0 := by
  have hd (k : Fin 2) : (D[k] χ) x = 0 :=
    image_eq_zero_of_notMem_tsupport (f := D[k] χ) (fun h =>
      hx (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single k 1) h))
  have hdd : (D[j] (D[i] χ)) x = 0 :=
    image_eq_zero_of_notMem_tsupport (f := D[j] (D[i] χ)) (fun h =>
      hx ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)) h)))
  simp only [suCutoffHessian, image_eq_zero_of_notMem_tsupport hx, hd, hdd,
    zero_smul, add_zero]




theorem suCutoffHessian_eq_of_eq_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : Plane → ℝ) (u : Plane → E) (p : Fin 2 → Plane → E)
    (H : Fin 2 → Fin 2 → Plane → E) {S : Set Plane} (hS : IsOpen S)
    (hone : ∀ x ∈ S, χ x = 1) (i j : Fin 2) (x : Plane) (hx : x ∈ S) :
    suCutoffHessian χ u p H i j x = H i j x := by
  have hd (k : Fin 2) (y : Plane) (hy : y ∈ S) : (D[k] χ) y = 0 := by
    have he : χ =ᶠ[𝓝 y] fun _ => (1 : ℝ) :=
      eventuallyEq_of_mem (hS.mem_nhds hy) (fun z hz => hone z hz)
    dsimp only
    rw [he.fderiv_eq (𝕜 := ℝ)]
    simp
  have hdd : (D[j] (D[i] χ)) x = 0 := by
    have he : (D[i] χ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      eventuallyEq_of_mem (hS.mem_nhds hx) (hd i)
    dsimp only
    rw [he.fderiv_eq (𝕜 := ℝ)]
    simp
  simp only [suCutoffHessian, hone x hx, hd _ x hx, hdd, one_smul, zero_smul, add_zero]

end PoincareConjecture.M60

end
