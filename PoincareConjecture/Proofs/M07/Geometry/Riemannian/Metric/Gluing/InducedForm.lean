import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom

open scoped ContDiff Manifold Topology
open Bundle

noncomputable section

namespace Poincare.Gluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

def inducedForm (g : Bundle.ContMDiffRiemannianMetric J ∞ E' (TangentSpace J : N → Type _))
    (f : M → N) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let A : E →L[ℝ] E' := mfderiv I J f x
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := g.inner (f x)
  (B.bilinearComp A A : E →L[ℝ] E →L[ℝ] ℝ)

theorem inducedForm_contMDiffAt (g : Bundle.ContMDiffRiemannianMetric J ∞ E' (TangentSpace J : N → Type _)) {f : M → N} {x₀ : M}
    (hf : ContMDiffAt I J ∞ f x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, inducedForm g f x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace J) (f x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : f x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace J) (f x₀)
  set D : M → (E →L[ℝ] E') :=
    inTangentCoordinates I J id f (fun x => mfderiv I J f x) x₀ with hD
  have hDsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ D x₀ :=
    hf.mfderiv_const (by simp)
  set B : N → (E' →L[ℝ] E' →L[ℝ] ℝ) := fun y =>
    ContinuousLinearMap.inCoordinates E' (TangentSpace J) (E' →L[ℝ] ℝ)
      (fun y => TangentSpace J y →L[ℝ] ℝ) (f x₀) y (f x₀) y (g.inner y) with hB
  have hBsmooth : ContMDiffAt J 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ B (f x₀) :=
    ((contMDiffAt_hom_bundle _).mp g.contMDiff.contMDiffAt).2
  have hcomp : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ((D x).precomp ℝ).comp ((B (f x)).comp (D x))) x₀ := by
    have h1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E' →L[ℝ] ℝ) ∞
        (fun x => (B (f x)).comp (D x)) x₀ :=
      (hBsmooth.comp x₀ hf).clm_comp hDsmooth
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hDsmooth).clm_comp h1
  refine hcomp.congr_of_eventuallyEq ?_
  have hUs : {x | x ∈ sT.baseSet} ∈ 𝓝 x₀ := sT.open_baseSet.mem_nhds hx₀
  have hUt : {x | f x ∈ tT.baseSet} ∈ 𝓝 x₀ :=
    hf.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hUs, hUt] with x hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  have hRHS : (((ContinuousLinearMap.precomp ℝ (D x)).comp ((B (f x)).comp (D x))) a) b
      = B (f x) (D x a) (D x b) := rfl
  have hkey : ∀ u : E, tT.symm (f x) (D x u) = mfderiv I J f x (sT.symm x u) := by
    intro u
    have hDu : D x u = tT.continuousLinearEquivAt ℝ (f x) hfx
        (mfderiv I J f x ((sT.continuousLinearEquivAt ℝ x hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (f x) : E' → TangentSpace J (f x))
        = ⇑(tT.continuousLinearEquivAt ℝ (f x) hfx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hfx]
      funext y
      exact (tT.symmL_apply hfx y).symm
    have hcoeS : (sT.symm x : E → TangentSpace I x)
        = ⇑(sT.continuousLinearEquivAt ℝ x hx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq sT hx]
      funext y
      exact (sT.symmL_apply hx y).symm
    rw [hDu, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  rw [hRHS, hB]
  have htrivN : trivializationAt ℝ (Bundle.Trivial N ℝ) (f x₀) =
      Bundle.Trivial.trivialization N ℝ := Bundle.Trivial.eq_trivialization N ℝ _
  have htrivM : trivializationAt ℝ (Bundle.Trivial M ℝ) x₀ =
      Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization M ℝ _
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial N ℝ) hfx hfx (by simp)]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hx hx (by simp)]
  simp only [htrivN, htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe,
    id_eq, inducedForm, ← htT, ← hsT, hkey]
  rfl

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in

theorem mfderiv_localSection_rightInverse {q : M → N} {s : N → M} {y : N}
    (hs : MDifferentiableAt J I s y) (hq : MDifferentiableAt I J q (s y))
    (hsec : ∀ᶠ z in 𝓝 y, q (s z) = z) (u : TangentSpace J y) :
    mfderiv I J q (s y) (mfderiv J I s y u) = u := by
  have hEq : q ∘ s =ᶠ[𝓝 y] id := hsec
  have hd : mfderiv J J (q ∘ s) y = ContinuousLinearMap.id ℝ (TangentSpace J y) := by
    rw [hEq.mfderiv_eq, mfderiv_id]
  rw [mfderiv_comp y hq hs] at hd
  exact congrArg (fun L : TangentSpace J y →L[ℝ] TangentSpace J y => L u) hd

end Poincare.Gluing
