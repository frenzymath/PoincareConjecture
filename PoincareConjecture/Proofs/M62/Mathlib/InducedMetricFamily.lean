import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.InducedForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology Bundle
open scoped Manifold ContDiff

namespace Poincare.Gluing

theorem inducedForm_family_contMDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {g : ℝ → Bundle.ContMDiffRiemannianMetric J ∞ E'
      (TangentSpace J : N → Type _)} {S : Set ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod J)
      (J.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun z : ℝ × N => (⟨z.2, (g z.1).inner z.2⟩ :
        Bundle.TotalSpace (E' →L[ℝ] E' →L[ℝ] ℝ)
          (fun y : N => TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ)))
      (S ×ˢ univ))
    {f : M → N} (hf : ContMDiff I J ∞ f) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun z : ℝ × M => (⟨z.2, inducedForm
        (I := I) (J := J) (g z.1) f z.2⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (S ×ˢ univ) := by
  rintro ⟨t, x₀⟩ ⟨ht, _⟩
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  set sT := trivializationAt E (TangentSpace I : M → Type _) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace J : N → Type _) (f x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : f x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace J) (f x₀)
  set D : M → E →L[ℝ] E' :=
    inTangentCoordinates I J id f (fun x => mfderiv I J f x) x₀ with hD
  have hDsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ D x₀ :=
    (hf x₀).mfderiv_const (by simp)
  have hDprod : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, E →L[ℝ] E') ∞ (fun z : ℝ × M => D z.2) (S ×ˢ univ) (t, x₀) :=
    (hDsmooth.comp (t, x₀) contMDiffAt_snd).contMDiffWithinAt
  set B : ℝ × N → E' →L[ℝ] E' →L[ℝ] ℝ := fun z =>
    ContinuousLinearMap.inCoordinates E' (TangentSpace J) (E' →L[ℝ] ℝ)
      (fun y => TangentSpace J y →L[ℝ] ℝ)
      (f x₀) z.2 (f x₀) z.2 ((g z.1).inner z.2) with hB
  have hBsmooth : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod J)
      𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ B (S ×ˢ univ) (t, f x₀) :=
    ((contMDiffWithinAt_hom_bundle _).mp (hg (t, f x₀) ⟨ht, mem_univ _⟩)).2
  have hBprod : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞
      (fun z : ℝ × M => B (z.1, f z.2)) (S ×ˢ univ) (t, x₀) := by
    have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) ∞
        (fun z : ℝ × M => (z.1, f z.2)) (t, x₀) :=
      contMDiffAt_fst.prodMk ((hf x₀).comp (t, x₀) contMDiffAt_snd)
    have hmaps : MapsTo (fun z : ℝ × M => (z.1, f z.2))
        (S ×ˢ univ) (S ×ˢ univ) := fun _ hz => ⟨hz.1, mem_univ _⟩
    exact hBsmooth.comp (t, x₀) hmap.contMDiffWithinAt hmaps
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun z : ℝ × M => ((D z.2).precomp ℝ).comp
        ((B (z.1, f z.2)).comp (D z.2))) (S ×ˢ univ) (t, x₀) :=
    (ContMDiffWithinAt.clm_precomp (F₃ := ℝ) hDprod).clm_comp
      (hBprod.clm_comp hDprod)
  refine hcomp.congr_of_eventuallyEq_of_mem ?_ ⟨ht, mem_univ _⟩
  have hUs : {z : ℝ × M | z.2 ∈ sT.baseSet} ∈ 𝓝 (t, x₀) :=
    continuousAt_snd (sT.open_baseSet.mem_nhds hx₀)
  have hUt : {z : ℝ × M | f z.2 ∈ tT.baseSet} ∈ 𝓝 (t, x₀) :=
    ((hf x₀).continuousAt.comp continuousAt_snd) (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hUs, mem_nhdsWithin_of_mem_nhds hUt]
    with z hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  have hRHS : (((D z.2).precomp ℝ).comp ((B (z.1, f z.2)).comp (D z.2))) a b =
      B (z.1, f z.2) (D z.2 a) (D z.2 b) := rfl
  have hkey : ∀ u : E, tT.symm (f z.2) (D z.2 u) =
      mfderiv I J f z.2 (sT.symm z.2 u) := by
    intro u
    have hDu : D z.2 u = tT.continuousLinearEquivAt ℝ (f z.2) hfx
        (mfderiv I J f z.2 ((sT.continuousLinearEquivAt ℝ z.2 hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (f z.2) : E' → TangentSpace J (f z.2)) =
        ⇑(tT.continuousLinearEquivAt ℝ (f z.2) hfx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hfx]
      funext y
      exact (tT.symmL_apply hfx y).symm
    have hcoeS : (sT.symm z.2 : E → TangentSpace I z.2) =
        ⇑(sT.continuousLinearEquivAt ℝ z.2 hx).symm := by
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
  simp only [htrivN, htrivM, Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, inducedForm, ← htT, ← hsT, hkey]
  rfl

end Poincare.Gluing
