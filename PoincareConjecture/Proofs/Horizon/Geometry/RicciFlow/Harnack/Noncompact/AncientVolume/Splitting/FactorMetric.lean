import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.Descent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology Bundle
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

private theorem pullbackForm_family_contMDiffWithinAt
    {m n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 m) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {g : ℝ → RiemannianMetric n N} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J)
    {f : M → N} {x₀ : M} (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f x₀)
    {t : ℝ} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 m))
      ((𝓡 m).prod 𝓘(ℝ,
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, Induced.pullbackForm (g p.1) f p.2⟩ :
        Bundle.TotalSpace
          (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 m) x →L[ℝ] TangentSpace (𝓡 m) x →L[ℝ] ℝ)))
      (J ×ˢ univ) (t, x₀) := by
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  let E := EuclideanSpace ℝ (Fin m)
  let E' := EuclideanSpace ℝ (Fin n)
  set sT := trivializationAt E (TangentSpace (𝓡 m) : M → Type _) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace (𝓡 n) : N → Type _) (f x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace (𝓡 m)) x₀
  have hfx₀ : f x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace (𝓡 n)) (f x₀)
  set D : M → E →L[ℝ] E' :=
    inTangentCoordinates (𝓡 m) (𝓡 n) id f
      (fun x => mfderiv (𝓡 m) (𝓡 n) f x) x₀ with hD
  have hDsmooth : ContMDiffAt (𝓡 m) 𝓘(ℝ, E →L[ℝ] E') ∞ D x₀ :=
    hf.mfderiv_const (by simp)
  have hDprod : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 m))
      𝓘(ℝ, E →L[ℝ] E') ∞ (fun p : ℝ × M => D p.2) (J ×ˢ univ) (t, x₀) :=
    (hDsmooth.comp (t, x₀) contMDiffAt_snd).contMDiffWithinAt
  set B : ℝ × N → E' →L[ℝ] E' →L[ℝ] ℝ := fun p =>
    ContinuousLinearMap.inCoordinates E' (TangentSpace (𝓡 n)) (E' →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      (f x₀) p.2 (f x₀) p.2 ((g p.1).inner p.2) with hB
  have hBsmooth : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ B (J ×ˢ univ) (t, f x₀) :=
    ((contMDiffWithinAt_hom_bundle _).mp (hg (t, f x₀) ⟨ht, mem_univ _⟩)).2
  have hBprod : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 m))
      𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞
      (fun p : ℝ × M => B (p.1, f p.2)) (J ×ˢ univ) (t, x₀) := by
    have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 m))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × M => (p.1, f p.2)) (t, x₀) :=
      contMDiffAt_fst.prodMk (hf.comp (t, x₀) contMDiffAt_snd)
    have hmaps : MapsTo (fun p : ℝ × M => (p.1, f p.2))
        (J ×ˢ univ) (J ×ˢ univ) := fun _ hp => ⟨hp.1, mem_univ _⟩
    exact hBsmooth.comp (t, x₀) hmap.contMDiffWithinAt hmaps
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 m))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : ℝ × M => ((D p.2).precomp ℝ).comp
        ((B (p.1, f p.2)).comp (D p.2))) (J ×ˢ univ) (t, x₀) :=
    (ContMDiffWithinAt.clm_precomp (F₃ := ℝ) hDprod).clm_comp
      (hBprod.clm_comp hDprod)
  refine hcomp.congr_of_eventuallyEq_of_mem ?_ ⟨ht, mem_univ _⟩
  have hUs : {p : ℝ × M | p.2 ∈ sT.baseSet} ∈ 𝓝 (t, x₀) :=
    continuousAt_snd (sT.open_baseSet.mem_nhds hx₀)
  have hUt : {p : ℝ × M | f p.2 ∈ tT.baseSet} ∈ 𝓝 (t, x₀) :=
    (hf.continuousAt.comp continuousAt_snd) (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hUs, mem_nhdsWithin_of_mem_nhds hUt]
    with p hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  have hRHS : (((D p.2).precomp ℝ).comp ((B (p.1, f p.2)).comp (D p.2))) a b =
      B (p.1, f p.2) (D p.2 a) (D p.2 b) := rfl
  have hkey : ∀ u : E, tT.symm (f p.2) (D p.2 u) =
      mfderiv (𝓡 m) (𝓡 n) f p.2 (sT.symm p.2 u) := by
    intro u
    have hDu : D p.2 u = tT.continuousLinearEquivAt ℝ (f p.2) hfx
        (mfderiv (𝓡 m) (𝓡 n) f p.2
          ((sT.continuousLinearEquivAt ℝ p.2 hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (f p.2) : E' → TangentSpace (𝓡 n) (f p.2)) =
        ⇑(tT.continuousLinearEquivAt ℝ (f p.2) hfx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hfx]
      funext y
      exact (tT.symmL_apply hfx y).symm
    have hcoeS : (sT.symm p.2 : E → TangentSpace (𝓡 m) p.2) =
        ⇑(sT.continuousLinearEquivAt ℝ p.2 hx).symm := by
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
    LinearMap.id_coe, id_eq, Induced.pullbackForm, Induced.pullbackFormOf,
    ← htT, ← hsT, hkey]
  rfl



theorem IsSmoothFamilyOn.pullbackImmersion
    {m n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 m) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {g : ℝ → RiemannianMetric n N} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J) (f : M → N)
    (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 m) (𝓡 n) f x)) :
    IsSmoothFamilyOn (fun t => Induced.pullbackMetric (g t) f hf himm) J := by
  rintro ⟨t, x⟩ ⟨ht, _⟩
  exact pullbackForm_family_contMDiffWithinAt hg (hf x) ht

open Poincare.Geometry.Manifold.RegularLevel



theorem IsSmoothFamilyOn.regularLevelMetric
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    {g : ℝ → RiemannianMetric (n + 1) M} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) (c : ℝ) :
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    let := openLevelSetChartedSpace hf U hreg n c
    let := isManifold_openLevelSet hf U hreg n c
    IsSmoothFamilyOn (fun t => regularLevelMetric hf U hreg c (g t)) J := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  exact hg.pullbackImmersion (openLevelIncl f U c)
    (contMDiff_openLevelIncl hf U hreg n c)
    (injective_mfderiv_openLevelIncl hf U hreg n c)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow

open Poincare.Geometry.Manifold.RegularLevel


theorem regularLevelMetric_equation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M] {J : Set ℝ}
    (F : RicciFlow (n + 1) M J)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) (c : ℝ) :
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    let := openLevelSetChartedSpace hf U hreg n c
    let := isManifold_openLevelSet hf U hreg n c
    ∀ t ∈ J, ∀ x : openLevelSet f U c, ∀ v w : TangentSpace (𝓡 n) x,
      HasDerivWithinAt
        (fun s => (RiemannianMetric.regularLevelMetric hf U hreg c (F.metric s)).inner x v w)
        (-2 * (F.connection t).ricci (openLevelIncl f U c x)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) x v)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) x w)) J t := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  dsimp only
  intro t ht x v w
  exact F.equation t ht (openLevelIncl f U c x) _ _

end PoincareConjecture.RicciFlow
