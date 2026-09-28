import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Descent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology Bundle PoincareConjecture
open scoped Manifold ContDiff

noncomputable section

namespace Poincare.Gluing

variable {n : ℕ}

theorem inducedForm_family_contMDiffWithinAt
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {g : ℝ → RiemannianMetric n N} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    {f : M → N} {x₀ : M} (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x₀)
    {t : ℝ} (ht : t ∈ J) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, inducedForm (I := 𝓡 n) (J := 𝓡 n) (g p.1) f p.2⟩ :
        Bundle.TotalSpace
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)))
      (J ×ˢ univ) (t, x₀) := by
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  let E := EuclideanSpace ℝ (Fin n)
  set sT := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x₀ with hsT
  set tT := trivializationAt E (TangentSpace (𝓡 n) : N → Type _) (f x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace (𝓡 n)) x₀
  have hfx₀ : f x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E (TangentSpace (𝓡 n)) (f x₀)
  set D : M → E →L[ℝ] E :=
    inTangentCoordinates (𝓡 n) (𝓡 n) id f
      (fun x => mfderiv (𝓡 n) (𝓡 n) f x) x₀ with hD
  have hDsmooth : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ D x₀ :=
    hf.mfderiv_const (by simp)
  have hDprod : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, E →L[ℝ] E) ∞ (fun p : ℝ × M => D p.2) (J ×ˢ univ) (t, x₀) :=
    (hDsmooth.comp (t, x₀) contMDiffAt_snd).contMDiffWithinAt
  set B : ℝ × N → E →L[ℝ] E →L[ℝ] ℝ := fun p =>
    ContinuousLinearMap.inCoordinates E (TangentSpace (𝓡 n)) (E →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      (f x₀) p.2 (f x₀) p.2 ((g p.1).inner p.2) with hB
  have hBsmooth : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B (J ×ˢ univ) (t, f x₀) :=
    ((contMDiffWithinAt_hom_bundle _).mp (hg (t, f x₀) ⟨ht, mem_univ _⟩)).2
  have hBprod : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : ℝ × M => B (p.1, f p.2)) (J ×ˢ univ) (t, x₀) := by
    have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × M => (p.1, f p.2)) (t, x₀) :=
      contMDiffAt_fst.prodMk (hf.comp (t, x₀) contMDiffAt_snd)
    have hmaps : MapsTo (fun p : ℝ × M => (p.1, f p.2))
        (J ×ˢ univ) (J ×ˢ univ) := fun _ hp => ⟨hp.1, mem_univ _⟩
    exact hBsmooth.comp (t, x₀) hmap.contMDiffWithinAt hmaps
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
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
      mfderiv (𝓡 n) (𝓡 n) f p.2 (sT.symm p.2 u) := by
    intro u
    have hDu : D p.2 u = tT.continuousLinearEquivAt ℝ (f p.2) hfx
        (mfderiv (𝓡 n) (𝓡 n) f p.2
          ((sT.continuousLinearEquivAt ℝ p.2 hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (f p.2) : E → TangentSpace (𝓡 n) (f p.2)) =
        ⇑(tT.continuousLinearEquivAt ℝ (f p.2) hfx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hfx]
      funext y
      exact (tT.symmL_apply hfx y).symm
    have hcoeS : (sT.symm p.2 : E → TangentSpace (𝓡 n) p.2) =
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
    LinearMap.id_coe, id_eq, inducedForm, ← htT, ← hsT, hkey]
  rfl

theorem isSmoothFamilyOn_of_local_diffeomorphisms
    {A : Type*} {P : A → Type*} {N : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace N]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ N]
    {J : Set ℝ} (g : ∀ i, ℝ → RiemannianMetric n (P i))
    (gN : ℝ → RiemannianMetric n N)
    (hg : ∀ i, RiemannianMetric.IsSmoothFamilyOn (g i) J)
    (q : ∀ i, P i → N)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hpres : ∀ t ∈ J, ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
      (g i t).inner x a b = (gN t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b)) :
    RiemannianMetric.IsSmoothFamilyOn gN J := by
  rintro ⟨t, y⟩ ⟨ht, _⟩
  obtain ⟨i, x, rfl⟩ := hcover y
  let s := (hq i x).localInverse
  have hs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ s (q i x) :=
    (hq i x).localInverse_contMDiffAt
  have hsec : ∀ᶠ z in 𝓝 (q i x), q i (s z) = z :=
    (hq i x).localInverse_eventuallyEq_right
  have hsmd : ∀ᶠ z in 𝓝 (q i x), MDifferentiableAt (𝓡 n) (𝓡 n) s z := by
    filter_upwards [s.open_source.mem_nhds (hq i x).localInverse_mem_source] with z hz
    exact s.mdifferentiableAt (by simp) hz
  have hlocal := inducedForm_family_contMDiffWithinAt (hg i) hs ht
  refine hlocal.congr_of_eventuallyEq_of_mem ?_ ⟨ht, mem_univ _⟩
  have hspatial : ∀ᶠ z in 𝓝 (q i x), ∀ τ ∈ J,
      (gN τ).inner z = inducedForm (I := 𝓡 n) (J := 𝓡 n) (g i τ) s z := by
    filter_upwards [hsec, hsmd, hsec.eventually_nhds] with z hz hmd hz2
    intro τ hτ
    ext a b
    have ha := mfderiv_localSection_rightInverse hmd
      ((hq i).mdifferentiable (by simp) _) hz2 a
    have hb := mfderiv_localSection_rightInverse hmd
      ((hq i).mdifferentiable (by simp) _) hz2 b
    have h := hpres τ hτ i (s z)
      (mfderiv (𝓡 n) (𝓡 n) s z a) (mfderiv (𝓡 n) (𝓡 n) s z b)
    rw [ha, hb, hz] at h
    exact h.symm
  filter_upwards [mem_nhdsWithin_of_mem_nhds (continuousAt_snd hspatial),
    self_mem_nhdsWithin] with p hp hpJ
  exact congrArg (fun B => Bundle.TotalSpace.mk' _ p.2 B) (hp p.1 hpJ.1)

end Poincare.Gluing
