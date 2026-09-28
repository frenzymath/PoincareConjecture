import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.Descent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem movingPullback_contMDiffAt
    (g : RiemannianMetric n M) {F : ℝ → M → M} {t : ℝ} {x : M}
    (hF : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => F p.1 p.2) (t, x)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace (𝓡 n) y →L[ℝ]
          TangentSpace (𝓡 n) y →L[ℝ] ℝ)
        p.2 (Poincare.Gluing.inducedForm g (F p.1) p.2)) (t, x) := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  let E := EuclideanSpace ℝ (Fin n)
  let sT := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let tT := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) (F t x)
  have hx : x ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace (𝓡 n)) x
  have hFx : F t x ∈ tT.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace (𝓡 n)) (F t x)
  let D : ℝ × M → E →L[ℝ] E :=
    inTangentCoordinates (𝓡 n) (𝓡 n) Prod.snd (fun p => F p.1 p.2)
      (fun p => mfderiv (𝓡 n) (𝓡 n) (F p.1) p.2) (t, x)
  have hDsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, E →L[ℝ] E) ∞ D (t, x) := by
    have hh : ContMDiffAt ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod (𝓡 n)) (𝓡 n) ∞
        (fun p : (ℝ × M) × M => F p.1.1 p.2) ((t, x), x) :=
      hF.comp ((t, x), x)
        ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
    exact hh.mfderiv (fun p : ℝ × M => F p.1) Prod.snd contMDiffAt_snd (by simp)
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun y =>
    ContinuousLinearMap.inCoordinates E (TangentSpace (𝓡 n)) (E →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      (F t x) y (F t x) y (g.inner y)
  have hBsmooth : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B (F t x) :=
    ((contMDiffAt_hom_bundle _).mp (g.contMDiff (F t x))).2
  have hcomp := (ContMDiffAt.clm_precomp (F₃ := ℝ) hDsmooth).clm_comp
    ((hBsmooth.comp (t, x) hF).clm_comp hDsmooth)
  apply hcomp.congr_of_eventuallyEq
  have hUs : ∀ᶠ p : ℝ × M in 𝓝 (t, x), p.2 ∈ sT.baseSet :=
    continuousAt_snd (sT.open_baseSet.mem_nhds hx)
  have hUt : ∀ᶠ p : ℝ × M in 𝓝 (t, x), F p.1 p.2 ∈ tT.baseSet :=
    hF.continuousAt (tT.open_baseSet.mem_nhds hFx)
  filter_upwards [hUs, hUt] with p hp hFp
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  have hkey (u : E) : tT.symm (F p.1 p.2) (D p u) =
      mfderiv (𝓡 n) (𝓡 n) (F p.1) p.2 (sT.symm p.2 u) := by
    have hDu : D p u = tT.continuousLinearEquivAt ℝ (F p.1 p.2) hFp
        (mfderiv (𝓡 n) (𝓡 n) (F p.1) p.2
          ((sT.continuousLinearEquivAt ℝ p.2 hp).symm u)) := by
      dsimp only [D, inTangentCoordinates]
      rw [ContinuousLinearMap.inCoordinates_eq hp hFp]
      rfl
    have hcoeT : (tT.symm (F p.1 p.2) : E → TangentSpace (𝓡 n) (F p.1 p.2)) =
        ⇑(tT.continuousLinearEquivAt ℝ (F p.1 p.2) hFp).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hFp]
      funext y
      exact (tT.symmL_apply hFp y).symm
    have hcoeS : (sT.symm p.2 : E → TangentSpace (𝓡 n) p.2) =
        ⇑(sT.continuousLinearEquivAt ℝ p.2 hp).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq sT hp]
      funext y
      exact (sT.symmL_apply hp y).symm
    rw [hDu, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  symm
  change B (F p.1 p.2) (D p a) (D p b) = _
  dsimp only [B]
  have htriv : trivializationAt ℝ (Bundle.Trivial M ℝ) (F t x) =
      Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization M ℝ _
  have htriv' : trivializationAt ℝ (Bundle.Trivial M ℝ) x =
      Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization M ℝ _
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hFp hFp (by simp)]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hp hp (by simp)]
  simp only [htriv, htriv', Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, Poincare.Gluing.inducedForm]
  change g.inner (F p.1 p.2) (tT.symm (F p.1 p.2) (D p a))
    (tT.symm (F p.1 p.2) (D p b)) = g.inner (F p.1 p.2)
      (mfderiv (𝓡 n) (𝓡 n) (F p.1) p.2 (sT.symm p.2 a))
      (mfderiv (𝓡 n) (𝓡 n) (F p.1) p.2 (sT.symm p.2 b))
  rw [hkey, hkey]



theorem movingPullback_smul_contMDiffAt
    (g : RiemannianMetric n M) {F : ℝ → M → M} {a : ℝ × M → ℝ}
    {t : ℝ} {x : M}
    (hF : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => F p.1 p.2) (t, x))
    (ha : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ a (t, x)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace (𝓡 n) y →L[ℝ]
          TangentSpace (𝓡 n) y →L[ℝ] ℝ)
        p.2 (a p • Poincare.Gluing.inducedForm g (F p.1) p.2)) (t, x) := by
  have hs := movingPullback_contMDiffAt g hF
  rw [Bundle.contMDiffAt_totalSpace] at hs ⊢
  refine ⟨hs.1, ?_⟩
  let E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ
  let : NormedAddCommGroup E := inferInstanceAs
    (NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
  let : NormedSpace ℝ E := inferInstanceAs
    (NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
  let V := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y →L[ℝ] ℝ
  let (y : M) : ContinuousAdd (TangentSpace (𝓡 n) y →L[ℝ] ℝ) :=
    inferInstanceAs (ContinuousAdd (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
  let : VectorBundle ℝ E V := inferInstanceAs
    (VectorBundle ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y →L[ℝ] ℝ))
  let e := trivializationAt E V x
  let : e.IsLinear ℝ := trivialization_linear ℝ (F := E) (E := V) e
  have he : ∀ᶠ p : ℝ × M in 𝓝 (t, x), p.2 ∈ e.baseSet :=
    continuousAt_snd (e.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E V x))
  apply (ha.smul hs.2).congr_of_eventuallyEq
  filter_upwards [he] with p hp
  exact (e.linear ℝ hp).map_smul (a p) (Poincare.Gluing.inducedForm g (F p.1) p.2)

end PoincareConjecture.RiemannianMetric
