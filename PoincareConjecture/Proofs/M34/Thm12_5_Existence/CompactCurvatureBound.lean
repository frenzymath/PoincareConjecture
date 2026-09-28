import PoincareConjecture.Proofs.M34.Mathlib.CompactEnergyComparison
import PoincareConjecture.Proofs.M04.CurvatureEnergyHeat
import PoincareConjecture.Proofs.M04.ShiCutoffMaximum
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem continuousOn_flow_curvatureTensorNorm (F : RicciFlow n M J) :
    ContinuousOn (fun p : ℝ × M => (F.connection p.1).curvatureTensorNorm p.2)
      (J ×ˢ univ) := by
  have h := (M04.contMDiffOn_flow_curvatureDerivativeEnergy F 0).continuousOn.sqrt
  apply h.congr
  intro p _hp
  dsimp only
  rw [LeviCivitaData.curvatureDerivativeNorm_zero]
  exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm

theorem hasDerivWithinAt_flow_curvatureEnergy (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ J) (x : M) :
    HasDerivWithinAt (fun s => (F.connection s).curvatureTensorNorm x ^ 2)
      (derivWithin (fun s => (F.connection s).curvatureTensorNorm x ^ 2) J t) J t := by
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun s : ℝ => (s, x)) := contMDiff_id.prodMk contMDiff_const
  have h := (M04.contMDiffOn_flow_curvatureDerivativeEnergy F 0).comp
    hslice.contMDiffOn (fun _ hs => ⟨hs, mem_univ x⟩)
  have hdiff := h.contDiffOn.differentiableOn (by simp) t ht
  simpa only [Function.comp_def, LeviCivitaData.curvatureDerivativeNorm_zero]
    using hdiff.hasDerivWithinAt

theorem curvatureEnergy_velocity_le_at_maximum (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ J) (x : M)
    (hmax : ∀ y : M, (F.connection t).curvatureTensorNorm y ^ 2 ≤
      (F.connection t).curvatureTensorNorm x ^ 2) :
    derivWithin (fun s => (F.connection s).curvatureTensorNorm x ^ 2) J t ≤
      16 * (n : ℝ) ^ 6 * (F.connection t).curvatureTensorNorm x ^ 3 := by
  have hslice : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun y : M => (t, y)) := contMDiff_const.prodMk contMDiff_id
  have h := (M04.contMDiffOn_flow_curvatureDerivativeEnergy F 0).comp
    hslice.contMDiffOn (s := univ) (fun y _ => ⟨ht, mem_univ y⟩)
  have hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (F.connection t).curvatureTensorNorm y ^ 2) := by
    simpa only [Function.comp_def, LeviCivitaData.curvatureDerivativeNorm_zero,
      contMDiffOn_univ] using h
  have hlap := M04.laplacian_nonpos_of_isLocalMax (F.connection t)
    (hsmooth x) (Filter.Eventually.of_forall hmax)
  have hheat := M04.curvatureEnergy_heat_inequality F ht x
  nlinarith [sq_nonneg ((F.connection t).curvatureDerivativeNorm 1 x)]

theorem compact_curvatureTensorNorm_le_quadraticGrowthBarrier [CompactSpace M]
    {T B : ℝ} (F : RicciFlow n M (Icc 0 T)) (hT : 0 < T) (hB : 0 < B)
    (hden : 16 * (n : ℝ) ^ 6 * B * T < 1)
    (hinit : ∀ x : M, (F.connection 0).curvatureTensorNorm x ≤ B) :
    ∀ t ∈ Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤
      Real.quadraticGrowthBarrier (16 * (n : ℝ) ^ 6) B t := by
  apply compact_nonnegative_norm_le_quadraticGrowthBarrier hT hB
    (by positivity) hden
    (fun t x => (F.connection t).curvatureTensorNorm x)
    (fun t x => derivWithin
      (fun s => (F.connection s).curvatureTensorNorm x ^ 2) (Icc 0 T) t)
    (continuousOn_flow_curvatureTensorNorm F)
    (fun _ _ _ => Real.sqrt_nonneg _) (fun _ ht x =>
      hasDerivWithinAt_flow_curvatureEnergy F ht x) _ hinit
  intro t ht x hmax
  exact curvatureEnergy_velocity_le_at_maximum F ⟨ht.1.le, ht.2⟩ x hmax

theorem compact_curvatureTensorNorm_le_twice [CompactSpace M]
    {T B : ℝ} (F : RicciFlow n M (Ico 0 T)) (hB : 0 < B)
    (hinit : ∀ x : M, (F.connection 0).curvatureTensorNorm x ≤ B)
    {t : ℝ} (ht : t ∈ Ico 0 T) (hsmall : 16 * (n : ℝ) ^ 6 * B * t ≤ 1 / 2) :
    ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ 2 * B := by
  by_cases ht0 : t = 0
  · subst t
    exact fun x => (hinit x).trans (by linarith)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hsub : Icc 0 t ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hne : (Icc 0 t).Nontrivial :=
    ⟨0, ⟨le_rfl, htpos.le⟩, t, ⟨htpos.le, le_rfl⟩, ne_of_lt htpos⟩
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub ordConnected_Icc hne
  have hbound := compact_curvatureTensorNorm_le_quadraticGrowthBarrier G htpos hB
    (by linarith) hinit t ⟨htpos.le, le_rfl⟩
  exact fun x => (hbound x).trans (Real.quadraticGrowthBarrier_le_twice hB.le hsmall)

end PoincareConjecture.M34
