import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Field
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.RadialFrame

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem curvature_transverse_eq (D : LeviCivitaData g) (x : M)
    (U T : TangentSpace (𝓡 2) x) (hUT : g.inner x U T = 0) :
    D.curvature x U T T =
      (D.scalarCurvature x / 2 * g.inner x T T) • U := by
  apply (g.inner_isInvertible x).injective
  apply ContinuousLinearMap.ext
  intro v
  change D.curvatureTensor x U T v T = _
  rw [D.curvatureTensor_eq_half_scalarCurvature, hUT]
  simp only [zero_mul, sub_zero, map_smul, smul_apply, smul_eq_mul]
  ring

open ConnectionAlongCurve ConnectionVariation ConjugateFrame

theorem jacobi_of_scalar_in_parallel_frame (D : LeviCivitaData g)
    {γ : ℝ → M} {P : ℝ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)}
    {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hi : ∀ s ∈ Icc a b, (P s).IsInvertible)
    (hγ : ∀ s ∈ Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ s)
    (hP : ∀ s ∈ Icc a b, ∀ u,
      ContDiffAt ℝ ∞ (chartField γ (γ s) (fun r => P r u)) s ∧
      manifoldCovDerivAlong g γ (fun r => P r u) 1 s = 0)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ ∞ φ (Ioo a b))
    (u : EuclideanSpace ℝ (Fin 2))
    (horth : g.inner (γ t) (P t u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = 0)
    (hode : deriv (deriv φ) t =
      -(D.scalarCurvature (γ t) / 2 *
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)) * φ t) :
    manifoldCovDerivAlong g γ
        (manifoldCovDerivAlong g γ (fun s => P s (φ s • u)) 1) 1 t =
      -D.curvature (γ t) (P t (φ t • u))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) := by
  let W := fun s => φ s • u
  let V := fun s => deriv φ s • u
  have hWs (s : ℝ) (hs : s ∈ Ioo a b) : ContDiffAt ℝ ∞ W s :=
    (hφ.contDiffAt (isOpen_Ioo.mem_nhds hs)).smul contDiffAt_const
  have hVs (s : ℝ) (hs : s ∈ Ioo a b) : ContDiffAt ℝ ∞ V s :=
    ((hφ.contDiffAt (isOpen_Ioo.mem_nhds hs)).fderiv_right (by simp)).clm_apply
      contDiffAt_const |>.smul contDiffAt_const
  have hd (s : ℝ) (hs : s ∈ Ioo a b) : deriv W s = V s := by
    exact (((hφ.contDiffAt (isOpen_Ioo.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt.smul_const u).deriv
  have hdV : deriv V t = deriv (deriv φ) t • u := by
    have hs : ContDiffAt ℝ ∞ (deriv φ) t :=
      ((hφ.contDiffAt (isOpen_Ioo.mem_nhds ht)).fderiv_right (by simp)).clm_apply contDiffAt_const
    exact (hs.differentiableAt (by simp)).hasDerivAt.smul_const u |>.deriv
  have heq : manifoldCovDerivAlong g γ (fun s => P s (φ s • u)) 1 =ᶠ[𝓝 t]
      (fun s => P s (V s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [covDeriv_frame_field hs hi (hγ s hs) (hP s (Ioo_subset_Icc_self hs)) (hWs s hs),
      hd s hs]
  rw [g.manifoldCovDerivAlong_congr_field γ heq,
    covDeriv_frame_field ht hi (hγ t ht) (hP t (Ioo_subset_Icc_self ht)) (hVs t ht),
    hdV, hode]
  have horth' : g.inner (γ t) (P t (φ t • u))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = 0 := by
    simp only [map_smul, smul_apply, smul_eq_mul, horth, mul_zero]
  rw [D.curvature_transverse_eq _ _ _ horth']
  simp only [map_smul, smul_smul, neg_mul, neg_smul, map_neg]

end PoincareConjecture.LeviCivitaData
