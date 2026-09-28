import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.RadialSystem
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.AbsoluteDeterminant
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Center



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]



theorem deriv2_polarDensityRoot_le_of_ricci
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ U)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1)
    {b t κ : ℝ} (hb : 0 < b) (hsub : ∀ s ∈ Icc 0 b, s • θ ∈ U)
    (ht : t ∈ Ioo 0 b)
    (hi : Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • θ)))
    (hRic : ∀ v : TangentSpace (𝓡 (m + 1)) (e (t • θ)),
      -(m : ℝ) * κ * g.inner (e (t • θ)) v v ≤ D.ricci (e (t • θ)) v v) :
    deriv (deriv (fun s : ℝ =>
      s * g.pullbackVolumeDensity e (s • θ) ^ (1 / (m : ℝ)))) t ≤
      κ * (t * g.pullbackVolumeDensity e (t • θ) ^ (1 / (m : ℝ))) := by
  obtain ⟨basis, hθbasis⟩ := exists_orthonormalBasis_radial θ hθ
  subst θ
  obtain ⟨P, hP0, hPi, hpair, hrad, hJ0, hJ, hV⟩ :=
    g.exists_radial_parallel_jacobi D hU h0 he hgeo hmetric (basis 0) hb hsub
  let J : ℝ → EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    fun s => (P s).inverse.comp (s • mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • basis 0))
  let K : ℝ → EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    fun s => (P s).inverse.comp
      ((g.radialCurvatureOperator (e (s • basis 0)) (P s (basis 0))).comp (P s))
  have hK (s : ℝ) (hs : s ∈ Icc 0 b) : LinearMap.IsSymmetric (K s).toLinearMap := by
    intro u v
    change inner ℝ ((P s).inverse (g.radialCurvatureOperator (e (s • basis 0))
      (P s (basis 0)) (P s u))) v =
        inner ℝ u ((P s).inverse (g.radialCurvatureOperator (e (s • basis 0))
          (P s (basis 0)) (P s v)))
    rw [← hpair s hs, ← hpair s hs, (hPi s hs).self_apply_inverse,
      (hPi s hs).self_apply_inverse, g.radialCurvatureOperator_apply D,
      g.radialCurvatureOperator_apply D]
    exact D.inner_radial_curvature_symm _ _ _ _
  have hKr (s : ℝ) (_hs : s ∈ Icc 0 b) : K s (basis 0) = 0 := by
    change (P s).inverse (g.radialCurvatureOperator (e (s • basis 0))
      (P s (basis 0)) (P s (basis 0))) = 0
    rw [g.radialCurvatureOperator_self D, map_zero]
  have hdet (s : ℝ) (hs : s ∈ Icc 0 b) (hs0 : 0 < s) :
      |((LinearMap.toMatrix basis.toBasis basis.toBasis (J s).toLinearMap).submatrix
        Fin.succ Fin.succ).det| = s ^ m * g.pullbackVolumeDensity e (s • basis 0) :=
    g.abs_det_transverse_radialDifferential_of_isInvertible e basis hs0
      (P s) (hPi s hs) (hpair s hs) (hrad s hs).symm
  have ht' : t ∈ Icc 0 b := ⟨ht.1.le, ht.2.le⟩
  have hρ := (g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (hU.mem_nhds (hsub t ht'))) hi).2
  have hne : ((LinearMap.toMatrix basis.toBasis basis.toBasis (J t).toLinearMap).submatrix
      Fin.succ Fin.succ).det ≠ 0 := by
    apply abs_pos.mp
    rw [hdet t ht' ht.1]
    exact mul_pos (pow_pos ht.1 _) hρ
  have htrace : -(m : ℝ) * κ ≤
      ((LinearMap.toMatrix basis.toBasis basis.toBasis (K t).toLinearMap).submatrix
        Fin.succ Fin.succ).trace := by
    have htr : ((LinearMap.toMatrix basis.toBasis basis.toBasis
        (K t).toLinearMap).submatrix Fin.succ Fin.succ).trace =
        D.ricci (e (t • basis 0)) (P t (basis 0)) (P t (basis 0)) :=
      g.trace_transverse_frame_radialCurvatureOperator_of_isInvertible
        D (e (t • basis 0)) basis (P t) (hPi t ht') (hpair t ht')
    rw [htr]
    have h := hRic (P t (basis 0))
    rw [hpair t ht', basis.inner_eq_ite, if_pos rfl, mul_one] at h
    exact h
  have hcomp := deriv2_abs_transverse_determinantRoot_le_of_jacobi basis
    (J := J) (V := deriv J) (K := K) hm
    (fun s hs => ((hJ s hs).differentiableAt (by simp)).hasDerivAt)
    hV hK hKr hJ0 ht hne htrace
  have heq : (fun s =>
      |((LinearMap.toMatrix basis.toBasis basis.toBasis (J s).toLinearMap).submatrix
        Fin.succ Fin.succ).det| ^ (1 / (m : ℝ))) =ᶠ[𝓝 t]
      (fun s => s * g.pullbackVolumeDensity e (s • basis 0) ^ (1 / (m : ℝ))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hρ0 : 0 ≤ g.pullbackVolumeDensity e (s • basis 0) := Real.sqrt_nonneg _
    rw [hdet s ⟨hs.1.le, hs.2.le⟩ hs.1,
      Real.mul_rpow (pow_nonneg hs.1.le _) hρ0, one_div,
      Real.pow_rpow_inv_natCast hs.1.le hm.ne']
  rw [heq.deriv.deriv_eq] at hcomp
  have hval : |((LinearMap.toMatrix basis.toBasis basis.toBasis
      (J t).toLinearMap).submatrix Fin.succ Fin.succ).det| ^ (1 / (m : ℝ)) =
      t * g.pullbackVolumeDensity e (t • basis 0) ^ (1 / (m : ℝ)) := heq.self_of_nhds
  exact hcomp.trans_eq (congrArg (κ * ·) hval)

end PoincareConjecture.RiemannianMetric
