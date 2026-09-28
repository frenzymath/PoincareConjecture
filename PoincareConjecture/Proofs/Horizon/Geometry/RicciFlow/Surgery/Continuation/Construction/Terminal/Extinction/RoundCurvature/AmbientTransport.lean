import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.Model
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.Definitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}

theorem sectionalCurvature_pos_of_local_similarity
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {f : N → M} {U : Set N} {c : ℝ} (hc : 0 < c)
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 3) y,
      h.inner y u v = c * g.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y u) (mfderiv (𝓡 3) (𝓡 3) f y v))
    {x : N} (hx : x ∈ U)
    (hpos : ∀ u v : TangentSpace (𝓡 3) x,
      LinearIndependent ℝ ![u, v] → 0 < Dh.curvatureTensor x u v u v)
    (v w : TangentSpace (𝓡 3) (f x))
    (hpair : IsOrthonormalPair g (f x) v w) :
    0 < D.sectionalCurvature (f x) v w := by
  let G := rescaledMetric g c hc
  let DG := rescaledMetric_connection g D c hc
  have hlocal : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 3) y,
      h.inner y u v = G.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y u) (mfderiv (𝓡 3) (𝓡 3) f y v) := hmetric
  have hsurj := (h.mfderiv_bijective_of_pullback_eq G x
    (fun a b => (hlocal x hx a b).symm)).2
  obtain ⟨u, rfl⟩ := hsurj v
  obtain ⟨z, rfl⟩ := hsurj w
  have hlin : LinearIndependent ℝ ![u, z] := by
    apply LinearIndependent.of_comp (mfderiv (𝓡 3) (𝓡 3) f x).toLinearMap
    apply linearIndependent_fin2.mpr
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      ContinuousLinearMap.coe_coe]
    constructor
    · intro hz
      have hbad := hpair.2.1
      simp only [hz, map_zero] at hbad
      exact zero_ne_one hbad
    · intro a ha
      have hzero := congrArg (fun q => g.inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x u) q) ha
      simp only [map_smul, smul_eq_mul, hpair.2.2, hpair.1, mul_zero] at hzero
      norm_num at hzero
  have hp := hpos u z hlin
  rw [Dh.curvatureTensor_eq_of_local_isometry DG hU hf hlocal hx] at hp
  change 0 < (rescaledMetric_connection g D c hc).curvatureTensor (f x)
    (mfderiv (𝓡 3) (𝓡 3) f x u) (mfderiv (𝓡 3) (𝓡 3) f x z)
    (mfderiv (𝓡 3) (𝓡 3) f x u) (mfderiv (𝓡 3) (𝓡 3) f x z) at hp
  rw [rescaledMetric_curvatureTensor] at hp
  have hK := (mul_pos_iff_of_pos_left hc).mp hp
  simpa only [sectionalCurvature, hpair.1, hpair.2.1, hpair.2.2,
    one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one] using hK

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.SingularRoundComponent

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)

theorem sectionalCurvature_pos_of_coordinate_realization
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) N.model.carrier)
    {h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))} (Dh : LeviCivitaData h)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ U)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U)
    (hh : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 3) y,
      h.inner y u v = N.normalizedMetric.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y u) (mfderiv (𝓡 3) (𝓡 3) e y v))
    (hpos : ∀ u v : TangentSpace (𝓡 3) (0 : EuclideanSpace ℝ (Fin 3)),
      LinearIndependent ℝ ![u, v] → 0 < Dh.curvatureTensor 0 u v u v)
    (v w : TangentSpace (𝓡 3) (N.forward (e 0)))
    (hpair : LeviCivitaData.IsOrthonormalPair g (N.forward (e 0)) v w) :
    0 < D.sectionalCurvature (N.forward (e 0)) v w := by
  apply D.sectionalCurvature_pos_of_local_similarity Dh N.scale_pos hU
    (N.forward_smooth.comp_contMDiffOn he) (f := N.forward ∘ e) ?_ h0 hpos v w hpair
  intro y hy u v
  rw [hh y hy, N.normalizedMetric_inner]
  rw [mfderiv_comp y (N.forward_smooth.mdifferentiable (by simp) (e y))
    (((he y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))]
  rfl

end PoincareConjecture.SingularRoundComponent
