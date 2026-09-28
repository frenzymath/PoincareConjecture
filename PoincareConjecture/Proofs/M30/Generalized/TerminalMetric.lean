import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Proofs.M13.OrdinaryFlow











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

private theorem inner_mfderiv_of_slice_identity (F : GeneralizedRicciFlowData.{u})
    {s t : ℝ} (ht : t = s)
    (f : (F.slice s).carrier → (F.slice t).carrier) (x : (F.slice s).carrier)
    (hf : ∀ᶠ y in 𝓝 x, (⟨t, f y⟩ : F.point) = (⟨s, y⟩ : F.point))
    (v w : TangentSpace (𝓡 3) x) :
    (F.metric t).inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) = (F.metric s).inner x v w := by
  subst t
  have heq : f =ᶠ[𝓝 x] id := by
    filter_upwards [hf] with y hy
    exact eq_of_heq (Sigma.mk.inj_iff.mp hy).2
  rw [heq.mfderiv_eq, mfderiv_id]
  change (F.metric s).inner (f x) v w = (F.metric s).inner x v w
  exact congrArg (fun y => (F.metric s).inner y v w) heq.eq_of_nhds




theorem Cylinder.pullbackInner_zero_of_identity
    {F : GeneralizedRicciFlowData.{u}} {origin scale : ℝ} {I : Set ℝ}
    {U : Set (F.slice origin).carrier} (hU : IsOpen U)
    (e : GeneralizedFlowCylinder F (F.slice origin) origin scale I U)
    (h₀ : (0 : ℝ) ∈ I)
    (hzero : ∀ x ∈ U, e.pointMap 0 h₀ x = (⟨origin, x⟩ : F.point))
    (x : (F.slice origin).carrier) (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner 0 h₀ x v w = scale * (F.metric origin).inner x v w := by
  unfold GeneralizedFlowCylinder.pullbackInner
  congr 1
  apply inner_mfderiv_of_slice_identity F (by simp) (e.forward 0 h₀) x ?_ v w
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hzero y hy




theorem scaled_terminal_ball_eq_baseBall (S : GeneralizedBlowupSequence.{u})
    (k : ℕ) (R : ℝ) :
    RiemannianMetric.ball
      (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
        (S.scale k) (S.base_scalar_pos k))
      (S.base k).2 R = S.baseBall k R := by
  have h := M13.homothety_ball_image ((S.flow k).metric (S.base k).1)
    (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k))
    (Diffeomorph.refl (𝓡 3) ((S.flow k).slice (S.base k).1).carrier ∞)
    (S.scale k) (S.base_scalar_pos k)
    (M13.identity_metricHomothety ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k))
    (S.base k).2 (R / Real.sqrt (S.scale k))
  have hsqrt : Real.sqrt (S.scale k) ≠ 0 :=
    (Real.sqrt_pos.mpr (S.base_scalar_pos k)).ne'
  simpa only [GeneralizedBlowupSequence.baseBall, Diffeomorph.coe_refl, id_eq,
    image_id, mul_div_cancel₀ _ hsqrt]
    using h.symm

end PoincareConjecture.M30
