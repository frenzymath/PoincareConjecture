import PoincareConjecture.Definitions.M27ProductModels
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "Ip" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


theorem twistedProductInvolution_mfderiv_snd
    (hs : ContMDiff Ip Ip ∞ m27TwistedProductInvolution)
    (p : UnitTwoSphere × ℝ) (v : TangentSpace Ip p) :
    (mfderiv Ip Ip m27TwistedProductInvolution p v).2 = -v.2 := by
  have hc := mfderiv_comp_apply p
    (mdifferentiableAt_snd (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)))
    (hs.mdifferentiable (by simp) p) v
  have he : Prod.snd ∘ m27TwistedProductInvolution =
      fun p : UnitTwoSphere × ℝ => -p.2 := rfl
  change @Eq ℝ _ _ at hc
  rw [he] at hc
  change (mfderiv Ip 𝓘(ℝ, ℝ) (-Prod.snd) p v : ℝ) =
    mfderiv Ip 𝓘(ℝ, ℝ) Prod.snd (m27TwistedProductInvolution p)
      (mfderiv Ip Ip m27TwistedProductInvolution p v) at hc
  rw [mfderiv_neg, mfderiv_snd, mfderiv_snd] at hc
  exact hc.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}


theorem twisted_cover_comp_involution (N : M27TwistedSphereLineFlowCertificate K) :
    N.cover ∘ m27TwistedProductInvolution = N.cover := by
  funext p
  exact ((N.cover_fibers p (m27TwistedProductInvolution p)).mpr (Or.inr rfl)).symm



theorem twisted_cover_field_equivariant
    (N : M27TwistedSphereLineFlowCertificate K)
    (Z : (x : M) → TangentSpace (𝓡 3) x) (p : UnitTwoSphere × ℝ) :
    let Y := mpullback Ip (𝓡 3) N.cover Z
    mfderiv Ip Ip m27TwistedProductInvolution p (Y p) =
      Y (m27TwistedProductInvolution p) := by
  let Y := mpullback Ip (𝓡 3) N.cover Z
  let tau := m27TwistedProductInvolution
  have hi (q : UnitTwoSphere × ℝ) : (mfderiv Ip (𝓡 3) N.cover q).IsInvertible :=
    ⟨N.cover_local_diffeomorph.mfderivToContinuousLinearEquiv (by simp) q, rfl⟩
  have hd := congrArg (fun f : UnitTwoSphere × ℝ → M =>
    (mfderiv Ip (𝓡 3) f p (Y p) : V))
    (twisted_cover_comp_involution N)
  have hcomp := mfderiv_comp_apply p
    (N.cover_local_diffeomorph.contMDiff.mdifferentiable (by simp) (tau p))
    (N.involution_smooth.mdifferentiable (by simp) p) (Y p)
  change @Eq V _ _ at hcomp
  have hpoint := congrFun (twisted_cover_comp_involution N) p
  change N.cover (tau p) = N.cover p at hpoint
  have hz : (Z (N.cover (tau p)) : V) = Z (N.cover p) :=
    congrArg (fun x => (Z x : V)) hpoint
  apply (hi (tau p)).injective
  change @Eq V ((mfderiv Ip (𝓡 3) N.cover (tau p))
      (mfderiv Ip Ip tau p (Y p)))
    ((mfderiv Ip (𝓡 3) N.cover (tau p)) (Y (tau p)))
  exact (hcomp.symm.trans hd).trans
    (((hi p).self_apply_inverse _).trans
      (hz.symm.trans ((hi (tau p)).self_apply_inverse _).symm))



theorem twisted_cover_field_axial_odd
    (N : M27TwistedSphereLineFlowCertificate K)
    (Z : (x : M) → TangentSpace (𝓡 3) x) (p : UnitTwoSphere × ℝ) :
    (mpullback Ip (𝓡 3) N.cover Z (m27TwistedProductInvolution p)).2 =
      -(mpullback Ip (𝓡 3) N.cover Z p).2 := by
  have h := congrArg (fun v : TangentSpace Ip (m27TwistedProductInvolution p) => v.2)
    (twisted_cover_field_equivariant N Z p)
  rw [twistedProductInvolution_mfderiv_snd N.involution_smooth] at h
  exact h.symm

end PoincareConjecture.M35
