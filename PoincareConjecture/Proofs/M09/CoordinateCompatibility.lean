import PoincareConjecture.Proofs.M09.CoordinateConnectionBilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM








set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

theorem fderiv_bilinear_symm
    {A E V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : A → E →L[ℝ] E →L[ℝ] V) (z : A) (hG : DifferentiableAt ℝ G z)
    (hsym : ∀ᶠ q in 𝓝 z, ∀ v w, G q v w = G q w v) (d : A) (v w : E) :
    fderiv ℝ G z d v w = fderiv ℝ G z d w v := by
  have hfirst := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const v z)).clm_apply
    (hasFDerivAt_const w z)
  have hsecond := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const w z)).clm_apply
    (hasFDerivAt_const v z)
  have heq : (fun q ↦ G q v w) =ᶠ[𝓝 z] (fun q ↦ G q w v) := hsym.mono fun _ h ↦ h v w
  have h := (hfirst.congr_of_eventuallyEq heq.symm).unique hsecond
  simpa using congrArg (fun L : A →L[ℝ] V ↦ L d) h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem coordinateConnection_symm (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (hG : DifferentiableAt ℝ G z)
    (hsym : ∀ᶠ q in 𝓝 z, ∀ v w, G q v w = G q w v) (v w : E) :
    coordinateConnection G z v w = coordinateConnection G z w v := by
  have hc : coordinateConnectionCovector G z v w = coordinateConnectionCovector G z w v := by
    ext u
    simp only [coordinateConnectionCovector_apply,
      fderiv_bilinear_symm G z hG hsym (0, u) v w]
    ring
  exact congrArg (G z).inverse hc

theorem coordinateConnection_compatible (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (z : ℝ × E) (hG : DifferentiableAt ℝ G z)
    (hsym : ∀ᶠ q in 𝓝 z, ∀ v w, G q v w = G q w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G z v v) (u v w : E) :
    fderiv ℝ G z (0, u) v w =
      G z (coordinateConnection G z u v) w + G z v (coordinateConnection G z u w) := by
  have hpoint := hsym.self_of_nhds
  rw [hpoint v (coordinateConnection G z u w),
    coordinateConnection_pairing G z hpos u v w,
    coordinateConnection_pairing G z hpos u w v,
    fderiv_bilinear_symm G z hG hsym (0, u) w v]
  ring

end PoincareConjecture.Proofs.M09
