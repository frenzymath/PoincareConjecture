import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem edist_transport_spherical_level_le
    (g : RiemannianMetric 3 M) {u : M → ℝ}
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u)
    {A : UnitTwoSphere → M} (hA : ContMDiff (𝓡 2) (𝓡 3) ∞ A)
    {c : ℝ} (hlevel : ∀ q, u (A q) = c)
    {V : Set M} (hV : IsOpen V) {Q : M → M}
    (hQ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q V) (hAV : ∀ q, A q ∈ V)
    {L C : ℝ} (hL : 0 < L) (hC : 0 < C)
    (htransport : ∀ q, ∀ v : TangentSpace (𝓡 3) (A q), mvfderiv (𝓡 3) u (A q) v = 0 →
      g.tangentNorm (Q (A q)) (mfderiv (𝓡 3) (𝓡 3) Q (A q) v) ≤
        L * g.tangentNorm (A q) v)
    (hparam : ∀ q, ∀ v : TangentSpace (𝓡 2) q,
      g.tangentNorm (A q) (mfderiv (𝓡 2) (𝓡 3) A q v) ≤
        C * (roundSphereMetric 2).tangentNorm q v)
    (q r : UnitTwoSphere) :
    g.edist (Q (A q)) (Q (A r)) ≤ ENNReal.ofReal (L * C * Real.pi) := by
  have hQs (q : UnitTwoSphere) := hQ.contMDiffAt (hV.mem_nhds (hAV q))
  have hsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ (Q ∘ A) := fun q => (hQs q).comp q (hA q)
  have htangent (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      mvfderiv (𝓡 3) u (A q) (mfderiv (𝓡 2) (𝓡 3) A q v) = 0 := by
    have heq : u ∘ A = fun _ => c := funext hlevel
    have hderiv := congrArg (fun T => T v)
      (mfderiv_comp q ((hu (A q)).mdifferentiableAt (by simp))
        ((hA q).mdifferentiableAt (by simp)))
    rw [heq, mfderiv_const, zero_apply] at hderiv
    change 0 = mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u (A q)
      (mfderiv (𝓡 2) (𝓡 3) A q v) at hderiv
    change (NormedSpace.fromTangentSpace (u (A q)))
      (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u (A q)
        (mfderiv (𝓡 2) (𝓡 3) A q v)) = 0
    rw [← hderiv, map_zero]
  have hbound (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      g.tangentNorm ((Q ∘ A) q) (mfderiv (𝓡 2) (𝓡 3) (Q ∘ A) q v) ≤
        (L * C) * (roundSphereMetric 2).tangentNorm q v := by
    rw [mfderiv_comp q ((hQs q).mdifferentiableAt (by simp))
      ((hA q).mdifferentiableAt (by simp))]
    exact (htransport q _ (htangent q v)).trans
      ((mul_le_mul_of_nonneg_left (hparam q v) hL.le).trans_eq (mul_assoc _ _ _).symm)
  have hd := (roundSphereMetric 2).edist_le_mul_of_tangentNorm_mfderiv_le
    g (hsmooth.of_le (by simp)) (mul_pos hL hC) hbound q r
  have hpi : (roundSphereMetric 2).edist q r ≤ ENNReal.ofReal Real.pi := by
    rw [Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_edist_eq_angle (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (Real.arccos_le_pi _)
  apply hd.trans
  rw [ENNReal.ofReal_mul (mul_pos hL hC).le]
  exact mul_le_mul' le_rfl hpi

end PoincareConjecture.RiemannianMetric
