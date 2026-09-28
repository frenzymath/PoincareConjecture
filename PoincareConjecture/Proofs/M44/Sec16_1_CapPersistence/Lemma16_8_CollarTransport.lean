import PoincareConjecture.Proofs.M44.Mathlib.SectionalNormalization
import PoincareConjecture.Proofs.M13.ContractionTransport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Definitions.Ch04.Pinching










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M44

variable {M N : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N]




theorem exists_collar_plane_of_positiveGram [T2Space M] {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (x : M) (C : ℝ) (u v : TangentSpace (𝓡 3) x)
    (hgram : 0 < g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)
    (hmargin : D.sectionalCurvature x u v < C⁻¹ * D.scalarCurvature x) :
    ∃ p q : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x p q ∧
      D.sectionalCurvature x p q < C⁻¹ * D.scalarCurvature x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨p, q, hp, hq, hpq, hvalue⟩ :=
    exists_orthonormal_curvature_quotient (M13.curvatureTensorLinear D x)
      (fun a b c d => D.curvatureTensor_swap_first x a b c d)
      (fun a b c d => D.curvatureTensor_swap_last x a b c d) u v hgram
  change g.inner x p p = 1 at hp
  change g.inner x q q = 1 at hq
  change g.inner x p q = 0 at hpq
  change D.curvatureTensor x p q p q = D.sectionalCurvature x u v at hvalue
  refine ⟨p, q, ⟨hp, hq, hpq⟩, ?_⟩
  calc
    D.sectionalCurvature x p q = D.curvatureTensor x p q p q := by
      simp only [LeviCivitaData.sectionalCurvature, hp, hq, hpq, one_mul,
        zero_pow (by decide : 2 ≠ 0), sub_zero, div_one]
    _ = D.sectionalCurvature x u v := hvalue
    _ < C⁻¹ * D.scalarCurvature x := hmargin




theorem exists_collar_plane_of_homothety [T2Space M] [T2Space N]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (f : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) {Q : ℝ} (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (x : M) (C : ℝ)
    (u v : TangentSpace (𝓡 3) x) (horth : LeviCivitaData.IsOrthonormalPair g x u v)
    (hmargin : D.sectionalCurvature x u v < C⁻¹ * D.scalarCurvature x) :
    ∃ p q : TangentSpace (𝓡 3) (f x), LeviCivitaData.IsOrthonormalPair h (f x) p q ∧
      D'.sectionalCurvature (f x) p q < C⁻¹ * D'.scalarCurvature (f x) := by
  let L := mfderiv (𝓡 3) (𝓡 3) f x
  apply exists_collar_plane_of_positiveGram D' (f x) C (L u) (L v)
  · change 0 < h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x u)
        (mfderiv (𝓡 3) (𝓡 3) f x u) *
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) -
      (h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x u)
        (mfderiv (𝓡 3) (𝓡 3) f x v)) ^ 2
    rw [hf, hf, hf, horth.1, horth.2.1, horth.2.2]
    simpa only [mul_one, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using
      mul_pos hQ hQ
  · change D'.sectionalCurvature (f x) (mfderiv (𝓡 3) (𝓡 3) f x u)
      (mfderiv (𝓡 3) (𝓡 3) f x v) < _
    rw [M13.homothety_sectionalCurvature_eq g h f Q hQ hf D D',
      M13.homothety_scalarCurvature_eq g h f Q hQ hf D D', ← mul_div_assoc]
    exact (div_lt_div_iff_of_pos_right hQ).mpr hmargin

end PoincareConjecture.M44
