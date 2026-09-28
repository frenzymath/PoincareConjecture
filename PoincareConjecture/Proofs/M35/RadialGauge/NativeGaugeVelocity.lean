import PoincareConjecture.Proofs.M35.RadialGauge.TensionDomainPullback
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.RadialGauge

open Uniqueness DeTurckNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem mapTension_eq_neg_pushedDeTurck
    (g b : RiemannianMetric n V) (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞)
    (D : LeviCivitaData g) (B : LeviCivitaData b)
    (K : LeviCivitaData (gaugePullbackMetric g Φ.symm)) (x : V) :
    mapTension D B Φ x = -intrinsicDeTurckField K B (Φ x) := by
  have hΦ : ContDiff ℝ ∞ (Φ : V → V) := contMDiff_iff_contDiff.mp Φ.contMDiff
  have h := mapTension_domain_pullback g b Φ.symm D B K hΦ (Φ x)
  have hid : (Φ : V → V) ∘ (Φ.symm : V → V) = id := funext Φ.apply_symm_apply
  rw [hid, Φ.symm_apply_apply, mapTension_id] at h
  exact h.symm

theorem mapTension_original_intrinsic
    (g b : RiemannianMetric 3 StandardCapSpace)
    (hg : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hc : MetricComplete g) (D : LeviCivitaData g) (B : LeviCivitaData b)
    (DI : LeviCivitaData (intrinsicSpatialMetric g hg hc))
    {F : StandardCapSpace → StandardCapSpace} (hF : ContDiff ℝ ∞ F) (x : StandardCapSpace) :
    mapTension D B (F ∘ intrinsicSpatialCoordinate g) x =
      mapTension DI B F (intrinsicSpatialCoordinate g x) := by
  let S := intrinsicSpatialDiffeomorph g hg hc
  have hS : ContDiff ℝ ∞ (S : StandardCapSpace → StandardCapSpace) :=
    contMDiff_iff_contDiff.mp S.contMDiff
  have h := mapTension_domain_pullback g b S.symm D B DI (hF.comp hS) (S x)
  have heq : (F ∘ (S : StandardCapSpace → StandardCapSpace)) ∘
      (S.symm : StandardCapSpace → StandardCapSpace) = F := by
    funext y
    simp only [Function.comp_apply, S.apply_symm_apply]
  rw [heq, S.symm_apply_apply] at h
  exact h.symm

end PoincareConjecture.M35.RadialGauge
