import PoincareConjecture.Proofs.M14.Sec6_6_RescalingExponential
import PoincareConjecture.Proofs.M14.Sec6_6_RescalingPathUnique

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hCoordinates : M12MetricPredecessors.{0} n)
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

private theorem uniquePathData_start_zero {S : GeneralizedLGeometryTransport n X time I}
    {T b τ : ℝ} {x y : S.Point} (hb : b = 0) (f : ℝ → S.Point) :
    (∃ p : M14BackwardPath S T b τ x y,
      EqOn p.curve f (Icc b τ) ∧ M14IsMinimizing p ∧
        ∀ q : M14BackwardPath S T b τ x y,
          M14IsMinimizing q → EqOn q.curve p.curve (Icc b τ)) ↔
    (∃ p : M14BackwardPath S T 0 τ x y,
      EqOn p.curve f (Icc 0 τ) ∧ M14IsMinimizing p ∧
        ∀ q : M14BackwardPath S T 0 τ x y,
          M14IsMinimizing q → EqOn q.curve p.curve (Icc 0 τ)) := by
  subst b
  rfl

include hCoordinates in

theorem rescalingUniqueBranch_iff {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z : G.Horizontal x) :
    M14UniqueMinimizingBranch G T τ x E Z ↔
      M14UniqueMinimizingBranch (rescalingTransport hM12 hM13 G Q hQ a)
        (parabolicTime Q a T) (Q * τ) x E'
          (rescalingInitialEquiv G.spacetime Q hQ a x Z) := by
  let A := rescalingInitialEquiv G.spacetime Q hQ a x
  have hdom : (Z, Real.sqrt τ) ∈ E.domain ↔ (A Z, Real.sqrt (Q * τ)) ∈ E'.domain := by
    simpa only [Real.sqrt_mul hQ.le] using
      rescalingExponential_domain_iff hCoordinates hM12 hM13 G Q hQ a E E' Z (Real.sqrt τ)
  constructor
  · rintro ⟨hs, p, hc, hm, hu⟩
    refine ⟨hdom.mp hs, ?_⟩
    have he : E'.gamma (A Z) (Real.sqrt (Q * τ)) = E.gamma Z (Real.sqrt τ) := by
      simpa only [Real.sqrt_mul hQ.le] using
        rescalingExponential_gamma hCoordinates hM12 hM13 G Q hQ a E E' Z (Real.sqrt τ) hs
    rw [he]
    have hdata : ∃ p' : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
        (parabolicTime Q a T) (Q * 0) (Q * τ) x (E.gamma Z (Real.sqrt τ)),
        EqOn p'.curve (fun r => E'.gamma (A Z) (Real.sqrt r)) (Icc (Q * 0) (Q * τ)) ∧
        M14IsMinimizing p' ∧
        ∀ q : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
            (parabolicTime Q a T) (Q * 0) (Q * τ) x (E.gamma Z (Real.sqrt τ)),
          M14IsMinimizing q → EqOn q.curve p'.curve (Icc (Q * 0) (Q * τ)) := by
      refine ⟨rescalingPath hM12 hM13 G Q hQ a p, ?_,
        (rescalingPath_minimizing_iff hM12 hM13 G Q hQ a p).mpr hm,
        (rescalingPath_unique_iff hM12 hM13 G Q hQ a p).mpr hu⟩
      intro r hr
      have ht : r / Q ∈ Icc 0 τ := by
        exact ⟨div_nonneg (by simpa only [mul_zero] using hr.1) hQ.le,
          (div_le_iff₀ hQ).mpr (by simpa only [mul_comm] using hr.2)⟩
      change p.curve (r / Q) = E'.gamma (A Z) (Real.sqrt r)
      rw [hc ht]
      have heq := rescalingExponential_originalTime hCoordinates hM12 hM13 G Q hQ a
        E E' Z hs ht
      simpa only [mul_div_cancel₀ _ hQ.ne'] using heq.symm
    exact (uniquePathData_start_zero (mul_zero Q) _).mp hdata
  · rintro ⟨hs', hp⟩
    have hs := hdom.mpr hs'
    refine ⟨hs, ?_⟩
    have he : E'.gamma (A Z) (Real.sqrt (Q * τ)) = E.gamma Z (Real.sqrt τ) := by
      simpa only [Real.sqrt_mul hQ.le] using
        rescalingExponential_gamma hCoordinates hM12 hM13 G Q hQ a E E' Z (Real.sqrt τ) hs
    rw [he] at hp
    have hdata : ∃ p' : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
        (parabolicTime Q a T) (Q * 0) (Q * τ) x (E.gamma Z (Real.sqrt τ)),
        EqOn p'.curve (fun r => E'.gamma (A Z) (Real.sqrt r)) (Icc (Q * 0) (Q * τ)) ∧
        M14IsMinimizing p' ∧
        ∀ q : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
            (parabolicTime Q a T) (Q * 0) (Q * τ) x (E.gamma Z (Real.sqrt τ)),
          M14IsMinimizing q → EqOn q.curve p'.curve (Icc (Q * 0) (Q * τ)) := by
      exact (uniquePathData_start_zero (mul_zero Q) _).mpr hp
    obtain ⟨p', hc, hm, hu⟩ := hdata
    let p := rescalingPathInverse hM12 hM13 G Q hQ a p'
    have hright : rescalingPath hM12 hM13 G Q hQ a p = p' :=
      rescalingPath_right_inverse hM12 hM13 G Q hQ a p'
    refine ⟨p, ?_, ?_, ?_⟩
    · intro r hr
      change p'.curve (Q * r) = E.gamma Z (Real.sqrt r)
      rw [hc ⟨mul_le_mul_of_nonneg_left hr.1 hQ.le,
        mul_le_mul_of_nonneg_left hr.2 hQ.le⟩]
      exact rescalingExponential_originalTime hCoordinates hM12 hM13 G Q hQ a E E' Z hs hr
    · apply (rescalingPath_minimizing_iff hM12 hM13 G Q hQ a p).mp
      simpa only [hright] using hm
    · apply (rescalingPath_unique_iff hM12 hM13 G Q hQ a p).mp
      simpa only [hright] using hu

end PoincareConjecture.M14
