import PoincareConjecture.Proofs.M14.Sec6_6_RescalingPathInverse









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)



theorem rescalingPath_unique_iff
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y) :
    (∀ q : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
        (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y,
      M14IsMinimizing q → EqOn q.curve (rescalingPath hM12 hM13 G Q hQ a p).curve
        (Icc (Q * τ₁) (Q * τ₂))) ↔
      ∀ q : M14BackwardPath G T τ₁ τ₂ x y,
        M14IsMinimizing q → EqOn q.curve p.curve (Icc τ₁ τ₂) := by
  constructor
  · intro h q hq s hs
    have hm := (rescalingPath_minimizing_iff hM12 hM13 G Q hQ a q).mpr hq
    have heq := h (rescalingPath hM12 hM13 G Q hQ a q) hm
      ⟨mul_le_mul_of_nonneg_left hs.1 hQ.le, mul_le_mul_of_nonneg_left hs.2 hQ.le⟩
    simpa only [rescalingPath_curve] using heq
  · intro h q hq s hs
    let q' := rescalingPathInverse hM12 hM13 G Q hQ a q
    have hq' : M14IsMinimizing q' := by
      apply (rescalingPath_minimizing_iff hM12 hM13 G Q hQ a q').mp
      simpa only [q', rescalingPath_right_inverse] using hq
    have ht : s / Q ∈ Icc τ₁ τ₂ :=
      ⟨(le_div_iff₀ hQ).mpr (by simpa only [mul_comm] using hs.1),
        (div_le_iff₀ hQ).mpr (by simpa only [mul_comm] using hs.2)⟩
    have heq := h q' hq' ht
    change q.curve (Q * (s / Q)) = p.curve (s / Q) at heq
    rw [mul_div_cancel₀ _ hQ.ne'] at heq
    exact heq

end PoincareConjecture.M14
