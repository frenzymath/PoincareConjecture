import PoincareConjecture.Proofs.M35.Thm12_28.SliceCylinders
import PoincareConjecture.Proofs.M35.Mathlib.DiffeomorphDerivative
import PoincareConjecture.Definitions.Ch11.SingularLimits










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.OrdinaryRealization



theorem sliceCylinder_pullbackInner {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {a : ℝ} (ha : a ∈ J) (Q : ℝ) (hQ : 0 < Q) (I : Set ℝ)
    (U : Set (slice J a).carrier) (htime : ∀ s ∈ I, a + s / Q ∈ J)
    (s : ℝ) (hs : s ∈ I) (x : (slice J a).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (sliceCylinder F ha Q hQ I U htime).pullbackInner s hs x v w =
      Q * (F.metric (a + s / Q)).inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (sliceDiffeomorph ha) x v)
        (mfderiv (𝓡 3) (𝓡 3) (sliceDiffeomorph ha) x w) := by
  let e := sliceDiffeomorph ha
  let e' := sliceDiffeomorph (htime s hs)
  change Q * (metric F (a + s / Q)).inner (e'.symm (e x))
    (mfderiv (𝓡 3) (𝓡 3) (e'.symm ∘ e) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e'.symm ∘ e) x w) = _
  rw [e'.symm.mfderiv_comp (by simp)]
  exact congrArg (fun r : ℝ => Q * r)
    (metric_pullback F (htime s hs) (e x)
      (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))



theorem sliceCylinder_roundCylinderPullback {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) {a : ℝ} (ha : a ∈ J)
    (Q : ℝ) (hQ : 0 < Q) (I : Set ℝ) (U : Set (slice J a).carrier)
    (htime : ∀ s ∈ I, a + s / Q ∈ J)
    (f : StandardCylinderSpace → StandardCapSpace) (s : ℝ) (hs : s ∈ I) :
    generalizedCylinderPullback (sliceCylinder F ha Q hQ I U htime)
        (fun z => (sliceDiffeomorph ha).symm (f z)) s =
      fun z v w => Q * roundCylinderPullback (F.metric (a + s / Q)) f z v w := by
  unfold generalizedCylinderPullback
  rw [dif_pos hs]
  funext z v w
  rw [sliceCylinder_pullbackInner]
  let e := sliceDiffeomorph ha
  have hc (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      mfderiv (𝓡 3) (𝓡 3) e (e.symm (f z))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (fun z => e.symm (f z)) z v) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z v := by
    exact congrArg (fun L => L v)
      (e.mfderiv_cancel_left (I₁ := (𝓡 2).prod 𝓘(ℝ, ℝ)) (by simp) f z)
  change Q * (F.metric (a + s / Q)).inner (f z)
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm (f z))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (fun z => e.symm (f z)) z v))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm (f z))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (fun z => e.symm (f z)) z w)) = _
  rw [hc v, hc w]
  rfl

end PoincareConjecture.M35.OrdinaryRealization
