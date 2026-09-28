import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundMetric
import Mathlib.Geometry.Manifold.Algebra.Structures










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




noncomputable def m60SphereConformalFactor (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (p : UnitTwoSphere) : ℝ :=
  g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
    (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0))



theorem m60SphereConformalFactor_nonneg (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (p : UnitTwoSphere) :
    0 ≤ m60SphereConformalFactor g f p := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact real_inner_self_nonneg (x := mfderiv (𝓡 2) (𝓡 n) f p
    (EuclideanSpace.basisFun (Fin 2) ℝ 0))



theorem m60SphereConformalFactor_spec (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hc : M60WeaklyConformal g f)
    (p : UnitTwoSphere) (v w : TangentSpace (𝓡 2) p) :
    g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p w) =
      m60SphereConformalFactor g f p * m60RoundSphereInner p v w := by
  obtain ⟨s, -, hs⟩ := hc p
  have he : m60RoundSphereInner p (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) = 1 := by
    rw [m60RoundSphereInner_eq_inner]
    change inner ℝ (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) = 1
    simp only [real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow]
  have hscale : m60SphereConformalFactor g f p = s := by
    unfold m60SphereConformalFactor
    rw [hs, he, mul_one]
  rw [hscale]
  exact hs v w



theorem m60SphereConformalFactor_eq_zero_iff (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hc : M60WeaklyConformal g f) (p : UnitTwoSphere) :
    m60SphereConformalFactor g f p = 0 ↔ p ∈ m60SphereBranchSet (n := n) f := by
  constructor
  · intro h
    change mfderiv (𝓡 2) (𝓡 n) f p = 0
    ext v
    change mfderiv (𝓡 2) (𝓡 n) f p v = 0
    by_contra hv
    have hp := g.pos (f p) _ hv
    rw [m60SphereConformalFactor_spec g f hc, h, zero_mul] at hp
    exact lt_irrefl 0 hp
  · intro h
    change mfderiv (𝓡 2) (𝓡 n) f p = 0 at h
    simp [m60SphereConformalFactor, h]



theorem m60SphereConformalFactor_contMDiff (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hc : M60WeaklyConformal g f) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (m60SphereConformalFactor g f) := by
  intro p
  let v : TangentSpace (𝓡 2) p := EuclideanSpace.basisFun (Fin 2) ℝ 0
  let V := FiberBundle.extend LoopPlane v
  have hV : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun q => (⟨q, V q⟩ : TangentBundle (𝓡 2) UnitTwoSphere)) p :=
    FiberBundle.contMDiffAt_extend (𝓡 2) LoopPlane v
  let A : UnitTwoSphere → ℝ := fun q =>
    M60.metricPullbackForm (n := 2) g f q (V q) (V q)
  let B : UnitTwoSphere → ℝ := fun q => m60RoundSphereMetric.inner q (V q) (V q)
  have hA : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ A p := by
    have h := (M60.metricPullbackForm_contMDiffAt g (hf p)).clm_bundle_apply₂
      (F₃ := ℝ) (E₃ := Bundle.Trivial UnitTwoSphere ℝ) hV hV
    simpa using (Bundle.contMDiffAt_totalSpace.mp h).2
  have hB : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ B p := by
    have h := (m60RoundSphereMetric.contMDiff p).clm_bundle_apply₂
      (F₃ := ℝ) (E₃ := Bundle.Trivial UnitTwoSphere ℝ) hV hV
    simpa using (Bundle.contMDiffAt_totalSpace.mp h).2
  have hBp : B p = 1 := by
    dsimp only [B, V]
    rw [FiberBundle.extend_apply_self, m60RoundSphereMetric_inner,
      m60RoundSphereInner_eq_inner]
    change inner ℝ (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) = 1
    simp only [real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow]
  have hne : B p ≠ 0 := by rw [hBp]; norm_num
  apply (hA.div₀ hB hne).congr_of_eventuallyEq
  filter_upwards [hB.continuousAt.eventually_ne hne] with q hq
  change m60SphereConformalFactor g f q = A q / B q
  dsimp only [A, B]
  rw [M60.metricPullbackForm_apply, m60SphereConformalFactor_spec g f hc,
    m60RoundSphereMetric_inner]
  exact (mul_div_cancel_right₀ _ hq).symm

end PoincareConjecture
