import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCoefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoefficientTransport
import PoincareConjecture.Proofs.M44.Mathlib.OpenChartDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem metric_inner_eq_of_chart_coefficients
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (E n) M] [ChartedSpace (E n) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    (a : PartialDiffeomorph (𝓡 n) (𝓡 n) (E n) M ∞)
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {f : M → N} (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f a.target) (c : ℝ)
    (hcoeff : ∀ x ∈ a.source, ∀ v w : E n,
      g.pullbackCoefficients a x v w = c * h.pullbackCoefficients (f ∘ a) x v w) :
    ∀ y ∈ a.target, ∀ v w : TangentSpace (𝓡 n) y,
      g.inner y v w = c * h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) := by
  have hread (x : E n) (hx : x ∈ a.source) :
      ∀ v w : TangentSpace (𝓡 n) (a x),
        g.inner (a x) v w = c * h.inner (f (a x))
          (mfderiv (𝓡 n) (𝓡 n) f (a x) v) (mfderiv (𝓡 n) (𝓡 n) f (a x) w) := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) a x).IsInvertible :=
      ⟨(a.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ hx).mfderivToContinuousLinearEquiv
        (by simp), rfl⟩
    intro v w
    obtain ⟨v0, hv⟩ := hi.surjective v
    obtain ⟨w0, hw⟩ := hi.surjective w
    have hcomp := mfderiv_comp x
      ((hf.contMDiffAt (a.open_target.mem_nhds (a.map_source hx))).mdifferentiableAt (by simp))
      ((a.contMDiffOn.contMDiffAt (a.open_source.mem_nhds hx)).mdifferentiableAt (by simp))
    have hcoef := hcoeff x hx v0 w0
    change g.inner (a x) (mfderiv (𝓡 n) (𝓡 n) a x v0) (mfderiv (𝓡 n) (𝓡 n) a x w0) =
      c * h.inner (f (a x)) (mfderiv (𝓡 n) (𝓡 n) (f ∘ a) x v0)
        (mfderiv (𝓡 n) (𝓡 n) (f ∘ a) x w0) at hcoef
    rw [hcomp] at hcoef
    change g.inner (a x) (mfderiv (𝓡 n) (𝓡 n) a x v0) (mfderiv (𝓡 n) (𝓡 n) a x w0) =
      c * h.inner (f (a x))
        (mfderiv (𝓡 n) (𝓡 n) f (a x) (mfderiv (𝓡 n) (𝓡 n) a x v0))
        (mfderiv (𝓡 n) (𝓡 n) f (a x) (mfderiv (𝓡 n) (𝓡 n) a x w0)) at hcoef
    simpa only [hv, hw] using hcoef
  intro y hy
  have h := hread (a.symm y) (a.map_target hy)
  have hax : a (a.symm y) = y := a.right_inv hy
  rw [hax] at h
  exact h

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

def cylinderTargetTransport
    (e : SurgeryFlowCylinder F C origin scale I U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) (E 3) C.carrier ∞)
    (s : ℝ) (hs : s ∈ I) :
    (⟨f.target, f.open_target⟩ : Opens C.carrier) → (F.slice (origin + s / scale)).carrier :=
  fun x => e.forward s hs x.1

theorem cylinderTargetTransport_smooth
    (e : SurgeryFlowCylinder F C origin scale I U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) (E 3) C.carrier ∞) (hmap : f.target ⊆ U)
    (s : ℝ) (hs : s ∈ I) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (cylinderTargetTransport e f s hs) := by
  apply contMDiffOn_univ.mp
  exact (e.forward_smooth s hs).comp contMDiff_subtype_val.contMDiffOn
    (fun y _ => hmap y.2)

theorem cylinderTargetTransport_invertible
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) (E 3) C.carrier ∞) (hmap : f.target ⊆ U)
    (s : ℝ) (hs : s ∈ I) (x : (⟨f.target, f.open_target⟩ : Opens C.carrier)) :
    (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs) x).IsInvertible := by
  have he := (cylinderSliceChart e hU s hs).isLocalDiffeomorphAt
    (𝓡 3) (𝓡 3) ∞ (hmap x.2)
  have hi := open_inclusion_isLocalDiffeomorph (I := 𝓡 3)
    (⟨f.target, f.open_target⟩ : Opens C.carrier)
  have hde : (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x.1).IsInvertible :=
    ⟨he.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hdi : (mfderiv (𝓡 3) (𝓡 3) (Subtype.val :
      (⟨f.target, f.open_target⟩ : Opens C.carrier) → C.carrier) x).IsInvertible :=
    ⟨hi.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩
  change (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ Subtype.val) x).IsInvertible
  rw [mfderiv_comp x
    (((e.forward_smooth s hs).contMDiffAt (hU.mem_nhds (hmap x.2))).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) x)]
  exact hde.comp hdi

theorem cylinderTargetTransport_metric
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) (E 3) C.carrier ∞) (hmap : f.target ⊆ U)
    (s : ℝ) (hs : s ∈ I)
    (g : RiemannianMetric 3 (⟨f.target, f.open_target⟩ : Opens C.carrier))
    (hcoeff : ∀ (p : (⟨f.target, f.open_target⟩ : Opens C.carrier)),
      ∀ x ∈ f.source, ∀ v w : E 3,
        g.pullbackCoefficients (targetChart f p) x v w =
          e.pullbackInner s hs (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
            (mfderiv (𝓡 3) (𝓡 3) f x w))
    (y : (⟨f.target, f.open_target⟩ : Opens C.carrier))
    (v w : TangentSpace (𝓡 3) y) :
    g.inner y v w = scale * (F.metric (origin + s / scale)).inner
      (cylinderTargetTransport e f s hs y)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs) y v)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs) y w) := by
  apply metric_inner_eq_of_chart_coefficients (targetPartialDiffeomorph f y) g
    (F.metric (origin + s / scale))
    (cylinderTargetTransport_smooth e f hmap s hs).contMDiffOn scale _ y (mem_univ _) v w
  intro x hx a b
  have heq : cylinderTargetTransport e f s hs ∘ targetChart f y =ᶠ[𝓝 x]
      e.forward s hs ∘ f := by
    filter_upwards [f.open_source.mem_nhds hx] with z hz
    change e.forward s hs (targetChart f y z).1 = e.forward s hs (f z)
    rw [targetChart_val f y hz]
  have hread := pullbackCoefficients_congr_of_eventuallyEq (F.metric (origin + s / scale)) heq
  change g.pullbackCoefficients (targetChart f y) x a b =
    scale * (F.metric (origin + s / scale)).pullbackCoefficients
      (cylinderTargetTransport e f s hs ∘ targetChart f y) x a b
  rw [hread]
  exact (hcoeff y x hx a b).trans
    (cylinderPhysicalCoefficients_normalization e hU f.open_source f.contMDiffOn
      (fun _ hz => hmap (f.map_source hz)) s hs hx a b).symm

end PoincareConjecture.M44
