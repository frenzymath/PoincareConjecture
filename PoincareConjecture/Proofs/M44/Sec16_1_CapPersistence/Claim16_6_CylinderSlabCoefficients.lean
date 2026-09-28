import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

theorem cylinderPhysicalCoefficients_eq_slab
    (e : SurgeryFlowCylinder F C origin scale I U)
    {f : E → C.carrier} {V : Set E} (hV : IsOpen V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V) (hmap : MapsTo f V U)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioc a b))
    (r : ℝ) (hr : r ∈ I) (hr' : origin + r / scale ∈ Icc a b)
    (s : ℝ) (hs : s ∈ I) (hs' : origin + s / scale ∈ Icc a b)
    {x : E} (hx : x ∈ V) :
    cylinderPhysicalCoefficients e f s hs x =
      ((F.regular_slabs a b hab hJ hNo).flow.metric (origin + s / scale)).pullbackCoefficients
        (((F.regular_slabs a b hab hJ hNo).identify ⟨origin + r / scale, hr'⟩).symm ∘
          e.forward r hr ∘ f) x := by
  let S := F.regular_slabs a b hab hJ hNo
  let A := (S.identify ⟨origin + r / scale, hr'⟩).symm ∘ e.forward r hr ∘ f
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A V :=
    (S.identify ⟨origin + r / scale, hr'⟩).symm.contMDiff.comp_contMDiffOn
      ((e.forward_smooth r hr).comp hf hmap)
  have heq : e.forward s hs ∘ f =ᶠ[𝓝 x]
      (S.identify ⟨origin + s / scale, hs'⟩) ∘ A := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact (e.slab_compatibility a b hab hJ hNo r hr s hs hr' hs' (f y) (hmap hy)).symm
  have hderiv := mfderiv_comp x
    ((S.identify ⟨origin + s / scale, hs'⟩).contMDiff.mdifferentiable (by simp) (A x))
    ((hA.contMDiffAt (hV.mem_nhds hx)).mdifferentiableAt (by simp))
  ext v w
  change (F.metric (origin + s / scale)).inner ((e.forward s hs ∘ f) x)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ f) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ f) x w) = _
  rw [heq.mfderiv_eq, hderiv]
  change (F.metric (origin + s / scale)).inner ((e.forward s hs ∘ f) x)
    (mfderiv (𝓡 3) (𝓡 3) (S.identify ⟨origin + s / scale, hs'⟩) (A x)
      (mfderiv (𝓡 3) (𝓡 3) A x v))
    (mfderiv (𝓡 3) (𝓡 3) (S.identify ⟨origin + s / scale, hs'⟩) (A x)
      (mfderiv (𝓡 3) (𝓡 3) A x w)) = _
  rw [heq.self_of_nhds]
  exact S.metric_pullback ⟨origin + s / scale, hs'⟩ (A x)
    (mfderiv (𝓡 3) (𝓡 3) A x v) (mfderiv (𝓡 3) (𝓡 3) A x w)

end PoincareConjecture.M44
