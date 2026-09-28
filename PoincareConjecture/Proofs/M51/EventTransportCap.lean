import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace SurgeryCapChart

variable {g₀ : StandardInitialMetric}
    {S S' : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier}
    {g' : RiemannianMetric 3 S'.carrier} {h : ℝ}

noncomputable def transport
    (C : SurgeryCapChart g₀ S g h)
    (q : Diffeomorph (𝓡 3) (𝓡 3) S.carrier S'.carrier ∞)
    (hq : ∀ x v w, g'.inner (q x)
      (mfderiv (𝓡 3) (𝓡 3) q x v)
      (mfderiv (𝓡 3) (𝓡 3) q x w) = g.inner x v w) :
    SurgeryCapChart g₀ S' g' h := by
  let carrier' : Set S'.carrier := q '' C.carrier
  have hsets : C.carrier = q.toHomeomorph ⁻¹' carrier' := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have hxy' : q x = q y := by
        simpa only [Diffeomorph.coe_toHomeomorph] using hxy.symm
      have hxy'' : x = y := q.injective hxy'
      simpa only [hxy''] using hy
  refine {
    radius := C.radius
    radius_eq := C.radius_eq
    tip := q C.tip
    map := q ∘ C.map
    inverse := C.inverse ∘ q.symm
    domain := C.domain
    domain_eq := C.domain_eq
    carrier := carrier'
    image := by
      rw [image_comp, C.image]
    carrier_compact := q.toHomeomorph.isCompact_image.mpr C.carrier_compact
    homeomorph := C.homeomorph.trans (q.toHomeomorph.sets hsets)
    homeomorph_eq := by
      intro x
      change q (C.homeomorph x) = q (C.map x)
      rw [C.homeomorph_eq]
    map_tip := by
      exact congrArg q C.map_tip
    left_inverse := by
      intro x hx
      change C.inverse (q.symm (q (C.map x))) = x
      rw [q.symm_apply_apply]
      exact C.left_inverse hx
    right_inverse := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      change q (C.map (C.inverse (q.symm (q x)))) = q x
      rw [q.symm_apply_apply, C.right_inverse hx]
    map_smooth := q.contMDiff.comp_contMDiffOn C.map_smooth
    inverse_smooth := C.inverse_smooth.comp q.symm.contMDiff.contMDiffOn
      (fun y hy => by
        change q.symm y ∈ C.carrier
        rcases hy with ⟨x, hx, rfl⟩
        simpa using hx)
    inner_ball := by
      have hq' : ∀ x v w, g.inner x v w = g'.inner (q x)
          (mfderiv (𝓡 3) (𝓡 3) q x v)
          (mfderiv (𝓡 3) (𝓡 3) q x w) := fun x v w => (hq x v w).symm
      rw [← RiemannianMetric.image_ball_diffeomorph g g' q hq']
      exact image_mono C.inner_ball
    outer_ball := by
      rintro y ⟨x, hx, rfl⟩
      have hd := C.outer_ball hx
      have hq' : ∀ x v w, g.inner x v w = g'.inner (q x)
          (mfderiv (𝓡 3) (𝓡 3) q x v)
          (mfderiv (𝓡 3) (𝓡 3) q x w) := fun x v w => (hq x v w).symm
      change g'.edist (q C.tip) (q x) ≤ ENNReal.ofReal
        (h * (g₀.cylindrical_end.radius + 5))
      rw [← RiemannianMetric.edist_diffeomorph g g' q hq' C.tip x]
      exact hd
  }

@[simp] theorem transport_carrier
    (C : SurgeryCapChart g₀ S g h)
    (q : Diffeomorph (𝓡 3) (𝓡 3) S.carrier S'.carrier ∞)
    (hq : ∀ x v w, g'.inner (q x)
      (mfderiv (𝓡 3) (𝓡 3) q x v)
      (mfderiv (𝓡 3) (𝓡 3) q x w) = g.inner x v w) :
    (C.transport q hq).carrier = q '' C.carrier := rfl

@[simp] theorem transport_map
    (C : SurgeryCapChart g₀ S g h)
    (q : Diffeomorph (𝓡 3) (𝓡 3) S.carrier S'.carrier ∞)
    (hq : ∀ x v w, g'.inner (q x)
      (mfderiv (𝓡 3) (𝓡 3) q x v)
      (mfderiv (𝓡 3) (𝓡 3) q x w) = g.inner x v w)
    (x : StandardCapSpace) :
    (C.transport q hq).map x = q (C.map x) := rfl

@[simp] theorem transport_tip
    (C : SurgeryCapChart g₀ S g h)
    (q : Diffeomorph (𝓡 3) (𝓡 3) S.carrier S'.carrier ∞)
    (hq : ∀ x v w, g'.inner (q x)
      (mfderiv (𝓡 3) (𝓡 3) q x v)
      (mfderiv (𝓡 3) (𝓡 3) q x w) = g.inner x v w) :
    (C.transport q hq).tip = q C.tip := rfl

end SurgeryCapChart

end PoincareConjecture
