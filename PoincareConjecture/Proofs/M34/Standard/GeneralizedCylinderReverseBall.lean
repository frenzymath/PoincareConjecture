import PoincareConjecture.Proofs.M34.Standard.LocalInverseMetricBound
import PoincareConjecture.Proofs.M34.Standard.QuadraticTangentComparison
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckSpatialMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

theorem reverse_ball_zero_of_pullback_inner_lower
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hU : IsOpen U) (h0 : 0 ∈ I) (hscale : 0 < scale)
    (g : RiemannianMetric 3 C.carrier) {o : C.carrier} (ho : o ∈ U)
    {p : F.point} (hp : e.pointMap 0 h0 o = p) {a : ℝ}
    (hcover : ∀ x ∈ (F.metric p.1).ball p.2 (a / Real.sqrt scale),
      ∃ y ∈ U, e.pointMap 0 h0 y = (⟨p.1, x⟩ : F.point))
    (hbound : ∀ x ∈ U, g.edist o x ≤ ENNReal.ofReal (2 * a) →
      ∀ v : TangentSpace (𝓡 3) x,
        (1 / 2 : ℝ) * g.inner x v v ≤ e.pullbackInner 0 h0 x v v) :
    ∀ x ∈ (F.metric p.1).ball p.2 (a / Real.sqrt scale),
      ∃ y ∈ g.ball o (2 * a) ∩ U,
        e.pointMap 0 h0 y = (⟨p.1, x⟩ : F.point) := by
  subst p
  let : T3Space C.carrier := C.t3Space
  let f := e.spatialOpenPartialHomeomorph hU 0 h0
  let h := F.metric (origin + 0 / scale)
  have hq : 0 < Real.sqrt scale := Real.sqrt_pos.mpr hscale
  have hr : (2 * Real.sqrt scale) * (a / Real.sqrt scale) = 2 * a := by
    field_simp
  have himage : h.ball (f o) (a / Real.sqrt scale) ⊆ f.target := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hcover x hx
    have he' : e.forward 0 h0 y = x := eq_of_heq (Sigma.mk.inj_iff.mp he).2
    exact ⟨y, hy, he'⟩
  have hlocal := g.ball_subset_image_ball_of_forward_tangentNorm_le h f
    ((e.spatialOpenPartialHomeomorph_contMDiffOn hU 0 h0).of_le (by simp))
    ((e.spatialOpenPartialHomeomorph_symm_contMDiffOn hU 0 h0).of_le (by simp))
    ho (mul_pos two_pos hq) himage (fun x hx hd v => by
      apply g.tangentNorm_le_two_sqrt_mul_of_half_inner_le h v _ hscale.le
      exact hbound x hx (by simpa only [hr] using hd) v)
  rw [hr] at hlocal
  intro x hx
  obtain ⟨y, hy, he⟩ := hlocal hx
  refine ⟨y, hy, ?_⟩
  exact congrArg (fun z : (F.slice (origin + 0 / scale)).carrier =>
    (⟨origin + 0 / scale, z⟩ : F.point)) he

end PoincareConjecture.GeneralizedFlowCylinder
