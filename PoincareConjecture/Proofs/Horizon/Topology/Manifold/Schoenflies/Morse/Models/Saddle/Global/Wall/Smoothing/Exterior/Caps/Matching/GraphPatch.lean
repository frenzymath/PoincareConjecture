import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.FlatPatch
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Pasting.Immersion
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1


def planarGraphFlattening {f : Real → Real} (hf : ContDiff Real ∞ f) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun p := p - f (p 1) • EuclideanSpace.single 0 1
  invFun p := p + f (p 1) • EuclideanSpace.single 0 1
  left_inv p := by ext i; simp
  right_inv p := by ext i; simp
  contMDiff_toFun :=
    (contDiff_id.sub ((hf.comp (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff).smul
      contDiff_const)).contMDiff
  contMDiff_invFun := by
    change ContMDiff (𝓡 2) (𝓡 2) ∞ (fun p : E2 =>
      p + f (p 1) • EuclideanSpace.single 0 1)
    exact (contDiff_id.add
      ((hf.comp (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff).smul
        contDiff_const)).contMDiff

@[simp] theorem planarGraphFlattening_zero {f : Real → Real} (hf : ContDiff Real ∞ f)
    (p : E2) : planarGraphFlattening hf p 0 = p 0 - f (p 1) := by
  change (p - f (p 1) • (EuclideanSpace.single 0 1 : E2)) 0 = _
  simp

@[simp] theorem planarGraphFlattening_one {f : Real → Real} (hf : ContDiff Real ∞ f)
    (p : E2) : planarGraphFlattening hf p 1 = p 1 := by
  change (p - f (p 1) • (EuclideanSpace.single 0 1 : E2)) 1 = _
  simp



theorem eventually_range_iff_graph_of_graph_arc
    (γ : S1 → E2)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ)
    {f : Real → Real} (hf : ContDiff Real ∞ f) {q : S1}
    (hgraph : ∀ᶠ p in 𝓝 q, γ p 0 = f (γ p 1)) :
    ∀ᶠ y in 𝓝 (γ q), y ∈ range γ ↔ y 0 = f (y 1) := by
  let D := planarGraphFlattening hf
  have hDγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D ∘ γ) := by
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (D.contMDiff.comp hγ.contMDiff) (D.injective.comp hγ.isEmbedding.injective)
    intro p
    rw [mfderiv_comp p (D.contMDiff.mdifferentiable (by simp) _)
      (hγ.contMDiff.mdifferentiable (by simp) _)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      ((hγ.isImmersion.isImmersionAt p).injective_mfderiv_modelWithCornersSelf (by simp))
  have hflat : ∀ᶠ p in 𝓝 q, (D ∘ γ) p 0 = 0 := by
    filter_upwards [hgraph] with p hp
    change planarGraphFlattening hf (γ p) 0 = 0
    rw [planarGraphFlattening_zero, hp, sub_self]
  have hgerm := eventually_range_iff_wall_of_flat_arc (D ∘ γ) hDγ hflat
  have hnear := D.continuous.continuousAt.eventually hgerm
  filter_upwards [hnear] with y hy
  have hrange : D y ∈ range (D ∘ γ) ↔ y ∈ range γ := by
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p, D.injective hp⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, rfl⟩
  rw [hrange] at hy
  exact hy.trans (by
    change planarGraphFlattening hf y 0 = 0 ↔ y 0 = f (y 1)
    rw [planarGraphFlattening_zero, sub_eq_zero])



theorem eventually_circleFamily_range_iff_rounded_graph
    {a b : Real} (C : Side.CircleFamily a b)
    {v : E3} (g : S2 → E3) (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (R : Real → Real ≃ₘ[Real] Real) (t₀ : Real) (α : S1 → S2)
    (hα : ContMDiff (𝓡 1) (𝓡 2) ∞ α)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (c : Real)
    (H : Real ≃ₘ[Real] Real) {x : Real → Real} (hx : ContDiff Real ∞ x)
    (θ : Real → Real) {U : Set S2} (hU : IsOpen U)
    {t : Real} (ht : t ∈ Icc a b)
    (hC : ∀ p, C.map (t, p) =
      projectedPastedRoundedAnchor g e F R t₀ α D J c H x θ U (t, p))
    {q : S1} (hq : α q ∈ U) :
    ∀ᶠ y in 𝓝 (C.map (t, q)),
      y ∈ range (fun p => C.map (t, p)) ↔ y 0 = x (H.symm (θ t - (y 1) ^ 2)) := by
  apply eventually_range_iff_graph_of_graph_arc (fun p => C.map (t, p)) (C.embedding t ht)
    (hx.comp (H.symm.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))))
  filter_upwards [(hU.preimage hα.continuous).mem_nhds hq] with p hp
  rw [hC p, projectedPastedRoundedAnchor_of_mem g e F R t₀ α D J c H x θ
    (U := U) (t := t) (q := p) hp, sliceParam_zero, sliceParam_one]
  rfl

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching
