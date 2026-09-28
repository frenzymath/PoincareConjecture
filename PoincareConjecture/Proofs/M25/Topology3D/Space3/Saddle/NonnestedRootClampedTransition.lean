import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsClampedTransition
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_nonnested_root_clamped_transition
    (U V : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
    (hU : ContDiffOn ℝ ∞ U U.source)
    (hUi : ContDiffOn ℝ ∞ U.symm U.target)
    (hV : ContDiffOn ℝ ∞ V V.source)
    (hVi : ContDiffOn ℝ ∞ V.symm V.target)
    (hUh : ∀ p ∈ U.source, (U p).2 = p.2)
    (hVh : ∀ p ∈ V.source, (V p).2 = p.2)
    (a l r b : ℝ) (hal : a < l) (hlr : l < r) (hrb : r < b)
    (hUs : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ U.source)
    (hVs : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ V.source)
    (hboundary : ∀ z ∈ Icc a b,
      (fun x : E2 => (U (x, z)).1) '' sphere 0 1 =
        (fun x : E2 => (V (x, z)).1) '' sphere 0 1) :
    ∃ (k : ℝ → ℝ) (radius : ℝ)
      (e : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2)),
      ContDiff ℝ ∞ k ∧
      (∀ z : ℝ, k z ∈ Icc a b) ∧
      EqOn k id (Icc l r) ∧
      1 < radius ∧
      e.source = {p | (p.2, k p.1) ∈ (V.trans U.symm).source} ∧
      e.target = {p | (p.2, k p.1) ∈ (V.trans U.symm).target} ∧
      (∀ p, e p = (p.1, (U.symm (V (p.2, k p.1))).1)) ∧
      (∀ p, e.symm p = (p.1, (V.symm (U (p.2, k p.1))).1)) ∧
      ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p, (e p).1 = p.1 ∧ (e.symm p).1 = p.1) ∧
      (univ ×ˢ ball (0 : E2) radius ⊆ e.source) ∧
      (univ ×ˢ ball (0 : E2) radius ⊆ e.target) ∧
      (∀ J : Set ℝ, ∀ A : Set E2,
        (A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) →
        e '' (J ×ˢ A) = J ×ˢ A ∧
        e.symm '' (J ×ˢ A) = J ×ˢ A) ∧
      (∀ z, k z = z → ∀ x ∈ closedBall (0 : E2) 1,
        ((e (z, x)).2, z) ∈ U.source ∧
        U ((e (z, x)).2, z) = V (x, z) ∧
        ((e.symm (z, x)).2, z) ∈ V.source ∧
        V ((e.symm (z, x)).2, z) = U (x, z)) := by
  let d := min (l - a) (b - r) / 2
  have hd : 0 < d := by
    dsimp [d]
    positivity
  obtain ⟨k, hk, hkrange, hkfix⟩ := exists_saddle_end_height_clamp l r d hlr hd
  have hkI (z : ℝ) : k z ∈ Icc a b := by
    have hz := hkrange z
    have hdl : d ≤ l - a := by
      dsimp [d]
      linarith [min_le_left (l - a) (b - r)]
    have hdr : d ≤ b - r := by
      dsimp [d]
      linarith [min_le_right (l - a) (b - r)]
    constructor <;> linarith [hz.1, hz.2, hdl, hdr]
  have hboundary' : ∀ z ∈ Icc a b,
      (fun x : E2 => (V (x, z)).1) '' sphere 0 1 =
        (fun x : E2 => (U (x, z)).1) '' sphere 0 1 := by
    intro z hz
    exact (hboundary z hz).symm
  obtain ⟨radius, hradius, e, he, hei, hes, het, hsmooth, hismooth,
      hheight, hsource, htarget, hprod, hclamp⟩ :=
    exists_stackClampedDiscTransition V U hV hVi hU hUi hVh hUh
      (Icc a b) isCompact_Icc hVs hUs hboundary' k hk hkI
  refine ⟨k, radius, e, hk, hkI, hkfix, hradius, ?_, ?_, ?_, ?_,
    hsmooth, hismooth, hheight, hsource, htarget, ?_, ?_⟩
  · exact hes
  · exact het
  · intro p
    exact he p
  · intro p
    exact hei p
  · intro J A hA
    exact hprod J A hA
  · intro z hz x hx
    exact hclamp z hz x hx

end PoincareConjecture.M25.Topology3D
