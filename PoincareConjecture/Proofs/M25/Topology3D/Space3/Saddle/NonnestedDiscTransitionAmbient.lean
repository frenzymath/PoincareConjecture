import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedDiscTransition
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedHeightFirstAmbientExtension










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞




theorem exists_saddle_nonnested_disc_transition_ambient
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
        (fun x : E2 => (V (x, z)).1) '' sphere 0 1)
    (u : UnitTwoSphere)
    (s : ℝ) (hs : s ∈ Ioo l r) :
    ∃ (k : ℝ → ℝ) (e : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
      (G : D3),
      ContDiff ℝ ∞ k ∧
      (∀ z : ℝ, k z ∈ Icc a b) ∧
      EqOn k id (Icc l r) ∧
      e.source = {p | (p.1, k p.2) ∈ (V.trans U.symm).source} ∧
      e.target = {p | (p.1, k p.2) ∈ (V.trans U.symm).target} ∧
      (∀ p, e p = ((U.symm (V (p.1, k p.2))).1, p.2)) ∧
      (∀ p, e.symm p = ((V.symm (U (p.1, k p.2))).1, p.2)) ∧
      ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p, (e p).2 = p.2) ∧
      (∀ p, (e.symm p).2 = p.2) ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ e.source ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ e.target ∧
      (∀ z : ℝ, ∀ A : Set E2,
        (A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) →
        e '' (A ×ˢ ({z} : Set ℝ)) = A ×ˢ ({z} : Set ℝ) ∧
        e.symm '' (A ×ˢ ({z} : Set ℝ)) = A ×ˢ ({z} : Set ℝ) ∧
        (∀ x ∈ A, (e (x, z)).1 ∈ A) ∧
        (∀ y ∈ A, (e.symm (y, z)).1 ∈ A) ∧
        (∀ p ∈ (V.trans U.symm).source, p.2 ∈ Icc l r →
          e p = (V.trans U.symm) p) ∧
        (∀ p ∈ (V.trans U.symm).target, p.2 ∈ Icc l r →
          (e.symm p) = ((V.trans U.symm).symm p))) ∧
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((e (x, z)).1, z)) ∧
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G.symm ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((e.symm (x, z)).1, z)) ∧
      G '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) ∧
      G.symm '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) := by
  obtain ⟨k, e, hk, hkrange, hkfix, hesource, hetarget, heformula, heiformula,
      he, hei, heh, hehi, hsource, htarget, hslices⟩ :=
    exists_saddle_nonnested_disc_transition U V hU hUi hV hVi hUh hVh
      a l r b hal hlr hrb hUs hVs hboundary
  have heh' : ∀ p ∈ e.source, (e p).2 = p.2 := fun p _ => heh p
  have hehi' : ∀ p ∈ e.target, (e.symm p).2 = p.2 := fun p _ => hehi p
  have hsource' : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ e.source := by
    intro p hp
    exact hsource ⟨hp.1, mem_univ _⟩
  have htarget' : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ e.target := by
    intro p hp
    exact htarget ⟨hp.1, mem_univ _⟩
  obtain ⟨B, hB, _, _, _⟩ := exists_saddle_end_fiber_chart e he hei heh' s
    (fun x hx => hsource ⟨hx, mem_univ _⟩)
  have himage (z : ℝ) (hz : z ∈ Icc l r) :
      e '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ) ∧
      e.symm '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ) := by
    have h := hslices z (closedBall (0 : E2) 1) (Or.inr (Or.inl rfl))
    exact ⟨h.1, h.2.1⟩
  obtain ⟨G, hG, hGi, hstack, hstackInv⟩ :=
    exists_nonnested_product_ambient_extension u e he hei heh' hehi'
      a l r b hal hrb hsource' htarget' himage B s hs hB
  refine ⟨k, e, G, hk, hkrange, hkfix, hesource, hetarget, heformula, heiformula,
    he, hei, heh, hehi,
    hsource, htarget, hslices, hG, hGi, hstack, hstackInv⟩

end PoincareConjecture.M25.Topology3D
