import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedRootClampedTransition










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D



theorem exists_saddle_nonnested_disc_transition_band
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
    ∃ (k : ℝ → ℝ) (e : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ)),
      ContDiff ℝ ∞ k ∧
      (∀ z : ℝ, k z ∈ Icc a b) ∧
      EqOn k id (Icc l r) ∧
      (e '' (closedBall (0 : E2) 1 ×ˢ Icc a b) =
        closedBall (0 : E2) 1 ×ˢ Icc a b) ∧
      (e.symm '' (closedBall (0 : E2) 1 ×ˢ Icc a b) =
        closedBall (0 : E2) 1 ×ˢ Icc a b) := by
  obtain ⟨k, radius, e, hk, hkrange, hkfix, _hradius, _hesource, _hetarget,
      _he, _hei, _hsmooth, _hismooth, _hheight, _hsource, _htarget, hprod,
      _hclamp⟩ :=
    exists_nonnested_root_clamped_transition U V hU hUi hV hVi hUh hVh
      a l r b hal hlr hrb hUs hVs hboundary
  let S : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, ℝ × E2)
      (E2 × ℝ) (ℝ × E2) ∞ :=
    (ContinuousLinearEquiv.prodComm ℝ E2 ℝ).toDiffeomorph
  let Sp : OpenPartialHomeomorph (E2 × ℝ) (ℝ × E2) :=
    S.toHomeomorph.toOpenPartialHomeomorph
  let Si : OpenPartialHomeomorph (ℝ × E2) (E2 × ℝ) :=
    S.symm.toHomeomorph.toOpenPartialHomeomorph
  let ed : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ) :=
    Sp.trans (e.trans Si)
  have hed (p : E2 × ℝ) :
      ed p = ((e (p.2, p.1)).2, (e (p.2, p.1)).1) := by
    simp [ed, Sp, Si, S]
    rfl
  have hedi (p : E2 × ℝ) :
      ed.symm p = ((e.symm (p.2, p.1)).2, (e.symm (p.2, p.1)).1) := by
    simp [ed, Sp, Si, S]
    rfl
  have hstack := hprod (Icc a b) (closedBall (0 : E2) 1)
    (Or.inr (Or.inl rfl))
  have hstack' :
      ed '' (closedBall (0 : E2) 1 ×ˢ Icc a b) =
        closedBall (0 : E2) 1 ×ˢ Icc a b := by
    ext p
    rcases p with ⟨x, z⟩
    constructor
    · rintro ⟨q, hq, hqeq⟩
      rcases q with ⟨x, z⟩
      have hq' : (z, x) ∈ Icc a b ×ˢ closedBall (0 : E2) 1 :=
        ⟨hq.2, hq.1⟩
      have hm : e (z, x) ∈ Icc a b ×ˢ closedBall (0 : E2) 1 := by
        rw [← hstack.1]
        exact ⟨(z, x), hq', rfl⟩
      rw [← hqeq, hed]
      exact ⟨hm.2, hm.1⟩
    · rintro ⟨hp, hz⟩
      have hp' : (z, x) ∈ Icc a b ×ˢ closedBall (0 : E2) 1 :=
        ⟨hz, hp⟩
      have hm : (z, x) ∈ e '' (Icc a b ×ˢ closedBall (0 : E2) 1) := by
        rw [hstack.1]
        exact hp'
      rcases hm with ⟨q, hq, hqe⟩
      rcases q with ⟨z', x'⟩
      refine ⟨(x', z'), ⟨hq.2, hq.1⟩, ?_⟩
      rw [hed, hqe]
  have hstackInv' :
      ed.symm '' (closedBall (0 : E2) 1 ×ˢ Icc a b) =
        closedBall (0 : E2) 1 ×ˢ Icc a b := by
    ext p
    rcases p with ⟨x, z⟩
    constructor
    · rintro ⟨q, hq, hqeq⟩
      rcases q with ⟨x, z⟩
      have hq' : (z, x) ∈ Icc a b ×ˢ closedBall (0 : E2) 1 :=
        ⟨hq.2, hq.1⟩
      have hm : e.symm (z, x) ∈ Icc a b ×ˢ closedBall (0 : E2) 1 := by
        rw [← hstack.2]
        exact ⟨(z, x), hq', rfl⟩
      rw [← hqeq, hedi]
      exact ⟨hm.2, hm.1⟩
    · rintro ⟨hp, hz⟩
      have hp' : (z, x) ∈ Icc a b ×ˢ closedBall (0 : E2) 1 :=
        ⟨hz, hp⟩
      have hm : (z, x) ∈ e.symm '' (Icc a b ×ˢ closedBall (0 : E2) 1) := by
        rw [hstack.2]
        exact hp'
      rcases hm with ⟨q, hq, hqe⟩
      rcases q with ⟨z', x'⟩
      refine ⟨(x', z'), ⟨hq.2, hq.1⟩, ?_⟩
      rw [hedi, hqe]
  exact ⟨k, ed, hk, hkrange, hkfix, hstack', hstackInv'⟩

end PoincareConjecture.M25.Topology3D
