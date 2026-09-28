import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedRootClampedTransition
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedHeightFirstAmbientExtension










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞


theorem exists_saddle_root_height_first_transition_ambient
    (U V : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hU : ContDiffOn ℝ ∞ U U.source)
    (hUi : ContDiffOn ℝ ∞ U.symm U.target)
    (hV : ContDiffOn ℝ ∞ V V.source)
    (hVi : ContDiffOn ℝ ∞ V.symm V.target)
    (hUh : ∀ p ∈ U.source, (U p).1 = p.1)
    (hVh : ∀ p ∈ V.source, (V p).1 = p.1)
    (a l r b : ℝ) (hal : a < l) (hlr : l < r) (hrb : r < b)
    (hUs : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ U.source)
    (hVs : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ V.source)
    (hboundary : ∀ z ∈ Icc a b,
      (fun x : E2 => (U (z, x)).2) '' sphere 0 1 =
        (fun x : E2 => (V (z, x)).2) '' sphere 0 1)
    (u : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo l r) :
    ∃ G : D3,
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm
            ((U.symm (V (z, x))).2, z)) ∧
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Icc l r,
        G.symm ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm
            ((V.symm (U (z, x))).2, z)) ∧
      G '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) ∧
      G.symm '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ Icc l r)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ Icc l r) := by
  let S : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, ℝ × E2)
      (E2 × ℝ) (ℝ × E2) ∞ :=
    (ContinuousLinearEquiv.prodComm ℝ E2 ℝ).toDiffeomorph
  let Sp : OpenPartialHomeomorph (E2 × ℝ) (ℝ × E2) :=
    S.toHomeomorph.toOpenPartialHomeomorph
  let Si : OpenPartialHomeomorph (ℝ × E2) (E2 × ℝ) :=
    S.symm.toHomeomorph.toOpenPartialHomeomorph
  let U' := Sp.trans (U.trans Si)
  let V' := Sp.trans (V.trans Si)
  have hU' : ContDiffOn ℝ ∞ U' U'.source := by
    change ContDiffOn ℝ ∞
      (fun p : E2 × ℝ => S.symm (U (S p))) U'.source
    exact S.symm.contDiff.comp_contDiffOn
      (hU.comp S.contDiff.contDiffOn (fun p hp => by
        simpa [U', Sp, Si] using hp))
  have hU'i : ContDiffOn ℝ ∞ U'.symm U'.target := by
    change ContDiffOn ℝ ∞
      (fun p : E2 × ℝ => S.symm (U.symm (S p))) U'.target
    exact S.symm.contDiff.comp_contDiffOn
      (hUi.comp S.contDiff.contDiffOn (fun p hp => by
        simpa [U', Sp, Si] using hp))
  have hV' : ContDiffOn ℝ ∞ V' V'.source := by
    change ContDiffOn ℝ ∞
      (fun p : E2 × ℝ => S.symm (V (S p))) V'.source
    exact S.symm.contDiff.comp_contDiffOn
      (hV.comp S.contDiff.contDiffOn (fun p hp => by
        simpa [U', V', Sp, Si] using hp))
  have hV'i : ContDiffOn ℝ ∞ V'.symm V'.target := by
    change ContDiffOn ℝ ∞
      (fun p : E2 × ℝ => S.symm (V.symm (S p))) V'.target
    exact S.symm.contDiff.comp_contDiffOn
      (hVi.comp S.contDiff.contDiffOn (fun p hp => by
        simpa [U', V', Sp, Si] using hp))
  have hU'h (p : E2 × ℝ) (hp : p ∈ U'.source) : (U' p).2 = p.2 := by
    change (U (p.2, p.1)).1 = p.2
    apply hUh
    have hp' : S p ∈ U.source := by
      simpa [U', Sp, Si] using hp
    change p.swap ∈ U.source
    exact hp'
  have hV'h (p : E2 × ℝ) (hp : p ∈ V'.source) : (V' p).2 = p.2 := by
    change (V (p.2, p.1)).1 = p.2
    apply hVh
    have hp' : S p ∈ V.source := by
      simpa [U', V', Sp, Si] using hp
    change p.swap ∈ V.source
    exact hp'
  have hU's : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ U'.source := by
    intro p hp
    have hp' : p.swap ∈ U.source := hUs ⟨hp.2, hp.1⟩
    simpa [U', Sp, Si, S, OpenPartialHomeomorph.trans_source] using hp'
  have hV's : closedBall (0 : E2) 1 ×ˢ Icc a b ⊆ V'.source := by
    intro p hp
    have hp' : p.swap ∈ V.source := hVs ⟨hp.2, hp.1⟩
    simpa [U', V', Sp, Si, S, OpenPartialHomeomorph.trans_source] using hp'
  have hboundary' (z : ℝ) (hz : z ∈ Icc a b) :
      (fun x : E2 => (U' (x, z)).1) '' sphere 0 1 =
        (fun x : E2 => (V' (x, z)).1) '' sphere 0 1 := by
    simpa [U', V', Sp, Si, S] using hboundary z hz
  obtain ⟨k, radius, e, hk, hkrange, hkfix, hradius, _hes, _het,
      heformula, heiformula, he, hei, hheight, hsource0, htarget0, hprod,
      _hclamp⟩ :=
    exists_nonnested_root_clamped_transition U' V' hU' hU'i hV' hV'i hU'h hV'h
      a l r b hal hlr hrb hU's hV's hboundary'
  have htime : ∀ p ∈ e.source, (e p).1 = p.1 :=
    fun p hp => (hheight p).1
  have htimei : ∀ p ∈ e.target, (e.symm p).1 = p.1 :=
    fun p hp => (hheight p).2
  have hsab : s ∈ Icc a b := by
    constructor <;> linarith [hs.1, hs.2]
  have hsource : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ e.source := by
    intro p hp
    exact hsource0 ⟨mem_univ _, closedBall_subset_ball hradius hp.2⟩
  have htarget : Icc a b ×ˢ closedBall (0 : E2) 1 ⊆ e.target := by
    intro p hp
    exact htarget0 ⟨mem_univ _, closedBall_subset_ball hradius hp.2⟩
  have himage (z : ℝ) (_hz : z ∈ Icc l r) :
      e '' (({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1) =
        ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1 ∧
      e.symm '' (({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1) =
        ({z} : Set ℝ) ×ˢ closedBall (0 : E2) 1 := by
    exact hprod {z} (closedBall (0 : E2) 1) (Or.inr (Or.inl rfl))
  let ed := Sp.trans (e.trans Si)
  have hed : ContDiffOn ℝ ∞ ed ed.source := by
    change ContDiffOn ℝ ∞
      (fun p : E2 × ℝ => S.symm (e (S p))) ed.source
    exact S.symm.contDiff.comp_contDiffOn
      (he.comp S.contDiff.contDiffOn (fun p hp => by
        simpa [ed, Sp, Si] using hp))
  have hedi : ContDiffOn ℝ ∞ ed.symm ed.target := by
    change ContDiffOn ℝ ∞
      (fun p : E2 × ℝ => S.symm (e.symm (S p))) ed.target
    exact S.symm.contDiff.comp_contDiffOn
      (hei.comp S.contDiff.contDiffOn (fun p hp => by
        simpa [ed, Sp, Si] using hp))
  have hedh (p : E2 × ℝ) (hp : p ∈ ed.source) : (ed p).2 = p.2 := by
    change (e (p.2, p.1)).1 = p.2
    apply htime
    have hp' : S p ∈ e.source := by
      simpa [ed, Sp, Si] using hp
    change p.swap ∈ e.source
    exact hp'
  have hdisc : ∀ x ∈ closedBall (0 : E2) 1, (x, s) ∈ ed.source := by
    intro x hx
    have hp : (s, x) ∈ e.source := hsource ⟨hsab, hx⟩
    simpa [ed, Sp, Si, S, OpenPartialHomeomorph.trans_source] using hp
  obtain ⟨B, hB, _, _, _⟩ := exists_saddle_end_fiber_chart ed hed hedi hedh s hdisc
  have hB' : ∀ x : E2, B.chart x = (e (s, x)).2 := by
    intro x
    simpa [ed, Sp, Si, S] using hB x
  obtain ⟨G, hG, hGi, hstack, hstackInv⟩ :=
    exists_nonnested_height_first_ambient_extension u e he hei htime htimei
      a l r b hal hrb hsource htarget himage B s hs hB'
  refine ⟨G, ?_, ?_, hstack, hstackInv⟩
  · intro x hx z hz
    rw [hG x hx z hz, heformula (z, x), hkfix hz]
    rfl
  · intro x hx z hz
    rw [hGi x hx z hz, heiformula (z, x), hkfix hz]
    rfl

end PoincareConjecture.M25.Topology3D
