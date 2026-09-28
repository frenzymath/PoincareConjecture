import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedDiscTransition
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)


theorem exists_nonnested_partial_physical_transport
    (u : UnitTwoSphere)
    (Phi : OpenPartialHomeomorph P P)
    (hPhi : ContDiffOn ℝ ∞ Phi Phi.source)
    (hPhii : ContDiffOn ℝ ∞ Phi.symm Phi.target)
    (hheight : ∀ p ∈ Phi.source, (Phi p).1 = p.1)
    (hheighti : ∀ p ∈ Phi.target, (Phi.symm p).1 = p.1) :
    ∃ K : OpenPartialHomeomorph E3 E3,
      (∀ x : E2, ∀ z : ℝ, (z, x) ∈ Phi.source →
        K ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((Phi (z, x)).2, z)) ∧
      (∀ x : E2, ∀ z : ℝ, (z, x) ∈ Phi.target →
        K.symm ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((Phi.symm (z, x)).2, z)) ∧
      ContDiffOn ℝ ∞ K K.source ∧
      ContDiffOn ℝ ∞ K.symm K.target := by
  let L := heightPlaneCoordinates u
  let SW : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, P) (E2 × ℝ) P ∞ :=
    (ContinuousLinearEquiv.prodComm ℝ E2 ℝ).toDiffeomorph
  let Lp : OpenPartialHomeomorph E3 (E2 × ℝ) :=
    L.toHomeomorph.toOpenPartialHomeomorph
  let SWp : OpenPartialHomeomorph (E2 × ℝ) P :=
    SW.toHomeomorph.toOpenPartialHomeomorph
  let SWip : OpenPartialHomeomorph P (E2 × ℝ) :=
    SW.symm.toHomeomorph.toOpenPartialHomeomorph
  let Lip : OpenPartialHomeomorph (E2 × ℝ) E3 :=
    L.symm.toHomeomorph.toOpenPartialHomeomorph
  let K : OpenPartialHomeomorph E3 E3 :=
    Lp.trans (SWp.trans (Phi.trans (SWip.trans Lip)))
  have hKi (p : P) (hp : p ∈ Phi.target) :
      (Phi.symm p).1 = p.1 := hheighti p hp
  have hforward (x : E2) (z : ℝ) (hp : (z, x) ∈ Phi.source) :
      K (L.symm (x, z)) = L.symm ((Phi (z, x)).2, z) := by
    change L.symm (SW.symm (Phi (SW (L (L.symm (x, z)))))) = _
    rw [L.apply_symm_apply]
    change L.symm ((Phi (z, x)).2, (Phi (z, x)).1) = _
    rw [hheight (z, x) hp]
  have hinverse (x : E2) (z : ℝ) (hp : (z, x) ∈ Phi.target) :
      K.symm (L.symm (x, z)) = L.symm ((Phi.symm (z, x)).2, z) := by
    change L.symm (SW.symm (Phi.symm (SW (L (L.symm (x, z)))))) = _
    rw [L.apply_symm_apply]
    change L.symm ((Phi.symm (z, x)).2, (Phi.symm (z, x)).1) = _
    rw [hKi (z, x) hp]
  have hsource (y : E3) (hy : y ∈ K.source) : SW (L y) ∈ Phi.source := by
    change y ∈ (Lp.trans (SWp.trans (Phi.trans (SWip.trans Lip)))).source at hy
    rw [OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy
    exact hy.2.2.1
  have htarget (y : E3) (hy : y ∈ K.target) : SW (L y) ∈ Phi.target := by
    change y ∈ (Lp.trans (SWp.trans (Phi.trans (SWip.trans Lip)))).target at hy
    rw [OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.trans_target] at hy
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hy
    have hpre := hy.1.1.2
    change (SWip.trans Lip).symm y ∈ Phi.target at hpre
    have heq : (SWip.trans Lip).symm y = SW (L y) := by rfl
    rw [heq] at hpre
    exact hpre
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · exact hforward
  · exact hinverse
  · change ContDiffOn ℝ ∞
      (fun y : E3 => L.symm (SW.symm (Phi (SW (L y))))) K.source
    have hSL : ContDiffOn ℝ ∞ (fun y : E3 => SW (L y)) K.source :=
      (SW.contDiff.comp L.contDiff).contDiffOn
    have hPhiSL : ContDiffOn ℝ ∞ (fun y : E3 => Phi (SW (L y))) K.source :=
      hPhi.comp hSL hsource
    have hSW : ContDiffOn ℝ ∞
        (fun y : E3 => SW.symm (Phi (SW (L y)))) K.source :=
      SW.symm.contDiff.contDiffOn.comp hPhiSL (fun _ _ => mem_univ _)
    exact L.symm.contDiff.contDiffOn.comp hSW (fun _ _ => mem_univ _)
  · change ContDiffOn ℝ ∞
      (fun y : E3 => L.symm (SW.symm (Phi.symm (SW (L y))))) K.target
    have hSL : ContDiffOn ℝ ∞ (fun y : E3 => SW (L y)) K.target :=
      (SW.contDiff.comp L.contDiff).contDiffOn
    have hPhiSL : ContDiffOn ℝ ∞ (fun y : E3 => Phi.symm (SW (L y))) K.target :=
      hPhii.comp hSL htarget
    have hSW : ContDiffOn ℝ ∞
        (fun y : E3 => SW.symm (Phi.symm (SW (L y)))) K.target :=
      SW.symm.contDiff.contDiffOn.comp hPhiSL (fun _ _ => mem_univ _)
    exact L.symm.contDiff.contDiffOn.comp hSW (fun _ _ => mem_univ _)



theorem nonnested_partial_physical_transport_stack
    (u : UnitTwoSphere)
    (Phi : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hPhi : ContDiffOn ℝ ∞ Phi Phi.source)
    (hPhii : ContDiffOn ℝ ∞ Phi.symm Phi.target)
    (hheight : ∀ p ∈ Phi.source, (Phi p).1 = p.1)
    (hheighti : ∀ p ∈ Phi.target, (Phi.symm p).1 = p.1)
    (hsource : ∀ J : Set ℝ,
      J ×ˢ closedBall (0 : E2) 1 ⊆ Phi.source)
    (htarget : ∀ J : Set ℝ,
      J ×ˢ closedBall (0 : E2) 1 ⊆ Phi.target)
    (hprod : ∀ J : Set ℝ,
      Phi '' (J ×ˢ closedBall (0 : E2) 1) =
        J ×ˢ closedBall (0 : E2) 1 ∧
      Phi.symm '' (J ×ˢ closedBall (0 : E2) 1) =
        J ×ˢ closedBall (0 : E2) 1) :
    ∃ K : OpenPartialHomeomorph E3 E3,
      (∀ x : E2, ∀ z : ℝ, (z, x) ∈ Phi.source →
        K ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((Phi (z, x)).2, z)) ∧
      (∀ x : E2, ∀ z : ℝ, (z, x) ∈ Phi.target →
        K.symm ((heightPlaneCoordinates u).symm (x, z)) =
          (heightPlaneCoordinates u).symm ((Phi.symm (z, x)).2, z)) ∧
      ContDiffOn ℝ ∞ K K.source ∧
      ContDiffOn ℝ ∞ K.symm K.target ∧
      (∀ J : Set ℝ,
        K '' ((heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ J)) =
          (heightPlaneCoordinates u).symm ''
            (closedBall (0 : E2) 1 ×ˢ J) ∧
        K.symm '' ((heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ J)) =
          (heightPlaneCoordinates u).symm ''
            (closedBall (0 : E2) 1 ×ˢ J)) := by
  obtain ⟨K, hK, hKi, hKs, hKsi⟩ :=
    exists_nonnested_partial_physical_transport u Phi hPhi hPhii hheight hheighti
  have hforward (J : Set ℝ) :
      K '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ J)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ J) := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases p with ⟨x, z⟩
      rcases hp with ⟨hx, hz⟩
      have hpPhi : (z, x) ∈ Phi.source := hsource J ⟨hz, hx⟩
      have hout : Phi (z, x) ∈ J ×ˢ closedBall (0 : E2) 1 := by
        rw [← (hprod J).1]
        exact ⟨(z, x), ⟨hz, hx⟩, rfl⟩
      refine ⟨((Phi (z, x)).2, (Phi (z, x)).1),
        ⟨hout.2, hout.1⟩, ?_⟩
      have hz' := (hheight (z, x) hpPhi)
      simpa only [hz'] using (hK x z hpPhi).symm
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨x, z⟩
      rcases hp with ⟨hx, hz⟩
      have hpPhi : (z, x) ∈ Phi.target := htarget J ⟨hz, hx⟩
      have hin : Phi.symm (z, x) ∈ J ×ˢ closedBall (0 : E2) 1 := by
        rw [← (hprod J).2]
        exact ⟨(z, x), ⟨hz, hx⟩, rfl⟩
      have hpre : (Phi.symm (z, x)).1 = z := by
        exact hheighti (z, x) hpPhi
      have hsrc : Phi.symm (z, x) ∈ Phi.source := Phi.map_target hpPhi
      have hpair : Phi.symm (z, x) =
          (z, (Phi.symm (z, x)).2) := Prod.ext hpre rfl
      have hcomp : Phi (z, (Phi.symm (z, x)).2) = (z, x) := by
        rw [← hpair]
        exact Phi.right_inv hpPhi
      have hsrc' : (z, (Phi.symm (z, x)).2) ∈ Phi.source := hpair ▸ hsrc
      refine ⟨(heightPlaneCoordinates u).symm
          ((Phi.symm (z, x)).2, z), ?_, ?_⟩
      · refine ⟨((Phi.symm (z, x)).2, z),
          ⟨hin.2, hpre ▸ hin.1⟩, rfl⟩
      rw [hK _ _ hsrc', hcomp]
  have hinverse (J : Set ℝ) :
      K.symm '' ((heightPlaneCoordinates u).symm ''
        (closedBall (0 : E2) 1 ×ˢ J)) =
        (heightPlaneCoordinates u).symm ''
          (closedBall (0 : E2) 1 ×ˢ J) := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases p with ⟨x, z⟩
      rcases hp with ⟨hx, hz⟩
      have hpPhi : (z, x) ∈ Phi.target := htarget J ⟨hz, hx⟩
      have hout : Phi.symm (z, x) ∈ J ×ˢ closedBall (0 : E2) 1 := by
        rw [← (hprod J).2]
        exact ⟨(z, x), ⟨hz, hx⟩, rfl⟩
      have hz' := hheighti (z, x) hpPhi
      have hz'' : (Phi.symm (z, x)).1 = z := by simpa using hz'
      refine ⟨((Phi.symm (z, x)).2, z),
          ⟨hout.2, hz'' ▸ hout.1⟩, ?_⟩
      exact (hKi x z hpPhi).symm
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨x, z⟩
      rcases hp with ⟨hx, hz⟩
      have hpPhi : (z, x) ∈ Phi.source := hsource J ⟨hz, hx⟩
      have hin : Phi (z, x) ∈ J ×ˢ closedBall (0 : E2) 1 := by
        rw [← (hprod J).1]
        exact ⟨(z, x), ⟨hz, hx⟩, rfl⟩
      have hpre : (Phi (z, x)).1 = z := hheight (z, x) hpPhi
      have htgt : Phi (z, x) ∈ Phi.target := Phi.map_source hpPhi
      have hpair : Phi (z, x) = (z, (Phi (z, x)).2) := Prod.ext hpre rfl
      have hcomp : Phi.symm (z, (Phi (z, x)).2) = (z, x) := by
        rw [← hpair]
        exact Phi.left_inv hpPhi
      have htgt' : (z, (Phi (z, x)).2) ∈ Phi.target := hpair ▸ htgt
      refine ⟨(heightPlaneCoordinates u).symm
          ((Phi (z, x)).2, z), ?_, ?_⟩
      · refine ⟨((Phi (z, x)).2, z),
          ⟨hin.2, hpre ▸ hin.1⟩, rfl⟩
      rw [hKi _ _ htgt', hcomp]
  exact ⟨K, hK, hKi, hKs, hKsi, fun J => ⟨hforward J, hinverse J⟩⟩

end PoincareConjecture.M25.Topology3D
