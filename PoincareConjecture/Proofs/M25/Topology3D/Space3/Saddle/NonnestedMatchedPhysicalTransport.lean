import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightPreservingSlice












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞





theorem exists_nonnested_matched_physical_transport
    (u : UnitTwoSphere)
    (Phi : Diffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) P P ∞)
    (S : Set P) (hS : IsCompact S)
    (hheight : ∀ p : P,
      (Phi p).1 = p.1 ∧ (Phi.symm p).1 = p.1)
    (hfix : ∀ p : P, p ∉ S → Phi p = p ∧ Phi.symm p = p)
    (hprod : ∀ J : Set ℝ,
      Phi '' (J ×ˢ closedBall (0 : E2) 1) = J ×ˢ closedBall 0 1 ∧
      Phi.symm '' (J ×ˢ closedBall (0 : E2) 1) = J ×ˢ closedBall 0 1) :
    let L := heightPlaneCoordinates u
    let SW : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, P) (E2 × ℝ) P ∞ :=
      (ContinuousLinearEquiv.prodComm ℝ E2 ℝ).toDiffeomorph
    let Kset : Set E3 := L.symm '' (SW.symm '' S)
    ∃ K : D3,
      (∀ x : E2, ∀ z : ℝ,
        K (L.symm (x, z)) =
          L.symm ((Phi (z, x)).2, z) ∧
        K.symm (L.symm (x, z)) =
          L.symm ((Phi.symm (z, x)).2, z)) ∧
      IsCompact Kset ∧
      tsupport (fun y : E3 => K y - y) ⊆ Kset ∧
      tsupport (fun y : E3 => K.symm y - y) ⊆ Kset ∧
      (∀ J : Set ℝ,
        K '' (L.symm '' (closedBall (0 : E2) 1 ×ˢ J)) =
          L.symm '' (closedBall (0 : E2) 1 ×ˢ J) ∧
        K.symm '' (L.symm '' (closedBall (0 : E2) 1 ×ˢ J)) =
          L.symm '' (closedBall (0 : E2) 1 ×ˢ J)) := by
  dsimp only
  let L := heightPlaneCoordinates u
  let SW : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, P) (E2 × ℝ) P ∞ :=
    (ContinuousLinearEquiv.prodComm ℝ E2 ℝ).toDiffeomorph
  let Kset : Set E3 := L.symm '' (SW.symm '' S)
  let K : D3 :=
    (((L.toDiffeomorph.trans SW).trans Phi).trans SW.symm).trans
      L.symm.toDiffeomorph
  have hformula (x : E2) (z : ℝ) :
      K (L.symm (x, z)) = L.symm ((Phi (z, x)).2, z) ∧
      K.symm (L.symm (x, z)) = L.symm ((Phi.symm (z, x)).2, z) := by
    constructor
    · change L.symm (SW.symm (Phi (SW (L (L.symm (x, z)))))) = _
      rw [L.apply_symm_apply]
      change L.symm ((Phi (z, x)).2, (Phi (z, x)).1) = _
      rw [(hheight (z, x)).1]
    · change L.symm (SW.symm (Phi.symm (SW (L (L.symm (x, z)))))) = _
      rw [L.apply_symm_apply]
      change L.symm ((Phi.symm (z, x)).2, (Phi.symm (z, x)).1) = _
      rw [(hheight (z, x)).2]
  have hKc : IsCompact Kset := by
    change IsCompact (L.symm '' (SW.symm '' S))
    rw [image_image]
    exact hS.image (L.symm.continuous.comp SW.symm.continuous)
  have hboth (y : E3) (hy : y ∉ Kset) : K y = y ∧ K.symm y = y := by
    let x : E2 := (L y).1
    let z : ℝ := (L y).2
    have hcoord : L.symm (x, z) = y := L.symm_apply_apply y
    have hp : (z, x) ∉ S := by
      intro hpx
      exact hy ⟨(x, z), ⟨(z, x), hpx, rfl⟩, hcoord⟩
    have hf : K (L.symm (x, z)) = L.symm (x, z) := by
      rw [(hformula x z).1, (hfix (z, x) hp).1]
    have hi : K.symm (L.symm (x, z)) = L.symm (x, z) := by
      rw [(hformula x z).2, (hfix (z, x) hp).2]
    rw [hcoord] at hf hi
    exact ⟨hf, hi⟩
  have hforward (J : Set ℝ) :
      K '' (L.symm '' (closedBall (0 : E2) 1 ×ˢ J)) =
        L.symm '' (closedBall (0 : E2) 1 ×ˢ J) := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases p with ⟨x, z⟩
      rcases hp with ⟨hx, hz⟩
      change x ∈ closedBall (0 : E2) 1 at hx
      change z ∈ J at hz
      have hout : Phi (z, x) ∈ J ×ˢ closedBall (0 : E2) 1 := by
        rw [← hprod J |>.1]
        exact ⟨(z, x), ⟨hz, hx⟩, rfl⟩
      have hz : z ∈ J := by simpa only [(hheight (z, x)).1] using hout.1
      refine ⟨((Phi (z, x)).2, z), ⟨?_, hz⟩, (hformula x z).1.symm⟩
      exact hout.2
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨x, z⟩
      rcases hp with ⟨hx, hz⟩
      change x ∈ closedBall (0 : E2) 1 at hx
      change z ∈ J at hz
      have hin : Phi.symm (z, x) ∈ J ×ˢ closedBall (0 : E2) 1 := by
        rw [← hprod J |>.2]
        exact ⟨(z, x), ⟨hz, hx⟩, rfl⟩
      have hzpre : (Phi.symm (z, x)).1 = z := by
        have hh := (hheight (Phi.symm (z, x))).1
        rw [Phi.apply_symm_apply] at hh
        exact hh.symm
      have hpre : Phi.symm (z, x) = (z, (Phi.symm (z, x)).2) :=
        Prod.ext hzpre rfl
      have hcomp : Phi (z, (Phi.symm (z, x)).2) = (z, x) := by
        rw [← hpre, Phi.apply_symm_apply]
      refine ⟨L.symm ((Phi.symm (z, x)).2, z),
        ⟨((Phi.symm (z, x)).2, z), ⟨hin.2, ?_⟩, rfl⟩, ?_⟩
      · exact hzpre ▸ hin.1
      · rw [(hformula ((Phi.symm (z, x)).2) z).1, hcomp]
  have hinverse (J : Set ℝ) :
      K.symm '' (L.symm '' (closedBall (0 : E2) 1 ×ˢ J)) =
        L.symm '' (closedBall (0 : E2) 1 ×ˢ J) := by
    ext y
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      rcases p with ⟨x, z⟩
      rcases hp with ⟨hx, hz⟩
      change x ∈ closedBall (0 : E2) 1 at hx
      change z ∈ J at hz
      have hout : Phi.symm (z, x) ∈ J ×ˢ closedBall (0 : E2) 1 := by
        rw [← hprod J |>.2]
        exact ⟨(z, x), ⟨hz, hx⟩, rfl⟩
      have hz : z ∈ J := by
        have hh := (hheight (Phi.symm (z, x))).1
        rw [Phi.apply_symm_apply] at hh
        have hfirst := hout.1
        rw [← hh] at hfirst
        exact hfirst
      refine ⟨((Phi.symm (z, x)).2, z), ⟨hout.2, hz⟩,
        (hformula x z).2.symm⟩
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨x, z⟩
      rcases hp with ⟨hx, hz⟩
      change x ∈ closedBall (0 : E2) 1 at hx
      change z ∈ J at hz
      have hin : Phi (z, x) ∈ J ×ˢ closedBall (0 : E2) 1 := by
        rw [← hprod J |>.1]
        exact ⟨(z, x), ⟨hz, hx⟩, rfl⟩
      have hzpre : (Phi (z, x)).1 = z := (hheight (z, x)).1
      have hpre : Phi (z, x) = (z, (Phi (z, x)).2) :=
        Prod.ext hzpre rfl
      have hcomp : Phi.symm (z, (Phi (z, x)).2) = (z, x) := by
        rw [← hpre, Phi.symm_apply_apply]
      refine ⟨L.symm ((Phi (z, x)).2, z),
        ⟨((Phi (z, x)).2, z), ⟨hin.2, ?_⟩, rfl⟩, ?_⟩
      · exact hzpre ▸ hin.1
      · rw [(hformula ((Phi (z, x)).2) z).2, hcomp]
  refine ⟨K, hformula, hKc, ?_, ?_, ?_⟩
  · apply closure_minimal ?_ hKc.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hboth y hyK).1)
  · apply closure_minimal ?_ hKc.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hboth y hyK).2)
  · intro J
    exact ⟨hforward J, hinverse J⟩

end PoincareConjecture.M25.Topology3D
