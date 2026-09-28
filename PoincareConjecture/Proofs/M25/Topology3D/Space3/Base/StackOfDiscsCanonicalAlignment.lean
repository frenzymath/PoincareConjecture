import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsRadialization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsRadialCap
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsSupportedCap

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackCanonicalCapAlignment
    (E U V : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hE : ContDiffOn ℝ ∞ E E.source) (hEi : ContDiffOn ℝ ∞ E.symm E.target)
    (hU : ContDiffOn ℝ ∞ U U.source) (hUi : ContDiffOn ℝ ∞ U.symm U.target)
    (hV : ContDiffOn ℝ ∞ V V.source) (hVi : ContDiffOn ℝ ∞ V.symm V.target)
    (hEh : ∀ p ∈ E.source, (E p).1 = p.1)
    (hUh : ∀ p ∈ U.source, (U p).1 = p.1)
    (hVh : ∀ p ∈ V.source, (V p).1 = p.1)
    (hEs : univ ×ˢ closedBall (0 : E2) 1 ⊆ E.source)
    (hEt : univ ×ˢ closedBall (0 : E2) 1 ⊆ E.target)
    (hEproduct : ∀ J : Set ℝ, ∀ Z : Set E2,
      (Z = ball 0 1 ∨ Z = closedBall 0 1 ∨ Z = sphere 0 1) →
      E '' (J ×ˢ Z) = J ×ˢ Z ∧ E.symm '' (J ×ˢ Z) = J ×ˢ Z)
    (L A a b B R : ℝ)
    (hLA : L < A) (hAa : A < a) (hab : a < b) (hbB : b < B) (hBR : B < R)
    (hUs : Icc A B ×ˢ closedBall (0 : E2) 1 ⊆ U.source)
    (hVs : Icc A B ×ˢ closedBall (0 : E2) 1 ⊆ V.source)
    (htransition : ∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1,
      U (E (z, q)) = V (z, q))
    (O : Set (ℝ × E2)) (hO : IsOpen O)
    (hcircleO : V '' (Icc A B ×ˢ sphere (0 : E2) 1) ⊆ O) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 / 4 ∧
      ∃ Psi : ℝ → Diffeomorph 𝓘(ℝ, ℝ × E2) 𝓘(ℝ, ℝ × E2)
        (ℝ × E2) (ℝ × E2) ∞,
      ∃ K : Set (ℝ × E2),
        IsCompact K ∧ K ⊆ O ∧ K ⊆ Ioo A B ×ˢ (univ : Set E2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × E2) => Psi p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × E2) => (Psi p.1).symm p.2) ∧
        (∀ p, Psi 0 p = p) ∧
        (∀ t, tsupport (fun p => Psi t p - p) ⊆ K ∧
          tsupport (fun p => (Psi t).symm p - p) ⊆ K) ∧
        (∀ t p, p ∉ K → Psi t p = p ∧ (Psi t).symm p = p) ∧
        (∀ t p, (Psi t p).1 = p.1 ∧ ((Psi t).symm p).1 = p.1) ∧
        (∀ t z, z ∈ Icc A B → ∀ q ∈ sphere (0 : E2) 1,
          Psi t (V (z, q)) = V (z, q) ∧ (Psi t).symm (V (z, q)) = V (z, q)) ∧
        ∀ s sigma lambda gamma rFlat rOne v0 v1 : ℝ,
          |sigma| = 1 → 0 < lambda → lambda < gamma →
          a ≤ s - gamma → s + gamma ≤ b →
          0 < rFlat → 1 - delta < rFlat → rFlat < rOne → rOne < 1 →
          0 < v0 → v0 < v1 → v1 < 1 → v1 ^ 2 + rOne ^ 2 < 1 →
          let ah := stackCanonicalHorizontal v0 v1
          let bv := stackCanonicalVertical rFlat rOne
          let M := stackCapProfilePath ah ah bv bv 0
          let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          let Y := (fun q : UnitTwoSphere =>
            (s + sigma * lambda * (M (heightCoordinates (q : E3))).2,
              (M (heightCoordinates (q : E3))).1)) '' Qminus
          Y ⊆ U.source ∧ Y ⊆ V.source ∧
            Psi 1 '' (U '' Y) = V '' Y ∧ (Psi 1).symm '' (V '' Y) = U '' Y := by
  have hEC : MapsTo E (univ ×ˢ sphere (0 : E2) 1)
      (univ ×ˢ sphere (0 : E2) 1) := by
    intro p hp
    rw [← (hEproduct univ (sphere 0 1) (Or.inr (Or.inr rfl))).1]
    exact mem_image_of_mem E hp
  have hEiC : MapsTo E.symm (univ ×ˢ sphere (0 : E2) 1)
      (univ ×ˢ sphere (0 : E2) 1) := by
    intro p hp
    rw [← (hEproduct univ (sphere 0 1) (Or.inr (Or.inr rfl))).2]
    exact mem_image_of_mem E.symm hp
  have hEiB : MapsTo E.symm (univ ×ˢ ball (0 : E2) 1)
      (univ ×ˢ ball (0 : E2) 1) := by
    intro p hp
    rw [← (hEproduct univ (ball 0 1) (Or.inl rfl)).2]
    exact mem_image_of_mem E.symm hp
  obtain ⟨dD, hdD, hdDq, Phi, _S, _hS, _hSband, _hPhiFix, _hPhiHeight,
      hPhiCircle, _hDsource, _hDtarget, hD, hDi, hDs, hDt, hDh, _hDih,
      hDproduct, hRadial⟩ :=
    exists_stackRadializedDiscChart E hE hEi hEh hEs hEt hEC hEiC hEiB
      L A B R hLA (hAa.trans (hab.trans hbB)) hBR
  let D := Phi.symm.toHomeomorph.toOpenPartialHomeomorph.trans E
  let C := D.trans U
  have hC : ContDiffOn ℝ ∞ C C.source :=
    hU.comp (hD.mono inter_subset_left) (fun _ hp => hp.2)
  have hCi : ContDiffOn ℝ ∞ C.symm C.target :=
    hDi.comp (hUi.mono inter_subset_left) (fun _ hp => hp.2)
  have hCh (p : ℝ × E2) (hp : p ∈ C.source) : (C p).1 = p.1 :=
    (hUh (D p) hp.2).trans (hDh p hp.1)
  have hCs : Icc A B ×ˢ closedBall (0 : E2) 1 ⊆ C.source := by
    intro p hp
    refine ⟨hDs ⟨mem_univ _, hp.2⟩, hUs ?_⟩
    have himage := (hEproduct (Icc A B) (closedBall 0 1) (Or.inr (Or.inl rfl))).1
    rw [← himage, ← (hDproduct (Icc A B)).2]
    exact mem_image_of_mem D hp
  have hboundary (z : ℝ) (hz : z ∈ Icc A B) (q : E2)
      (hq : q ∈ sphere (0 : E2) 1) : C (z, q) = V (z, q) := by
    change U (E (Phi.symm (z, q))) = V (z, q)
    rw [(hPhiCircle z q hq).2]
    exact htransition z hz q hq
  let W := C.source ∩ C ⁻¹' O
  have hW : IsOpen W := C.isOpen_inter_preimage hO
  have hCW : Icc A B ×ˢ sphere (0 : E2) 1 ⊆ W := by
    intro p hp
    refine ⟨hCs ⟨hp.1, sphere_subset_closedBall hp.2⟩, ?_⟩
    change C (p.1, p.2) ∈ O
    rw [hboundary p.1 hp.1 p.2 hp.2]
    exact hcircleO (mem_image_of_mem V hp)
  obtain ⟨dM, hdM, _hdMq, Psi, K, hK, hKW, hKband, hPsi, hPsii, hPsi0,
      hSupport, hFix, hHeight, hCircle, hCaps⟩ :=
    exists_stackCanonicalCapIsotopy V C hV hVi hC hCi hVh hCh
      A a b B hAa hab hbB hVs hCs
      (fun z hz q hq => (hboundary z hz q hq).symm) W hW inter_subset_left hCW
  let delta := min dD dM
  have hd : 0 < delta := lt_min hdD hdM
  have hddD : delta ≤ dD := min_le_left _ _
  have hddM : delta ≤ dM := min_le_right _ _
  have hKO : K ⊆ O := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := hKW hy
    exact hp.2
  refine ⟨delta, hd, hddD.trans_lt hdDq, Psi, K, hK, hKO, hKband,
    hPsi, hPsii, hPsi0, hSupport, hFix, hHeight, ?_, ?_⟩
  · intro t z hz q hq
    rw [← hboundary z hz q hq]
    exact hCircle t z hz q hq
  · intro s sigma lambda gamma rFlat rOne v0 v1 hsigma hlambda hlg hleft hright
      hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
    have hinner : Icc (s - gamma) (s + gamma) ⊆ Icc A B :=
      fun _ hz => ⟨hAa.le.trans (hleft.trans hz.1), (hz.2.trans hright).trans hbB.le⟩
    have hrD : 1 - dD < rFlat := lt_of_le_of_lt (sub_le_sub_left hddD 1) hrann
    have hrM : 1 - dM < rFlat := lt_of_le_of_lt (sub_le_sub_left hddM 1) hrann
    have hnorm (z : ℝ) (hz : z ∈ Icc (s - gamma) (s + gamma)) (x : E2)
        (hx : |‖x‖ - 1| < dD) :
        ‖(D (z, x)).2‖ = ‖x‖ ∧ ‖(D.symm (z, x)).2‖ = ‖x‖ := by
      obtain ⟨_hxs, _hxt, hf, hi⟩ := hRadial z (hinner hz) x hx
      have hq : (z, (circleDirection x : E2)) ∈ univ ×ˢ sphere (0 : E2) 1 :=
        ⟨mem_univ z, (circleDirection x).2⟩
      have hn := mem_sphere_zero_iff_norm.mp (hEC hq).2
      have hni := mem_sphere_zero_iff_norm.mp (hEiC hq).2
      change ‖(D (z, x)).2‖ = ‖x‖ ∧ ‖(D.symm (z, x)).2‖ = ‖x‖
      rw [hf, hi]
      simp only [norm_smul, Real.norm_of_nonneg (norm_nonneg x), hn, hni, mul_one, and_self]
    obtain ⟨_hYD, _hYDi, hDY, _hDiY⟩ :=
      stackCanonicalCap_image_eq_of_radial_annulus D hD hDi hDh
        s sigma lambda gamma dD hsigma hlambda hlg hdD
        (fun _ hp => hDs ⟨mem_univ _, hp.2⟩)
        (fun _ hp => hDt ⟨mem_univ _, hp.2⟩) hnorm
        rFlat rOne v0 v1 hrFlat hrD hradii hrOne hv0 hv01 hv1 hgap
    obtain ⟨hYV, hYC, hf, hi⟩ :=
      hCaps s sigma lambda gamma rFlat rOne v0 v1 hsigma hlambda hlg hleft hright
        hrFlat hrM hradii hrOne hv0 hv01 hv1 hgap
    let ah := stackCanonicalHorizontal v0 v1
    let bv := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath ah ah bv bv 0
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let Y := (fun q : UnitTwoSphere =>
      (s + sigma * lambda * (M (heightCoordinates (q : E3))).2,
        (M (heightCoordinates (q : E3))).1)) '' Qminus
    change D '' Y = Y at hDY
    have hCY : C '' Y = U '' Y := by
      calc
        C '' Y = U '' (D '' Y) := (image_image U D Y).symm
        _ = U '' Y := congrArg (image U) hDY
    have hYU : Y ⊆ U.source := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := (show y ∈ D '' Y from hDY.symm ▸ hy)
      exact hxy ▸ (hYC hx).2
    change Psi 1 '' (C '' Y) = V '' Y at hf
    change (Psi 1).symm '' (V '' Y) = C '' Y at hi
    rw [hCY] at hf hi
    exact ⟨hYU, hYV, hf, hi⟩

end PoincareConjecture.M25.Topology3D
