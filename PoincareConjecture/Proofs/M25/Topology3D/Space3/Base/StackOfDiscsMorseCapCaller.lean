import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseGraph
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseNormalization

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackMorseCanonicalCapNormalization
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (A : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hA : ContDiffOn ℝ ∞ A A.source)
    (hAi : ContDiffOn ℝ ∞ A.symm A.target)
    (c kappa rho lambda : ℝ) (hkappa : |kappa| = 1)
    (hrho : 0 < rho) (hlambda : 0 < lambda)
    (hsmall : lambda < rho ^ 2 / 2)
    (hsource : closedBall (0 : E2) (2 * rho) ×ˢ
      Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ A.source)
    (hheight : ∀ p ∈ A.source, ⟪(u : E3), A p⟫_ℝ = p.2)
    (hgraph : ∀ p ∈ A.source,
      A p ∈ range (fun q : UnitTwoSphere => psi (q, 0)) ↔
        p.2 = c + kappa * ‖p.1‖ ^ 2)
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let Qminus : Set UnitTwoSphere :=
      {q | (heightCoordinates (q : E3)).2 ≤ 0}
    let distance : UnitTwoSphere → ℝ := fun q =>
      rho ^ 2 + lambda * (M (heightCoordinates (q : E3))).2
    let horizontal : UnitTwoSphere → E2 := fun q =>
      Real.sqrt (distance q) • (M (heightCoordinates (q : E3))).1
    let endpoint : UnitTwoSphere → E3 := fun q =>
      A (horizontal q, c + kappa * distance q)
    let original : E2 → E3 := fun x => A (x, c + kappa * ‖x‖ ^ 2)
    let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
    let disc : Set E3 := original '' closedBall (0 : E2) rho
    let discOpen : Set E3 := original '' ball (0 : E2) rho
    let seam : Set E3 := original '' sphere (0 : E2) rho
    let rest : Set E3 := S \ discOpen
    let cap : Set E3 := endpoint '' Qminus
    let s : ℝ := c + kappa * rho ^ 2
    let zflat : ℝ := c + kappa * (rho ^ 2 - lambda)
    let flatMap : E2 → E3 := fun x =>
      A (Real.sqrt (rho ^ 2 - lambda) • x, zflat)
    let Flat : Set E3 := flatMap '' closedBall (0 : E2) rFlat
    ∃ r0 : ℝ, 0 < r0 ∧ r0 < rho ∧
      ∃ Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
        ∃ C N : Set E3,
          (∀ x ∈ closedBall (0 : E2) rho,
            (x, c + kappa * ‖x‖ ^ 2) ∈ A.source) ∧
          horizontal '' Qminus = closedBall (0 : E2) rho ∧
          (∀ q ∈ Qminus,
            rho ^ 2 - lambda ≤ distance q ∧ distance q ≤ rho ^ 2 ∧
            0 < distance q ∧ horizontal q ∈ closedBall (0 : E2) rho ∧
            (horizontal q, c + kappa * distance q) ∈ A.source ∧
            endpoint q ∈ A.target ∧
            A.symm (endpoint q) = (horizontal q, c + kappa * distance q) ∧
            ⟪(u : E3), endpoint q⟫_ℝ = c + kappa * distance q) ∧
          ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) ∧
          ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) ∧
          (∀ y, Phi 0 y = y) ∧
          (∀ q ∈ Qminus, ∀ t ∈ Icc (0 : ℝ) 1,
            (horizontal q, c + kappa *
              ((1 - t) * ‖horizontal q‖ ^ 2 + t * distance q)) ∈ A.source ∧
            Phi t (original (horizontal q)) =
              A (horizontal q, c + kappa *
                ((1 - t) * ‖horizontal q‖ ^ 2 + t * distance q))) ∧
          IsCompact C ∧
          C ⊆ A '' (closedBall (0 : E2) r0 ×ˢ
            Ioo (c - 4 * rho ^ 2) (c + 4 * rho ^ 2)) ∧
          (∀ t, tsupport (fun y => Phi t y - y) ⊆ C) ∧
          (∀ t, tsupport (fun y => (Phi t).symm y - y) ⊆ C) ∧
          IsOpen N ∧ rest ⊆ N ∧ Disjoint N C ∧
          (∀ t y, y ∈ N → Phi t y = y ∧ (Phi t).symm y = y) ∧
          disc ⊆ S ∧ disc \ discOpen = seam ∧
          Phi 1 '' disc = cap ∧ (Phi 1).symm '' cap = disc ∧
          rest ∩ cap = seam ∧ Phi 1 '' S = rest ∪ cap ∧
          (∀ y ∈ cap,
            -lambda ≤ kappa * (⟪(u : E3), y⟫_ℝ - s) ∧
            kappa * (⟪(u : E3), y⟫_ℝ - s) ≤ 0) ∧
          (∀ x ∈ closedBall (0 : E2) rFlat,
            (Real.sqrt (rho ^ 2 - lambda) • x, zflat) ∈ A.source ∧
            endpoint (southSpherePoint x) = flatMap x) ∧
          Flat ⊆ cap := by
  classical
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let Qminus : Set UnitTwoSphere := {q | (heightCoordinates (q : E3)).2 ≤ 0}
  let distance : UnitTwoSphere → ℝ := fun q =>
    rho ^ 2 + lambda * (M (heightCoordinates (q : E3))).2
  let horizontal : UnitTwoSphere → E2 := fun q =>
    Real.sqrt (distance q) • (M (heightCoordinates (q : E3))).1
  let endpoint : UnitTwoSphere → E3 := fun q =>
    A (horizontal q, c + kappa * distance q)
  let original : E2 → E3 := fun x => A (x, c + kappa * ‖x‖ ^ 2)
  let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
  let disc := original '' closedBall (0 : E2) rho
  let discOpen := original '' ball (0 : E2) rho
  let seam := original '' sphere (0 : E2) rho
  let rest := S \ discOpen
  let cap := endpoint '' Qminus
  let s := c + kappa * rho ^ 2
  let zflat := c + kappa * (rho ^ 2 - lambda)
  let flatMap : E2 → E3 := fun x => A (Real.sqrt (rho ^ 2 - lambda) • x, zflat)
  let Flat := flatMap '' closedBall (0 : E2) rFlat
  let q0 : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
  let h : E2 → ℝ := fun x => rho ^ 2 + lambda * (M (heightCoordinates (q0 x : E3))).2
  obtain ⟨e, _he, _hKe, _heU, _hes, _heis, htarget, _himage,
    hgs, _hgpos, _hgf, hcapGraph, hbounds, _hflat, eps, heps, hepsrho,
    _hannulus, hseamGraph⟩ :=
    exists_stackMorseCap_graph rFlat rOne v0 v1 rho lambda
      hrFlat hradii hrOne hv0 hv01 hv1 hgap hrho hlambda hsmall
  let g : E2 → ℝ := fun y => h (e.symm y)
  change ContDiffOn ℝ ∞ g e.target at hgs
  change (fun q : UnitTwoSphere => (horizontal q, distance q)) '' Qminus =
    (fun y : E2 => (y, g y)) '' closedBall (0 : E2) rho at hcapGraph
  change ∀ y ∈ closedBall (0 : E2) rho,
    rho ^ 2 - lambda ≤ g y ∧ g y ≤ rho ^ 2 ∧ ‖y‖ ^ 2 ≤ g y at hbounds
  change ∀ y : E2, |‖y‖ - rho| < eps → g y = ‖y‖ ^ 2 at hseamGraph
  have hnative (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      horizontal q ∈ closedBall (0 : E2) rho ∧ g (horizontal q) = distance q := by
    have hm := hcapGraph ▸ mem_image_of_mem
      (fun p : UnitTwoSphere => (horizontal p, distance p)) hq
    obtain ⟨y, hy, heq⟩ := hm
    have he1 : y = horizontal q := congrArg Prod.fst heq
    have he2 : g y = distance q := congrArg Prod.snd heq
    exact ⟨he1 ▸ hy, he1 ▸ he2⟩
  have hhorizontal : horizontal '' Qminus = closedBall (0 : E2) rho := by
    apply subset_antisymm
    · rintro _ ⟨q, hq, rfl⟩
      exact (hnative q hq).1
    · intro y hy
      have hm := hcapGraph.symm ▸ mem_image_of_mem (fun x : E2 => (x, g x)) hy
      obtain ⟨q, hq, heq⟩ := hm
      exact ⟨q, hq, congrArg Prod.fst heq⟩
  let r0 := rho - eps / 2
  have hr0 : 0 < r0 := by dsimp [r0]; linarith only [hepsrho, hrho]
  have hr0rho : r0 < rho := by dsimp [r0]; linarith only [heps]
  have hbound (x : E2) (hx : x ∈ closedBall (0 : E2) rho) :
      ‖x‖ ^ 2 ≤ g x ∧ g x ≤ rho ^ 2 := ⟨(hbounds x hx).2.2, (hbounds x hx).2.1⟩
  have hseam (x : E2) (hx : x ∈ closedBall (0 : E2) rho) (hx0 : r0 ≤ ‖x‖) :
      g x = ‖x‖ ^ 2 := by
    apply hseamGraph
    have hn := mem_closedBall_zero_iff.mp hx
    rw [abs_of_nonpos (sub_nonpos.mpr hn)]
    dsimp only [r0] at hx0
    linarith only [hx0, heps]
  obtain ⟨Phi, C, N, hPhi, hPhii, hPhi0, htrack, hC, hCsub, hs, hsi,
    hN, hrestN, hNC, hfix, hdiscS, hboundary, hdiscImage, hcapInverse,
    hcross, hsurface⟩ :=
    exists_stackMorseGraphNormalization A hA hAi c kappa rho r0 hkappa hr0 hr0rho
      hsource S hgraph g e.target e.open_target htarget hgs hbound hseam
  let graphCap := (fun x : E2 => A (x, c + kappa * g x)) '' closedBall (0 : E2) rho
  have hcap : graphCap = cap := by
    have heq := congrArg
      (fun V : Set (E2 × ℝ) => (fun p : E2 × ℝ => A (p.1, c + kappa * p.2)) '' V)
      hcapGraph
    simpa only [image_image, Function.comp_def, graphCap, cap, endpoint] using heq.symm
  change Phi 1 '' disc = graphCap at hdiscImage
  change (Phi 1).symm '' graphCap = disc at hcapInverse
  change rest ∩ graphCap = seam at hcross
  change Phi 1 '' S = rest ∪ graphCap at hsurface
  rw [hcap] at hdiscImage hcapInverse hcross hsurface
  have hrad : 0 < rho ^ 2 - lambda := by nlinarith only [hsmall, sq_pos_of_pos hrho]
  have hkap2 : kappa ^ 2 = 1 := by nlinarith only [sq_abs kappa, hkappa]
  have hcoordinate (x : E2) (hx : ‖x‖ ≤ rho)
      (v : ℝ) (hv0 : 0 ≤ v) (hvrho : v ≤ rho ^ 2) :
      (x, c + kappa * v) ∈ A.source := by
    have habs : |kappa * v| ≤ rho ^ 2 := by
      rw [abs_mul, hkappa, one_mul, abs_of_nonneg hv0]
      exact hvrho
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    apply hsource
    refine ⟨mem_closedBall_zero_iff.mpr (by linarith only [hx, hrho]), ?_, ?_⟩
    · linarith only [hl, sq_nonneg rho]
    · linarith only [hu, sq_nonneg rho]
  have horiginal (x : E2) (hx : x ∈ closedBall (0 : E2) rho) :
      (x, c + kappa * ‖x‖ ^ 2) ∈ A.source :=
    hcoordinate x (mem_closedBall_zero_iff.mp hx) (‖x‖ ^ 2) (sq_nonneg _)
      ((sq_le_sq₀ (norm_nonneg x) hrho.le).mpr (mem_closedBall_zero_iff.mp hx))
  have hpoints (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      rho ^ 2 - lambda ≤ distance q ∧ distance q ≤ rho ^ 2 ∧
      0 < distance q ∧ horizontal q ∈ closedBall (0 : E2) rho ∧
      (horizontal q, c + kappa * distance q) ∈ A.source ∧
      endpoint q ∈ A.target ∧
      A.symm (endpoint q) = (horizontal q, c + kappa * distance q) ∧
      ⟪(u : E3), endpoint q⟫_ℝ = c + kappa * distance q := by
    obtain ⟨hqball, hqg⟩ := hnative q hq
    have hb := hbounds (horizontal q) hqball
    rw [hqg] at hb
    have hpos := hrad.trans_le hb.1
    have hsrc := hcoordinate (horizontal q) (mem_closedBall_zero_iff.mp hqball)
      (distance q) hpos.le hb.2.1
    exact ⟨hb.1, hb.2.1, hpos, hqball, hsrc, A.map_source hsrc,
      A.left_inv hsrc, hheight _ hsrc⟩
  have htracks (q : UnitTwoSphere) (hq : q ∈ Qminus)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (horizontal q, c + kappa *
        ((1 - t) * ‖horizontal q‖ ^ 2 + t * distance q)) ∈ A.source ∧
      Phi t (original (horizontal q)) = A (horizontal q, c + kappa *
        ((1 - t) * ‖horizontal q‖ ^ 2 + t * distance q)) := by
    obtain ⟨_, hu, hp, hx, _⟩ := hpoints q hq
    have hn := mem_closedBall_zero_iff.mp hx
    have hn2 := (sq_le_sq₀ (norm_nonneg (horizontal q)) hrho.le).mpr hn
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hv0 : 0 ≤ (1 - t) * ‖horizontal q‖ ^ 2 + t * distance q :=
      add_nonneg (mul_nonneg ht1 (sq_nonneg _)) (mul_nonneg ht.1 hp.le)
    have hv1 : (1 - t) * ‖horizontal q‖ ^ 2 + t * distance q ≤ rho ^ 2 := by
      calc
        _ ≤ (1 - t) * rho ^ 2 + t * rho ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hn2 ht1)
            (mul_le_mul_of_nonneg_left hu ht.1)
        _ = rho ^ 2 := by ring
    refine ⟨hcoordinate (horizontal q) hn _ hv0 hv1, ?_⟩
    simpa only [(hnative q hq).2] using htrack (horizontal q) hx t ht
  have hsigned (y : E3) (hy : y ∈ cap) :
      -lambda ≤ kappa * (⟪(u : E3), y⟫_ℝ - s) ∧
      kappa * (⟪(u : E3), y⟫_ℝ - s) ≤ 0 := by
    obtain ⟨q, hq, rfl⟩ := hy
    obtain ⟨hl, hu, _, _, _, _, _, hh⟩ := hpoints q hq
    have heq : kappa * (⟪(u : E3), endpoint q⟫_ℝ - s) = distance q - rho ^ 2 := by
      rw [hh]
      calc
        _ = kappa ^ 2 * (distance q - rho ^ 2) := by dsimp only [s]; ring
        _ = distance q - rho ^ 2 := by rw [hkap2, one_mul]
    rw [heq]
    constructor <;> linarith only [hl, hu]
  obtain ⟨hflatModel, _⟩ := stackCanonicalModel_flat_disc rFlat rOne v0 v1
    hrFlat hradii hrOne hv0 hv01 hv1 hgap
  change ∀ x : E2, ‖x‖ ≤ rFlat →
    M (heightCoordinates (southSpherePoint x : E3)) = (x, -1) at hflatModel
  have hflatq (x : E2) (hx : x ∈ closedBall (0 : E2) rFlat) :
      southSpherePoint x ∈ Qminus := by
    change (heightCoordinates (southSpherePoint x : E3)).2 ≤ 0
    rw [southSpherePoint_coordinates x
      ((mem_closedBall_zero_iff.mp hx).trans_lt (hradii.trans hrOne))]
    exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  have hflat (x : E2) (hx : x ∈ closedBall (0 : E2) rFlat) :
      (Real.sqrt (rho ^ 2 - lambda) • x, zflat) ∈ A.source ∧
      endpoint (southSpherePoint x) = flatMap x := by
    have hm := hflatModel x (mem_closedBall_zero_iff.mp hx)
    have hd : distance (southSpherePoint x) = rho ^ 2 - lambda := by
      dsimp only [distance]
      rw [hm]
      simp only [mul_neg_one, sub_eq_add_neg]
    have hh : horizontal (southSpherePoint x) = Real.sqrt (rho ^ 2 - lambda) • x := by
      dsimp only [horizontal]
      rw [hd, hm]
    have hs := (hpoints (southSpherePoint x) (hflatq x hx)).2.2.2.2.1
    refine ⟨?_, ?_⟩
    · simpa only [hd, hh, zflat] using hs
    · change A (horizontal (southSpherePoint x),
        c + kappa * distance (southSpherePoint x)) = flatMap x
      rw [hh, hd]
  have hFlat : Flat ⊆ cap := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨southSpherePoint x, hflatq x hx, (hflat x hx).2⟩
  exact ⟨r0, hr0, hr0rho, Phi, C, N, horiginal, hhorizontal, hpoints,
    hPhi, hPhii, hPhi0, htracks, hC, hCsub, hs, hsi, hN, hrestN, hNC, hfix,
    hdiscS, hboundary, hdiscImage, hcapInverse, hcross, hsurface, hsigned, hflat, hFlat⟩

end PoincareConjecture.M25.Topology3D
