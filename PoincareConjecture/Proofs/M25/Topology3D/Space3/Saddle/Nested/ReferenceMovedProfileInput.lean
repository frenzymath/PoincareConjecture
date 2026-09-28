import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem reference_moved_profile_input
    (P : SurgeryCapProfile)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (K : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (sigma s s' eps beta tau lambda lo hi : ℝ)
    (A N : BallNeighborhoodChart E3 E3) (E Z : Set E3)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hTs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hTh : ∀ p ∈ T.source, (heightCoordinates (T p)).2 = p.2)
    (hg : StrictMono g)
    (hKh : ∀ y : E3, (heightCoordinates (K y)).2 =
      g (heightCoordinates y).2)
    (hsigma : |sigma| = 1)
    (heps : 0 < eps) (hbeta : 0 < beta) (hbe : beta ≤ eps)
    (htau : 0 < tau) (hte : tau ≤ eps) (hlambda : 0 < lambda)
    (hsmall : lambda * P.heightBound < eps)
    (haff : ∀ r : ℝ, |r| ≤ eps → g (s + r) = s' + r)
    (hZ : IsClosed Z) :
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    let Qplus : Set UnitTwoSphere := {q | 0 ≤ H0 (q : E3)}
    let Qminus : Set UnitTwoSphere := {q | H0 (q : E3) ≤ 0}
    let cap0 : UnitTwoSphere → E3 := P.capMap T s sigma 0 lambda
    let north0 : Set E3 := cap0 '' Qplus
    let south0 : Set E3 := cap0 '' Qminus
    let rim0 : Set E3 := T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))
    (∀ q : UnitTwoSphere, N.chart (q : E3) = cap0 q) →
    N.chart.target = T.target →
    A.boundary = E ∪ north0 →
    N.boundary = south0 ∪ north0 →
    E ∩ north0 = rim0 →
    south0 ∩ north0 = rim0 →
    N.closedRegion ⊆ A.closedRegion →
    N.closedRegion ⊆ {y : E3 | |H0 y - s| < tau} →
    (∀ y ∈ A.closedRegion, lo ≤ H0 y ∧ H0 y ≤ hi) →
    (∀ q : UnitTwoSphere, -1 / 8 < H0 (q : E3) →
      N.chart (q : E3) ∈ A.boundary) →
    A.closedRegion ∩ Z ⊆ north0 →
    (∀ r ∈ Icc (0 : ℝ) beta,
      A.inside ∩ {y : E3 | H0 y = s - sigma * r} =
        T '' (ball (0 : E2) 1 ×ˢ ({s - sigma * r} : Set ℝ)) ∧
      A.closedRegion ∩ {y : E3 | H0 y = s - sigma * r} =
        T '' (closedBall (0 : E2) 1 ×ˢ ({s - sigma * r} : Set ℝ)) ∧
      A.boundary ∩ {y : E3 | H0 y = s - sigma * r} =
        T '' (sphere (0 : E2) 1 ×ˢ ({s - sigma * r} : Set ℝ))) →
    let T1 := heightTransportTube T g K
    let A1 := A.mapDiffeomorph K
    let N1 := N.mapDiffeomorph K
    let E1 : Set E3 := K '' E
    let Z1 : Set E3 := K '' Z
    let cap1 : UnitTwoSphere → E3 := P.capMap T1 s' sigma 0 lambda
    let north1 : Set E3 := cap1 '' Qplus
    let south1 : Set E3 := cap1 '' Qminus
    let rim1 : Set E3 := T1 '' (sphere (0 : E2) 1 ×ˢ ({s'} : Set ℝ))
    (∀ p : E2 × ℝ, T1 p = K (T (p.1, g.symm p.2))) ∧
    (∀ y : E3, T1.symm y =
      ((T.symm (K.symm y)).1, g (T.symm (K.symm y)).2)) ∧
    (∀ p : E2 × ℝ, p ∈ T1.source ↔ (p.1, g.symm p.2) ∈ T.source) ∧
    (∀ y : E3, y ∈ T1.target ↔ K.symm y ∈ T.target) ∧
    ContDiffOn ℝ ∞ T1 T1.source ∧
    ContDiffOn ℝ ∞ T1.symm T1.target ∧
    closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T1.source ∧
    (∀ p ∈ T1.source, H0 (T1 p) = p.2) ∧
    (∀ y ∈ T1.target, (T1.symm y).2 = H0 y) ∧
    A1.chart.source = A.chart.source ∧
    A1.chart.target = K '' A.chart.target ∧
    (∀ y : E3, A1.chart y = K (A.chart y)) ∧
    (∀ y : E3, A1.chart.symm y = A.chart.symm (K.symm y)) ∧
    A1.inside = K '' A.inside ∧
    A1.closedRegion = K '' A.closedRegion ∧
    A1.boundary = K '' A.boundary ∧
    N1.chart.source = N.chart.source ∧ N1.chart.target = T1.target ∧
    (∀ y : E3, N1.chart y = K (N.chart y)) ∧
    (∀ y : E3, N1.chart.symm y = N.chart.symm (K.symm y)) ∧
    N1.inside = K '' N.inside ∧ N1.closedRegion = K '' N.closedRegion ∧
    N1.boundary = K '' N.boundary ∧
    (∀ q : UnitTwoSphere, cap1 q = K (cap0 q) ∧
      N1.chart (q : E3) = cap1 q) ∧
    K '' north0 = north1 ∧ K.symm '' north1 = north0 ∧
    K '' south0 = south1 ∧ K.symm '' south1 = south0 ∧
    K '' rim0 = rim1 ∧ K.symm '' rim1 = rim0 ∧
    K.symm '' E1 = E ∧
    A1.boundary = E1 ∪ north1 ∧ N1.boundary = south1 ∪ north1 ∧
    E1 ∩ north1 = rim1 ∧ south1 ∩ north1 = rim1 ∧
    north1 = N1.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ H0 y} ∧
    N1.closedRegion ⊆ A1.closedRegion ∧
    N1.closedRegion ⊆ {y : E3 | |H0 y - s'| < tau} ∧
    (∀ y ∈ A1.closedRegion, g lo ≤ H0 y ∧ H0 y ≤ g hi) ∧
    (∀ q : UnitTwoSphere, -1 / 8 < H0 (q : E3) →
      N1.chart (q : E3) ∈ A1.boundary) ∧
    IsClosed Z1 ∧ A1.closedRegion ∩ Z1 ⊆ north1 ∧
    (∀ r ∈ Icc (0 : ℝ) beta,
      A1.inside ∩ {y : E3 | H0 y = s' - sigma * r} =
        T1 '' (ball (0 : E2) 1 ×ˢ ({s' - sigma * r} : Set ℝ)) ∧
      A1.closedRegion ∩ {y : E3 | H0 y = s' - sigma * r} =
        T1 '' (closedBall (0 : E2) 1 ×ˢ ({s' - sigma * r} : Set ℝ)) ∧
      A1.boundary ∩ {y : E3 | H0 y = s' - sigma * r} =
        T1 '' (sphere (0 : E2) 1 ×ˢ ({s' - sigma * r} : Set ℝ))) ∧
    (∀ (X : Set E2) (I : Set ℝ),
      K '' (T '' (X ×ˢ I)) = T1 '' (X ×ˢ (g '' I))) ∧
    (∀ a b : ℝ,
      K '' (T '' (sphere (0 : E2) 1 ×ˢ Icc a b)) =
        T1 '' (sphere (0 : E2) 1 ×ˢ Icc (g a) (g b))) ∧
    K '' (T '' (sphere (0 : E2) 1 ×ˢ Ici s)) =
      T1 '' (sphere (0 : E2) 1 ×ˢ Ici s') := by
  classical
  dsimp only
  let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
  let Qplus : Set UnitTwoSphere := {q | 0 ≤ H0 (q : E3)}
  let Qminus : Set UnitTwoSphere := {q | H0 (q : E3) ≤ 0}
  let cap0 : UnitTwoSphere → E3 := P.capMap T s sigma 0 lambda
  let north0 := cap0 '' Qplus
  let south0 := cap0 '' Qminus
  let rim0 := T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))
  intro hNc hNt hA hN hEr hNr hNA hNw hAw hpatch havoid hcuts
  change ∀ q : UnitTwoSphere, N.chart (q : E3) = cap0 q at hNc
  change A.boundary = E ∪ north0 at hA
  change N.boundary = south0 ∪ north0 at hN
  change E ∩ north0 = rim0 at hEr
  change south0 ∩ north0 = rim0 at hNr
  change N.closedRegion ⊆ {y : E3 | |H0 y - s| < tau} at hNw
  change ∀ y ∈ A.closedRegion, lo ≤ H0 y ∧ H0 y ≤ hi at hAw
  change ∀ q : UnitTwoSphere, -1 / 8 < H0 (q : E3) →
    N.chart (q : E3) ∈ A.boundary at hpatch
  change A.closedRegion ∩ Z ⊆ north0 at havoid
  change ∀ y : E3, H0 (K y) = g (H0 y) at hKh
  change ∀ p ∈ T.source, H0 (T p) = p.2 at hTh
  let T1 := heightTransportTube T g K
  let A1 := A.mapDiffeomorph K
  let N1 := N.mapDiffeomorph K
  let cap1 : UnitTwoSphere → E3 := P.capMap T1 s' sigma 0 lambda
  let north1 := cap1 '' Qplus
  let south1 := cap1 '' Qminus
  let rim1 := T1 '' (sphere (0 : E2) 1 ×ˢ ({s'} : Set ℝ))
  have hwidth : 0 < min eps (min beta tau) := lt_min heps (lt_min hbeta htau)
  have hgs : g s = s' := by
    have hz : |(0 : ℝ)| ≤ eps := by
      rw [abs_zero]
      exact hwidth.le.trans (min_le_left _ _)
    simpa only [add_zero] using haff 0 hz
  have hheight (p : E2 × ℝ) (hp : p ∈ T1.source) : H0 (T1 p) = p.2 := by
    change H0 (K (T (p.1, g.symm p.2))) = p.2
    rw [hKh, hTh _ ((heightTransportTube_mem_source T g K p).mp hp)]
    exact g.apply_symm_apply p.2
  have hinvheight (y : E3) (hy : y ∈ T1.target) : (T1.symm y).2 = H0 y := by
    have hh := hheight (T1.symm y) (T1.map_target hy)
    rw [T1.right_inv hy] at hh
    exact hh.symm

  have hBsource (B : BallNeighborhoodChart E3 E3) :
      (B.mapDiffeomorph K).chart.source = B.chart.source := by
    ext y
    change (y ∈ B.chart.source ∧ B.chart y ∈ (univ : Set E3)) ↔ _
    simp only [mem_univ, and_true]
  have hBtarget (B : BallNeighborhoodChart E3 E3) :
      (B.mapDiffeomorph K).chart.target = K '' B.chart.target := by
    ext y
    change (y ∈ (univ : Set E3) ∧ K.symm y ∈ B.chart.target) ↔ _
    constructor
    · intro hy
      exact ⟨K.symm y, hy.2, K.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_univ _, by simpa only [K.symm_apply_apply] using hx⟩
  have hNt1 : N1.chart.target = T1.target := by
    rw [hBtarget N, hNt]
    ext y
    rw [heightTransportTube_mem_target]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [K.symm_apply_apply] using hx
    · intro hy
      exact ⟨K.symm y, hy, K.apply_symm_apply y⟩
  have hcap (q : UnitTwoSphere) : cap1 q = K (cap0 q) := by
    have hoff : |sigma * (lambda * (P.model q).2)| ≤ eps := by
      calc
        _ = lambda * |(P.model q).2| := by
          rw [abs_mul, hsigma, one_mul, abs_mul, abs_of_pos hlambda]
        _ ≤ lambda * P.heightBound :=
          mul_le_mul_of_nonneg_left (P.height_bound q) hlambda.le
        _ ≤ eps := hsmall.le
    have hgq := haff (sigma * (lambda * (P.model q).2)) hoff
    have hgi : g.symm (s' + sigma * (lambda * (P.model q).2)) =
        s + sigma * (lambda * (P.model q).2) := by
      rw [← hgq, g.symm_apply_apply]
    simp only [cap1, cap0, SurgeryCapProfile.capMap_apply, zero_add,
      T1, heightTransportTube_apply, hgi]
  have hNc1 (q : UnitTwoSphere) : N1.chart (q : E3) = cap1 q := by
    change K (N.chart (q : E3)) = cap1 q
    rw [hNc q, hcap q]
  have hCapImage (X : Set UnitTwoSphere) : K '' (cap0 '' X) = cap1 '' X := by
    ext y
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, hcap q⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨cap0 q, ⟨q, hq, rfl⟩, (hcap q).symm⟩
  have hNorth : K '' north0 = north1 := hCapImage Qplus
  have hSouth : K '' south0 = south1 := hCapImage Qminus
  have hBack (X Y : Set E3) (hXY : K '' X = Y) : K.symm '' Y = X := by
    rw [← hXY, image_image]
    simp only [K.symm_apply_apply, image_id']
  have hInter (X Y : Set E3) : K '' (X ∩ Y) = K '' X ∩ K '' Y := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, ⟨x, hy, rfl⟩⟩
    · rintro ⟨⟨x, hx, rfl⟩, ⟨z, hz, hzx⟩⟩
      have hzx' : z = x := K.injective hzx
      exact ⟨x, ⟨hx, hzx' ▸ hz⟩, rfl⟩
  have hTubeImage (X : Set E2) (I : Set ℝ) :
      K '' (T '' (X ×ˢ I)) = T1 '' (X ×ˢ (g '' I)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩, rfl⟩
      exact ⟨(x, g z), ⟨hx, ⟨z, hz, rfl⟩⟩,
        heightTransportTube_reparametrized_apply T g K (x, z)⟩
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hw
      exact ⟨T (x, z), ⟨(x, z), ⟨hx, hz⟩, rfl⟩,
        (heightTransportTube_reparametrized_apply T g K (x, z)).symm⟩
  have hRim : K '' rim0 = rim1 := by
    simpa only [image_singleton, hgs] using hTubeImage (sphere 0 1) {s}
  have hA1 : A1.boundary = K '' E ∪ north1 := by
    rw [A.mapDiffeomorph_boundary, hA, image_union, hNorth]
  have hN1 : N1.boundary = south1 ∪ north1 := by
    rw [N.mapDiffeomorph_boundary, hN, image_union, hSouth, hNorth]
  have hEr1 : K '' E ∩ north1 = rim1 := by
    rw [← hNorth, ← hInter, hEr, hRim]
  have hNr1 : south1 ∩ north1 = rim1 := by
    rw [← hSouth, ← hNorth, ← hInter, hNr, hRim]
  have hNative : north1 = N1.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ H0 y} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q : E3), ⟨norm_eq_of_mem_sphere q, hq⟩, hNc1 q⟩
    · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
      let q : UnitTwoSphere := ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
      exact ⟨q, hp, (hNc1 q).symm⟩
  have hContain : N1.closedRegion ⊆ A1.closedRegion := by
    rw [N.mapDiffeomorph_closedRegion, A.mapDiffeomorph_closedRegion]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hNA hx, rfl⟩

  have hShort : N1.closedRegion ⊆ {y : E3 | |H0 y - s'| < tau} := by
    rw [N.mapDiffeomorph_closedRegion]
    rintro _ ⟨x, hx, rfl⟩
    have hw : |H0 x - s| < tau := hNw hx
    have hh := haff (H0 x - s) (hw.le.trans hte)
    rw [show s + (H0 x - s) = H0 x by ring] at hh
    change |H0 (K x) - s'| < tau
    rw [hKh, hh]
    simpa only [add_sub_cancel_left] using hw
  have hBounds (y : E3) (hy : y ∈ A1.closedRegion) :
      g lo ≤ H0 y ∧ H0 y ≤ g hi := by
    rw [A.mapDiffeomorph_closedRegion] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hKh]
    exact ⟨hg.monotone (hAw x hx).1, hg.monotone (hAw x hx).2⟩
  have hPatch1 (q : UnitTwoSphere) (hq : -1 / 8 < H0 (q : E3)) :
      N1.chart (q : E3) ∈ A1.boundary := by
    rw [A.mapDiffeomorph_boundary]
    exact ⟨N.chart (q : E3), hpatch q hq, rfl⟩
  have hClosed : IsClosed (K '' Z) := by
    have hpre : K '' Z = K.symm ⁻¹' Z := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa only [mem_preimage, K.symm_apply_apply] using hx
      · intro hy
        exact ⟨K.symm y, hy, K.apply_symm_apply y⟩
    rw [hpre]
    exact hZ.preimage K.symm.continuous
  have hAvoid1 : A1.closedRegion ∩ K '' Z ⊆ north1 := by
    rw [A.mapDiffeomorph_closedRegion, ← hInter, ← hNorth]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, havoid hx, rfl⟩
  have hLevel (D : Set E3) (a b : ℝ) (hab : g a = b) :
      K '' (D ∩ {y : E3 | H0 y = a}) =
        (K '' D) ∩ {y : E3 | H0 y = b} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hh⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      change H0 (K x) = b
      rw [hKh, hh, hab]
    · rintro ⟨⟨x, hx, rfl⟩, hh⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      exact g.injective ((hKh x).symm.trans (hh.trans hab.symm))
  have hCuts1 (r : ℝ) (hr : r ∈ Icc (0 : ℝ) beta) :
      A1.inside ∩ {y : E3 | H0 y = s' - sigma * r} =
        T1 '' (ball (0 : E2) 1 ×ˢ ({s' - sigma * r} : Set ℝ)) ∧
      A1.closedRegion ∩ {y : E3 | H0 y = s' - sigma * r} =
        T1 '' (closedBall (0 : E2) 1 ×ˢ ({s' - sigma * r} : Set ℝ)) ∧
      A1.boundary ∩ {y : E3 | H0 y = s' - sigma * r} =
        T1 '' (sphere (0 : E2) 1 ×ˢ ({s' - sigma * r} : Set ℝ)) := by
    have hoff : |-(sigma * r)| ≤ eps := by
      rw [abs_neg, abs_mul, hsigma, one_mul, abs_of_nonneg hr.1]
      exact hr.2.trans hbe
    have hgcut : g (s - sigma * r) = s' - sigma * r := by
      simpa only [sub_eq_add_neg] using haff (-(sigma * r)) hoff
    have htube (X : Set E2) :
        K '' (T '' (X ×ˢ ({s - sigma * r} : Set ℝ))) =
          T1 '' (X ×ˢ ({s' - sigma * r} : Set ℝ)) := by
      simpa only [image_singleton, hgcut] using hTubeImage X {s - sigma * r}
    obtain ⟨hi, hc, hb⟩ := hcuts r hr
    change A.inside ∩ {y : E3 | H0 y = s - sigma * r} = _ at hi
    change A.closedRegion ∩ {y : E3 | H0 y = s - sigma * r} = _ at hc
    change A.boundary ∩ {y : E3 | H0 y = s - sigma * r} = _ at hb
    refine ⟨?_, ?_, ?_⟩
    · rw [A.mapDiffeomorph_inside, ← hLevel A.inside _ _ hgcut, hi, htube]
    · rw [A.mapDiffeomorph_closedRegion, ← hLevel A.closedRegion _ _ hgcut, hc, htube]
    · rw [A.mapDiffeomorph_boundary, ← hLevel A.boundary _ _ hgcut, hb, htube]
  have hIcc (a b : ℝ) : g '' Icc a b = Icc (g a) (g b) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hg.monotone hx.1, hg.monotone hx.2⟩
    · intro hz
      refine ⟨g.symm z, ⟨?_, ?_⟩, g.apply_symm_apply z⟩
      · by_contra hn
        have hh := hg (lt_of_not_ge hn)
        rw [g.apply_symm_apply] at hh
        exact (not_lt_of_ge hz.1) hh
      · by_contra hn
        have hh := hg (lt_of_not_ge hn)
        rw [g.apply_symm_apply] at hh
        exact (not_lt_of_ge hz.2) hh
  have hIci : g '' Ici s = Ici s' := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change s' ≤ g x
      rw [← hgs]
      exact hg.monotone hx
    · intro hz
      refine ⟨g.symm z, ?_, g.apply_symm_apply z⟩
      change s ≤ g.symm z
      by_contra hn
      have hh := hg (lt_of_not_ge hn)
      rw [g.apply_symm_apply, hgs] at hh
      exact (not_lt_of_ge hz) hh
  refine ⟨heightTransportTube_apply T g K, heightTransportTube_symm_apply T g K,
    heightTransportTube_mem_source T g K, heightTransportTube_mem_target T g K,
    heightTransportTube_contDiffOn T g K hT, heightTransportTube_contDiffOn_symm T g K hTi,
    heightTransportTube_closedDisc_source T g K hTs, hheight, hinvheight,
    hBsource A, hBtarget A, fun _ => rfl, fun _ => rfl,
    A.mapDiffeomorph_inside K, A.mapDiffeomorph_closedRegion K, A.mapDiffeomorph_boundary K,
    hBsource N, hNt1, fun _ => rfl, fun _ => rfl,
    N.mapDiffeomorph_inside K, N.mapDiffeomorph_closedRegion K, N.mapDiffeomorph_boundary K,
    fun q => ⟨hcap q, hNc1 q⟩, hNorth, hBack _ _ hNorth, hSouth, hBack _ _ hSouth,
    hRim, hBack _ _ hRim, hBack E (K '' E) rfl, hA1, hN1, hEr1, hNr1,
    hNative, hContain, hShort, hBounds, hPatch1, hClosed, hAvoid1, hCuts1, hTubeImage, ?_, ?_⟩
  · intro a b
    rw [hTubeImage, hIcc]
  · rw [hTubeImage, hIci]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
