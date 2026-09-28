import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.TwoBandLabelMatching
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionUniqueness
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem saddle_nested_transported_tube
    (u : UnitTwoSphere) (K0 : D3)
    (hK0 : ∀ y : E3, ⟪(u : E3), K0 y⟫_ℝ = ⟪(u : E3), y⟫_ℝ)
    (Tp : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hTps : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ Tp.source)
    (hTp : ContDiffOn ℝ ∞ Tp Tp.source)
    (hTpi : ContDiffOn ℝ ∞ Tp.symm Tp.target)
    (hTph : ∀ x ∈ Tp.source, ⟪(u : E3), Tp x⟫_ℝ = x.2) :
    ∃ U : OpenPartialHomeomorph (E2 × ℝ) E3,
      U.source = Tp.source ∧ (∀ x : E2 × ℝ, U x = K0 (Tp x)) ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ U.source ∧
      ContDiffOn ℝ ∞ U U.source ∧ ContDiffOn ℝ ∞ U.symm U.target ∧
      (∀ x ∈ U.source, ⟪(u : E3), U x⟫_ℝ = x.2) ∧
      (∀ B : Set (E2 × ℝ), K0 '' (Tp '' B) = U '' B) ∧
      ∀ (P : SurgeryCapProfile) (s sigma lambda : ℝ) (Q : Set UnitTwoSphere),
        K0 '' (P.capMap Tp s sigma 0 lambda '' Q) =
          P.capMap U s sigma 0 lambda '' Q := by
  let h := Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞
  let U := heightTransportTube Tp h K0
  have hsource : U.source = Tp.source := by
    ext p
    exact heightTransportTube_mem_source Tp h K0 p
  have hpoint (p : E2 × ℝ) : U p = K0 (Tp p) := rfl
  refine ⟨U, hsource, hpoint, heightTransportTube_closedDisc_source Tp h K0 hTps,
    heightTransportTube_contDiffOn Tp h K0 hTp,
    heightTransportTube_contDiffOn_symm Tp h K0 hTpi, ?_, ?_, ?_⟩
  · intro p hp
    rw [hpoint, hK0]
    exact hTph p (hsource ▸ hp)
  · intro B
    rw [image_image]
    rfl
  · intro P s sigma lambda Q
    rw [image_image]
    rfl

set_option linter.unusedVariables false in

theorem saddle_nested_middle_whole_image
    (u : UnitTwoSphere) (K0 : D3)
    (hK0 : ∀ y : E3, ⟪(u : E3), K0 y⟫_ℝ = ⟪(u : E3), y⟫_ℝ)
    (Sp S : Set E3) (t z v b : ℝ) (hb : 0 < b) (htz : 4 * b < z - t)
    (hzv : z < v)
    (hlevels : ∀ s ∈ Icc (t - 4 * b) (v + 4 * b),
      K0 '' (Sp ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = s}) =
        S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = s})
    (Tp T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3)
    (hTps : ∀ k, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (Tp k).source)
    (hTs : ∀ k, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T k).source)
    (hTp : ∀ k, ContDiffOn ℝ ∞ (Tp k) (Tp k).source)
    (hT : ∀ k, ContDiffOn ℝ ∞ (T k) (T k).source)
    (hTph : ∀ k x, x ∈ (Tp k).source → ⟪(u : E3), Tp k x⟫_ℝ = x.2)
    (hTh : ∀ k x, x ∈ (T k).source → ⟪(u : E3), T k x⟫_ℝ = x.2)
    (hlowerP : ∀ s ∈ Icc (t - 4 * b) (z + 4 * b),
      Sp ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = s} =
        Tp 0 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
          Tp 1 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
      Tp 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
        Tp 1 '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ)))
    (hlower : ∀ s ∈ Icc (t - 4 * b) (z + 4 * b),
      S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = s} =
        T 0 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
          T 1 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
      T 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
        T 1 '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ)))
    (hupperP : ∀ s ∈ Icc (v - 4 * b) (v + 4 * b),
      Tp 2 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
        Sp ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = s})
    (hupper : ∀ s ∈ Icc (v - 4 * b) (v + 4 * b),
      T 2 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
        S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = s}) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let cut : Fin 3 → ℝ := ![z, t, v]
    let window : Fin 3 → Set ℝ := ![Icc (z - 4 * b) (z + 4 * b),
      Icc (t - 4 * b) (t + 4 * b), Icc (v - 4 * b) (v + 4 * b)]
    K0 '' ((Sp ∩ {y | z ≤ H y ∧ H y ≤ v}) ∪
        Tp 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z)) =
      (S ∩ {y | z ≤ H y ∧ H y ≤ v}) ∪ T 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z) ∧
    ∀ (k : Fin 3), ∀ s ∈ window k,
      K0 '' (Tp k '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))) =
        T k '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) := by
  classical
  dsimp only
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let L := heightPlaneCoordinates u
  let U : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3 :=
    fun i => (Tp i.castSucc).transHomeomorph K0.toHomeomorph
  have hUs (i : Fin 2) :
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (U i).source := hTps i.castSucc
  have hUh (i : Fin 2) (p : E2 × ℝ) (hp : p ∈ (U i).source) :
      H (U i p) = p.2 :=
    (hK0 (Tp i.castSucc p)).trans (hTph i.castSucc p hp)
  have hUimage (i : Fin 2) (B : Set (E2 × ℝ)) :
      U i '' B = K0 '' (Tp i.castSucc '' B) := by
    rw [image_image]
    rfl
  have hTwo (E : Fin 2 → Set E3) : (⋃ i : Fin 2, E i) = E 0 ∪ E 1 := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · intro hy
      exact hy.elim (fun hh => mem_iUnion.mpr ⟨0, hh⟩)
        (fun hh => mem_iUnion.mpr ⟨1, hh⟩)
  have hdis : Disjoint
      (T 0 '' (sphere (0 : E2) 1 ×ˢ Icc (t - 4 * b) (z + 4 * b)))
      (T 1 '' (sphere (0 : E2) 1 ×ˢ Icc (t - 4 * b) (z + 4 * b))) := by
    apply disjoint_left.mpr
    rintro y ⟨p, hp, hpy⟩ ⟨q, hq, hqy⟩
    have hi : T 0 p ∈ T 1 '' (ball (0 : E2) 1 ×ˢ ({p.2} : Set ℝ)) :=
      (hlower p.2 hp.2).2 ⟨p, ⟨sphere_subset_closedBall hp.1, rfl⟩, rfl⟩
    obtain ⟨r, hr, hrp⟩ := hi
    have hrq : r = q := (T 1).injOn
      (hTs 1 ⟨ball_subset_closedBall hr.1, mem_univ _⟩)
      (hTs 1 ⟨sphere_subset_closedBall hq.1, mem_univ _⟩)
      (hrp.trans (hpy.trans hqy.symm))
    have hn := mem_ball_zero_iff.mp hr.1
    rw [hrq] at hn
    have he := mem_sphere_zero_iff_norm.mp hq.1
    linarith
  have hUnion (s : ℝ) (hs : s ∈ Icc (t - 4 * b) (z + 4 * b)) :
      (⋃ i : Fin 2, U i '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))) =
        ⋃ i : Fin 2, T i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) := by
    rw [hTwo, hTwo, hUimage, hUimage]
    change K0 '' (Tp 0 '' _) ∪ K0 '' (Tp 1 '' _) = T 0 '' _ ∪ T 1 '' _
    rw [← image_union, ← (hlowerP s hs).1,
      hlevels s ⟨hs.1, by linarith [hs.2]⟩, (hlower s hs).1]
  obtain ⟨e, _heband, he⟩ := exists_saddle_two_band_label_matching
    (fun i => U i) (fun i => T i.castSucc) H (t - 4 * b) (z + 4 * b) (by linarith)
    (fun i => (K0.continuous.comp_continuousOn (hTp i.castSucc).continuousOn).mono
      (fun _ hx => hTps i.castSucc ⟨sphere_subset_closedBall hx.1, mem_univ _⟩))
    (fun i => (hT i.castSucc).continuousOn.mono
      (fun _ hx => hTs i.castSucc ⟨sphere_subset_closedBall hx.1, mem_univ _⟩))
    (fun i x hx s _ => hUh i (x, s) (hUs i ⟨sphere_subset_closedBall hx, mem_univ _⟩))
    (fun i x hx s _ => hTh i.castSucc (x, s)
      (hTs i.castSucc ⟨sphere_subset_closedBall hx, mem_univ _⟩))
    hUnion hdis
  have hslice (A : OpenPartialHomeomorph (E2 × ℝ) E3) (B : Set E2) (w : ℝ) :
      A '' (B ×ˢ ({w} : Set ℝ)) = (fun x : E2 => A (x, w)) '' B := by
    ext y
    constructor
    · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
      have hsw : s = w := mem_singleton_iff.mp hs
      subst s
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x, w), ⟨hx, rfl⟩, rfl⟩

  have hfiber (A : OpenPartialHomeomorph (E2 × ℝ) E3)
      (hAs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ A.source)
      (hAh : ∀ p ∈ A.source, H (A p) = p.2) :
      ∃ B : OpenPartialHomeomorph E2 E2,
        (∀ x, B x = (L (A (x, z))).1) ∧ closedBall (0 : E2) 1 ⊆ B.source := by
    let eA := A.transHomeomorph L.toHomeomorph
    have heh (p : E2 × ℝ) (hp : p ∈ eA.source) : (eA p).2 = p.2 :=
      (heightPlaneCoordinates_snd u (A p)).trans (hAh p hp)
    let iota : E2 → E2 × ℝ := fun x => (x, z)
    let source := iota ⁻¹' eA.source
    let target := iota ⁻¹' eA.target
    let f : E2 → E2 := fun x => (eA (iota x)).1
    let g : E2 → E2 := fun y => (eA.symm (iota y)).1
    have hiota : Continuous iota := continuous_id.prodMk continuous_const
    have hinvh (p : E2 × ℝ) (hp : p ∈ eA.target) : (eA.symm p).2 = p.2 := by
      have h := heh (eA.symm p) (eA.map_target hp)
      rw [eA.right_inv hp] at h
      exact h.symm
    have hif (x : E2) (hx : x ∈ source) : iota (f x) = eA (iota x) := by
      apply Prod.ext
      · rfl
      · exact (heh (iota x) hx).symm
    have hig (y : E2) (hy : y ∈ target) : iota (g y) = eA.symm (iota y) := by
      apply Prod.ext
      · rfl
      · exact (hinvh (iota y) hy).symm
    let B : OpenPartialHomeomorph E2 E2 := {
      toFun := f
      invFun := g
      source := source
      target := target
      map_source' := by
        intro x hx
        change iota (f x) ∈ eA.target
        rw [hif x hx]
        exact eA.map_source hx
      map_target' := by
        intro y hy
        change iota (g y) ∈ eA.source
        rw [hig y hy]
        exact eA.map_target hy
      left_inv' := by
        intro x hx
        change (eA.symm (iota (f x))).1 = x
        rw [hif x hx, eA.left_inv hx]
      right_inv' := by
        intro y hy
        change (eA (iota (g y))).1 = y
        rw [hig y hy, eA.right_inv hy]
      open_source := eA.open_source.preimage hiota
      open_target := eA.open_target.preimage hiota
      continuousOn_toFun := (eA.continuousOn.comp hiota.continuousOn (fun _ hx => hx)).fst
      continuousOn_invFun :=
        (eA.symm.continuousOn.comp hiota.continuousOn (fun _ hy => hy)).fst }
    exact ⟨B, fun _ => rfl, fun x hx => hAs ⟨hx, mem_univ _⟩⟩
  have hdim : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E2]
  have hz : z ∈ Icc (t - 4 * b) (z + 4 * b) := ⟨by linarith, by linarith⟩
  have hlift (A B : OpenPartialHomeomorph (E2 × ℝ) E3)
      (hAs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ A.source)
      (hBs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ B.source)
      (hAh : ∀ x ∈ A.source, H (A x) = x.2)
      (hBh : ∀ x ∈ B.source, H (B x) = x.2)
      (hh : (fun x : E2 => (L (A (x, z))).1) '' closedBall 0 1 =
        (fun x : E2 => (L (B (x, z))).1) '' closedBall 0 1) :
      A '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ⊆
        B '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
    rw [hslice, hslice]
    rintro _ ⟨x, hx, rfl⟩
    have hximage : (L (A (x, z))).1 ∈
        (fun y : E2 => (L (B (y, z))).1) '' closedBall 0 1 := by
      rw [← hh]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hximage
    refine ⟨y, hy, L.injective (Prod.ext hxy ?_)⟩
    simp only [L, heightPlaneCoordinates_snd]
    exact (hBh (y, z) (hBs ⟨hy, mem_univ _⟩)).trans
      (hAh (x, z) (hAs ⟨hx, mem_univ _⟩)).symm
  have hsame (i : Fin 2) :
      U i '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        T (e i).castSucc '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
    obtain ⟨BU, hBU, hBUs⟩ := hfiber (U i) (hUs i) (hUh i)
    obtain ⟨BV, hBV, hBVs⟩ := hfiber (T (e i).castSucc) (hTs (e i).castSucc)
      (hTh (e i).castSucc)
    have hBUimage (A : Set E2) : BU '' A =
        (fun x : E2 => (L (U i (x, z))).1) '' A := image_congr (fun x _ => hBU x)
    have hBVimage (A : Set E2) : BV '' A =
        (fun x : E2 => (L (T (e i).castSucc (x, z))).1) '' A :=
      image_congr (fun x _ => hBV x)
    have hbound : BU '' sphere 0 1 = BV '' sphere 0 1 := by
      rw [hBUimage, hBVimage]
      have hh := congrArg (fun A : Set E3 => (fun y => (L y).1) '' A) (he i z hz)
      simpa only [hslice, image_image] using hh
    have hBUcompact : IsCompact (BU '' closedBall (0 : E2) 1) :=
      (isCompact_closedBall _ _).image_of_continuousOn (BU.continuousOn.mono hBUs)
    have hBVcompact : IsCompact (BV '' closedBall (0 : E2) 1) :=
      (isCompact_closedBall _ _).image_of_continuousOn (BV.continuousOn.mono hBVs)
    have hne : BU '' closedBall (0 : E2) 1 ∪ BV '' closedBall (0 : E2) 1 ≠ univ := by
      intro hall
      have hbounded := (hBUcompact.union hBVcompact).isBounded
      rw [hall] at hbounded
      exact NormedSpace.unbounded_univ ℝ E2 hbounded
    obtain ⟨p, hp⟩ := (ne_univ_iff_exists_notMem _).mp hne
    have hclosed := compactChart_region_eq_of_boundary_eq BU BV hdim hBUs hBVs hbound
      (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))
    rw [hBUimage, hBVimage] at hclosed
    exact Subset.antisymm
      (hlift (U i) (T (e i).castSucc) (hUs i) (hTs (e i).castSucc)
        (hUh i) (hTh (e i).castSucc) hclosed)
      (hlift (T (e i).castSucc) (U i) (hTs (e i).castSucc) (hUs i)
        (hTh (e i).castSucc) (hUh i) hclosed.symm)
  have he0 : e 0 = 0 := by
    by_contra hnot
    have he01 : e 0 = 1 := by omega
    have he10 : e 1 = 0 := by
      have hne : e 1 ≠ e 0 := e.injective.ne (by decide)
      rw [he01] at hne
      omega
    have hnest : U 0 '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ⊆
        U 1 '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
      rw [hUimage, hUimage]
      apply image_mono
      exact (hlowerP z hz).2.trans (image_mono (prod_mono ball_subset_closedBall subset_rfl))
    rw [hsame 0, hsame 1, he01, he10] at hnest
    have hbad : T 1 '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ⊆
        T 1 '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := hnest.trans (hlower z hz).2
    obtain ⟨x, hx⟩ := (isConnected_sphere hdim (0 : E2) zero_le_one).nonempty
    obtain ⟨p, hp, hpx⟩ := hbad ⟨(x, z), ⟨sphere_subset_closedBall hx, rfl⟩, rfl⟩
    have heq : p = (x, z) := (T 1).injOn
      (hTs 1 ⟨ball_subset_closedBall hp.1, mem_univ _⟩)
      (hTs 1 ⟨sphere_subset_closedBall hx, mem_univ _⟩) hpx
    have hn := mem_ball_zero_iff.mp hp.1
    rw [heq] at hn
    have hxnorm := mem_sphere_zero_iff_norm.mp hx
    exact (not_lt_of_ge hxnorm.ge) hn
  have he1 : e 1 = 1 := by
    have hne : e 1 ≠ e 0 := e.injective.ne (by decide)
    rw [he0] at hne
    omega
  have heid (i : Fin 2) : e i = i := by
    fin_cases i
    · exact he0
    · exact he1
  have hordered (i : Fin 2) (s : ℝ) (hs : s ∈ Icc (t - 4 * b) (z + 4 * b)) :
      K0 '' (Tp i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))) =
        T i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) := by
    rw [← hUimage]
    simpa only [heid] using he i s hs
  have horderedUpper (s : ℝ) (hs : s ∈ Icc (v - 4 * b) (v + 4 * b)) :
      K0 '' (Tp 2 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))) =
        T 2 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) := by
    rw [hupperP s hs, hlevels s ⟨by linarith [hs.1], hs.2⟩, hupper s hs]
  have houter : K0 '' (Tp 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z)) =
      T 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z) := by
    rw [image_image]
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hs : p.2 ∈ Icc (t - 4 * b) (z + 4 * b) :=
        ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
      have hm : K0 (Tp 1 p) ∈ T 1 '' (sphere (0 : E2) 1 ×ˢ ({p.2} : Set ℝ)) := by
        have hh : K0 '' (Tp 1 '' (sphere (0 : E2) 1 ×ˢ ({p.2} : Set ℝ))) =
            T 1 '' (sphere (0 : E2) 1 ×ˢ ({p.2} : Set ℝ)) := hordered 1 p.2 hs
        rw [← hh]
        exact ⟨Tp 1 p, ⟨p, ⟨hp.1, rfl⟩, rfl⟩, rfl⟩
      obtain ⟨q, hq, hqp⟩ := hm
      refine ⟨q, ⟨hq.1, ?_⟩, hqp⟩
      rw [mem_singleton_iff.mp hq.2]
      exact hp.2
    · rintro ⟨q, hq, rfl⟩
      have hs : q.2 ∈ Icc (t - 4 * b) (z + 4 * b) :=
        ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
      have hm : T 1 q ∈ K0 '' (Tp 1 '' (sphere (0 : E2) 1 ×ˢ ({q.2} : Set ℝ))) := by
        have hh : K0 '' (Tp 1 '' (sphere (0 : E2) 1 ×ˢ ({q.2} : Set ℝ))) =
            T 1 '' (sphere (0 : E2) 1 ×ˢ ({q.2} : Set ℝ)) := hordered 1 q.2 hs
        rw [hh]
        exact ⟨q, ⟨hq.1, rfl⟩, rfl⟩
      obtain ⟨x, ⟨p, hp, rfl⟩, hpx⟩ := hm
      refine ⟨p, ⟨hp.1, ?_⟩, hpx⟩
      rw [mem_singleton_iff.mp hp.2]
      exact hq.2
  have hcentral : K0 '' (Sp ∩ {y | z ≤ H y ∧ H y ≤ v}) =
      S ∩ {y | z ≤ H y ∧ H y ≤ v} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hs : H x ∈ Icc (t - 4 * b) (v + 4 * b) :=
        ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
      have hm : K0 x ∈ S ∩ {q : E3 | H q = H x} := by
        change K0 x ∈ S ∩ {q : E3 | ⟪(u : E3), q⟫_ℝ = H x}
        rw [← hlevels (H x) hs]
        exact ⟨x, ⟨hx.1, rfl⟩, rfl⟩
      refine ⟨hm.1, ?_⟩
      change z ≤ ⟪(u : E3), K0 x⟫_ℝ ∧ ⟪(u : E3), K0 x⟫_ℝ ≤ v
      rw [hK0]
      exact hx.2
    · intro hy
      have hs : H y ∈ Icc (t - 4 * b) (v + 4 * b) :=
        ⟨by linarith [hy.2.1], by linarith [hy.2.2]⟩
      have hm : y ∈ K0 '' (Sp ∩ {q : E3 | H q = H y}) := by
        change y ∈ K0 '' (Sp ∩ {q : E3 | ⟪(u : E3), q⟫_ℝ = H y})
        rw [hlevels (H y) hs]
        exact ⟨hy.1, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hm
      refine ⟨x, ⟨hx.1, ?_⟩, hxy⟩
      change z ≤ H x ∧ H x ≤ v
      rw [show H x = H y from hx.2]
      exact hy.2
  constructor
  · rw [image_union, hcentral, houter]
  · intro k s hs
    fin_cases k
    · exact hordered 0 s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · exact hordered 1 s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · exact horderedUpper s hs
end PoincareConjecture.M25.Topology3D
