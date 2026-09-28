import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.TwoBandLabelMatching
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionUniqueness
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsPairedAlignment
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFullCapAlignment
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_three_cap_alignment
    (P : SurgeryCapProfile) (u : UnitTwoSphere)
    (U V : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3)
    (hU : ∀ i, ContDiffOn ℝ ∞ (U i) (U i).source)
    (hUi : ∀ i, ContDiffOn ℝ ∞ (U i).symm (U i).target)
    (hV : ∀ i, ContDiffOn ℝ ∞ (V i) (V i).source)
    (hVi : ∀ i, ContDiffOn ℝ ∞ (V i).symm (V i).target)
    (hUs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (U i).source)
    (hVs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (V i).source)
    (hUh : ∀ i x, x ∈ (U i).source → ⟪(u : E3), U i x⟫_ℝ = x.2)
    (hVh : ∀ i x, x ∈ (V i).source → ⟪(u : E3), V i x⟫_ℝ = x.2)
    (S R : Set E3) (m c p tau : ℝ) (htau : 0 < tau)
    (hmc : m + 4 * tau < c) (hcp : c + 4 * tau < p)
    (hR : R ⊆ S)
    (hRheight : ∀ y ∈ R, m ≤ ⟪(u : E3), y⟫_ℝ ∧ ⟪(u : E3), y⟫_ℝ ≤ p)
    (O : Fin 2 → Set E3) (hO : ∀ i, IsOpen (O i))
    (hOdis : Disjoint (O 0) (O 1))
    (hVbuffer : ∀ i : Fin 2,
      V i.castSucc '' (closedBall (0 : E2) 1 ×ˢ Icc (m - tau) (m + tau)) ⊆ O i)
    (hLower : ∀ z ∈ Icc (m - tau) (m + tau),
      (⋃ i : Fin 2, U i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))) =
        S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = z} ∧
      (⋃ i : Fin 2, V i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))) =
        S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = z})
    (hUpper : ∀ z ∈ Icc (p - tau) (p + tau),
      U 2 '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = z} ∧
      V 2 '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = z}) :
    ∃ eta bound : ℝ, 0 < eta ∧ eta < tau ∧ 1 ≤ bound ∧ P.heightBound ≤ bound ∧
      ∀ lambda : ℝ, 0 < lambda → lambda * bound < eta →
        let cut : Fin 3 → ℝ := ![m, m, p]
        let sign : Fin 3 → ℝ := ![1, 1, -1]
        let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
        let CU : Fin 3 → Set E3 := fun i =>
          P.capMap (U i) (cut i) (sign i) 0 lambda '' Qminus
        let CV : Fin 3 → Set E3 := fun i =>
          P.capMap (V i) (cut i) (sign i) 0 lambda '' Qminus
        ∃ (F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (K : Set E3),
          F '' (R ∪ ⋃ i : Fin 3, CU i) = R ∪ ⋃ i : Fin 3, CV i ∧
          F.symm '' (R ∪ ⋃ i : Fin 3, CV i) = R ∪ ⋃ i : Fin 3, CU i ∧
          (∀ y ∈ R, F y = y ∧ F.symm y = y) ∧
          IsCompact K ∧
          tsupport (fun y => F y - y) ⊆ K ∧
          tsupport (fun y => F.symm y - y) ⊆ K := by
  classical
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let L := heightPlaneCoordinates u
  let UL : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3 := fun i => U i.castSucc
  have hslice (T : OpenPartialHomeomorph (E2 × ℝ) E3) (A : Set E2) (z : ℝ) :
      T '' (A ×ˢ ({z} : Set ℝ)) = (fun x : E2 => T (x, z)) '' A := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have htz : t = z := mem_singleton_iff.mp ht
      subst t
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x, z), ⟨hx, rfl⟩, rfl⟩
  have hVbands (i : Fin 2) :
      V i.castSucc '' (sphere (0 : E2) 1 ×ˢ Icc (m - tau) (m + tau)) ⊆ O i :=
    (image_mono (prod_mono sphere_subset_closedBall subset_rfl)).trans (hVbuffer i)
  obtain ⟨e, _heband, he⟩ := exists_saddle_two_band_label_matching
    (fun i => UL i) (fun i => V i.castSucc) H (m - tau) (m + tau) (by linarith)
    (fun i => (hU i.castSucc).continuousOn.mono
      (fun _ hx => hUs i.castSucc ⟨sphere_subset_closedBall hx.1, mem_univ _⟩))
    (fun i => (hV i.castSucc).continuousOn.mono
      (fun _ hx => hVs i.castSucc ⟨sphere_subset_closedBall hx.1, mem_univ _⟩))
    (fun i x hx z _ => hUh i.castSucc (x, z)
      (hUs i.castSucc ⟨sphere_subset_closedBall hx, mem_univ _⟩))
    (fun i x hx z _ => hVh i.castSucc (x, z)
      (hVs i.castSucc ⟨sphere_subset_closedBall hx, mem_univ _⟩))
    (fun z hz => (hLower z hz).1.trans (hLower z hz).2.symm)
    (hOdis.mono (hVbands 0) (hVbands 1))
  let VL : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3 := fun i => V (e i).castSucc
  have hm : m ∈ Icc (m - tau) (m + tau) := ⟨by linarith, by linarith⟩
  have hboundary (i : Fin 2) (z : ℝ) (hz : z ∈ Icc (m - tau) (m + tau)) :
      (fun x : E2 => UL i (x, z)) '' sphere 0 1 =
        (fun x : E2 => VL i (x, z)) '' sphere 0 1 := by
    simpa only [hslice] using he i z hz
  have hchart (T : OpenPartialHomeomorph (E2 × ℝ) E3)
      (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
      (hTh : ∀ x ∈ T.source, H (T x) = x.2)
      (hTs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source) :
      ∃ B : BallNeighborhoodChart E2 E2, ∀ x : E2,
        B.chart x = (L (T (x, m))).1 := by
    let A := T.trans L.toHomeomorph.toOpenPartialHomeomorph
    have hA : ContDiffOn ℝ ∞ A A.source :=
      L.contDiff.comp_contDiffOn (hT.mono (fun _ hx => hx.1))
    have hAi : ContDiffOn ℝ ∞ A.symm A.target :=
      hTi.comp L.symm.contDiff.contDiffOn (fun _ hx => hx.2)
    have hAh (x : E2 × ℝ) (hx : x ∈ A.source) : (A x).2 = x.2 :=
      (heightPlaneCoordinates_snd u (T x)).trans (hTh x hx.1)
    obtain ⟨B, hB, _, _, _⟩ := exists_saddle_end_fiber_chart A hA hAi hAh m
      (fun x hx => ⟨hTs ⟨hx, mem_univ _⟩, mem_univ _⟩)
    exact ⟨B, hB⟩
  have hdim : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E2]
  have hlift (A B : OpenPartialHomeomorph (E2 × ℝ) E3)
      (hAs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ A.source)
      (hBs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ B.source)
      (hAh : ∀ x ∈ A.source, H (A x) = x.2)
      (hBh : ∀ x ∈ B.source, H (B x) = x.2)
      (hh : (fun x : E2 => (L (A (x, m))).1) '' closedBall 0 1 =
        (fun x : E2 => (L (B (x, m))).1) '' closedBall 0 1) :
      A '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)) ⊆
        B '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)) := by
    rw [hslice, hslice]
    rintro _ ⟨x, hx, rfl⟩
    have hximage : (L (A (x, m))).1 ∈
        (fun y : E2 => (L (B (y, m))).1) '' closedBall 0 1 := by
      rw [← hh]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hximage
    refine ⟨y, hy, L.injective (Prod.ext hxy ?_)⟩
    simp only [L, heightPlaneCoordinates_snd]
    exact (hBh (y, m) (hBs ⟨hy, mem_univ _⟩)).trans
      (hAh (x, m) (hAs ⟨hx, mem_univ _⟩)).symm
  have hsame (i : Fin 2) :
      UL i '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)) =
        VL i '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)) := by
    obtain ⟨BU, hBU⟩ := hchart (UL i) (hU i.castSucc) (hUi i.castSucc)
      (hUh i.castSucc) (hUs i.castSucc)
    obtain ⟨BV, hBV⟩ := hchart (VL i) (hV (e i).castSucc) (hVi (e i).castSucc)
      (hVh (e i).castSucc) (hVs (e i).castSucc)
    have hBUs (A : Set E2) : BU.chart '' A =
        (fun x : E2 => (L (UL i (x, m))).1) '' A := image_congr (fun x _ => hBU x)
    have hBVs (A : Set E2) : BV.chart '' A =
        (fun x : E2 => (L (VL i (x, m))).1) '' A := image_congr (fun x _ => hBV x)
    have hbound : BU.boundary = BV.boundary := by
      change BU.chart '' sphere 0 1 = BV.chart '' sphere 0 1
      rw [hBUs, hBVs]
      have hh := congrArg (fun A : Set E3 => (fun y => (L y).1) '' A)
        (hboundary i m hm)
      simpa only [image_image] using hh
    have hclosed := BU.closedRegion_eq_of_boundary_eq BV hdim hbound
    change BU.chart '' closedBall 0 1 = BV.chart '' closedBall 0 1 at hclosed
    rw [hBUs, hBVs] at hclosed
    exact Subset.antisymm
      (hlift (UL i) (VL i) (hUs i.castSucc) (hVs (e i).castSucc)
        (hUh i.castSucc) (hVh (e i).castSucc) hclosed)
      (hlift (VL i) (UL i) (hVs (e i).castSucc) (hUs i.castSucc)
        (hVh (e i).castSucc) (hUh i.castSucc) hclosed.symm)
  have hdiscO (i : Fin 2) :
      VL i '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)) ⊆ O (e i) := by
    apply Subset.trans ?_ (hVbuffer (e i))
    exact image_mono (prod_mono subset_rfl (singleton_subset_iff.mpr hm))
  have hOij (i j : Fin 2) (hij : i ≠ j) : Disjoint (O i) (O j) := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hOdis
    · exact hOdis.symm
    · exact False.elim (hij rfl)
  have hdis : Disjoint
      (UL 0 '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)))
      (UL 1 '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ))) := by
    rw [hsame 0, hsame 1]
    exact (hOij (e 0) (e 1) (e.injective.ne (by decide))).mono (hdiscO 0) (hdiscO 1)
  let WL : Fin 2 → Set E3 := fun i => O (e i) ∩ {y | H y < c}
  have hWL (i : Fin 2) : IsOpen (WL i) :=
    (hO (e i)).inter (isOpen_Iio.preimage H.continuous)
  have hUWL (i : Fin 2) :
      UL i '' (closedBall (0 : E2) 1 ×ˢ ({m} : Set ℝ)) ⊆ WL i := by
    intro y hy
    refine ⟨hdiscO i (hsame i ▸ hy), ?_⟩
    obtain ⟨x, hx, rfl⟩ := hy
    have hh := hUh i.castSucc x (hUs i.castSucc ⟨hx.1, mem_univ _⟩)
    have hxm := mem_singleton_iff.mp hx.2
    change H (UL i x) < c
    change H (UL i x) = x.2 at hh
    linarith
  have hRband (y : E3) (hy : y ∈ R) (hz : H y ∈ Icc (m - tau) (m + tau)) :
      ∃ i : Fin 2, y ∈ VL i '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ)) := by
    have hh : y ∈ ⋃ i : Fin 2,
        V i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ)) := by
      rw [(hLower (H y) hz).2]
      exact ⟨hR hy, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hh
    exact ⟨e.symm i, by simpa only [VL, e.apply_symm_apply] using hi⟩
  obtain ⟨etaL, boundL, hetaL, hetaLtau, hboundL, hPboundL, hlaterL⟩ :=
    exists_stackNonnestedLowerCapAlignment P UL VL
      (fun i => hU i.castSucc) (fun i => hUi i.castSucc)
      (fun i => hV (e i).castSucc) (fun i => hVi (e i).castSucc)
      u (fun i => hUh i.castSucc) (fun i => hVh (e i).castSucc)
      (fun i => hUs i.castSucc) (fun i => hVs (e i).castSucc)
      m tau htau hboundary hsame hdis R (fun y hy => (hRheight y hy).1)
      hRband WL hWL hUWL
  let OU : Set E3 := {y | c < H y}
  have hOU : IsOpen OU := isOpen_Ioi.preimage H.continuous
  obtain ⟨k, hk, hkrange, hkfix⟩ := exists_saddle_end_height_clamp
    (p - 3 * tau / 4) (p + 3 * tau / 4) (tau / 4) (by linarith) (by positivity)
  have hkI (z : ℝ) : k z ∈ Icc (p - tau) (p + tau) := by
    have hz := hkrange z
    constructor <;> linarith [hz.1, hz.2]
  have hboundaryU (z : ℝ) (hz : z ∈ Icc (p - tau) (p + tau)) :
      (fun x : E2 => U 2 (x, z)) '' sphere 0 1 =
        (fun x : E2 => V 2 (x, z)) '' sphere 0 1 := by
    simpa only [hslice] using (hUpper z hz).1.trans (hUpper z hz).2.symm
  have hcircleOU :
      V 2 '' (sphere (0 : E2) 1 ×ˢ Icc (p - 3 * tau / 4) (p + 3 * tau / 4)) ⊆ OU := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := hVh 2 x (hVs 2 ⟨sphere_subset_closedBall hx.1, mem_univ _⟩)
    change c < H (V 2 x)
    change H (V 2 x) = x.2 at hh
    linarith [hx.2.1]
  obtain ⟨boundU, _hboundU, _hPboundU, hlaterU⟩ :=
    exists_stackOriginalCapAlignment_in_height_band P (U 2) (V 2)
      (hU 2) (hUi 2) (hV 2) (hVi 2) u (hUh 2) (hVh 2) (hUs 2) (hVs 2)
      (Icc (p - tau) (p + tau)) isCompact_Icc hboundaryU k hk hkI
      (p - tau) (p - 3 * tau / 4) (p - tau / 2)
      (p + tau / 2) (p + 3 * tau / 4) (p + tau)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      hkfix OU hOU hcircleOU
  let eta := min etaL (tau / 4) / 2
  let bound := max boundL boundU
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaL' : eta < etaL := by
    have hh := min_le_left etaL (tau / 4)
    dsimp only [eta]
    linarith
  have hetaU : eta < tau / 4 := by
    have hh := min_le_right etaL (tau / 4)
    dsimp only [eta]
    linarith
  have hPb : P.heightBound ≤ bound := hPboundL.trans (le_max_left _ _)
  refine ⟨eta, bound, heta, hetaL'.trans hetaLtau,
    hboundL.trans (le_max_left _ _), hPb, ?_⟩
  intro lambda hlambda hsmall
  dsimp only
  let cut : Fin 3 → ℝ := ![m, m, p]
  let sign : Fin 3 → ℝ := ![1, 1, -1]
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let CU : Fin 3 → Set E3 := fun i => P.capMap (U i) (cut i) (sign i) 0 lambda '' Qminus
  let CV : Fin 3 → Set E3 := fun i => P.capMap (V i) (cut i) (sign i) 0 lambda '' Qminus
  let CLU : Fin 2 → Set E3 := fun i => P.capMap (UL i) m 1 0 lambda '' Qminus
  let CLV : Fin 2 → Set E3 := fun i => P.capMap (VL i) m 1 0 lambda '' Qminus
  have hsmallL : lambda * boundL < etaL :=
    ((mul_le_mul_of_nonneg_left (le_max_left _ _) hlambda.le).trans_lt hsmall).trans hetaL'
  have hsmallU : lambda * boundU < tau / 4 :=
    ((mul_le_mul_of_nonneg_left (le_max_right _ _) hlambda.le).trans_lt hsmall).trans hetaU
  have hsmallP : lambda * P.heightBound < tau :=
    ((mul_le_mul_of_nonneg_left hPb hlambda.le).trans_lt hsmall).trans
      (hetaL'.trans hetaLtau)
  obtain ⟨FL, KL, hFLcap, _hFLall, _hFLallinv, hFLR, hKL, hKLW,
      _hFLsupport, _hFLisupport, hFLfix⟩ :=
    hlaterL (fun _ => lambda) (fun _ => hlambda) (fun _ => hsmallL)
  have hKLheight (y : E3) (hy : y ∈ KL) : H y < c := by
    rcases hKLW hy with hh | hh <;> exact hh.2
  have hupperStack (T : OpenPartialHomeomorph (E2 × ℝ) E3)
      (hTs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
      (hTh : ∀ x ∈ T.source, H (T x) = x.2) :
      T '' (closedBall (0 : E2) 1 ×ˢ Icc (p - tau / 4) (p + tau / 4)) ⊆ OU := by
    rintro _ ⟨x, hx, rfl⟩
    change c < H (T x)
    rw [hTh x (hTs ⟨hx.1, mem_univ _⟩)]
    linarith [hx.2.1]
  obtain ⟨FU, KU, hFUcap, _hFUcapinv, hKU, hKUO, _hFUsupport,
      _hFUisupport, hFUfix, hFUprotected⟩ :=
    hlaterU p (-1) lambda (tau / 4) (by norm_num) hlambda hsmallU
      (by linarith) (by linarith) OU OU hOU hOU
      (hupperStack (U 2) (hUs 2) (hUh 2)) (hupperStack (V 2) (hVs 2) (hVh 2))
  have hKUheight (y : E3) (hy : y ∈ KU) : c < H y := by
    rcases hKUO hy with (hh | hh) | hh
    · exact hh
    · exact hh.1
    · exact hh
  have hFUR (y : E3) (hy : y ∈ R) : FU y = y ∧ FU.symm y = y := by
    apply hFUprotected y ?_ (Or.inl ?_)
    · by_cases hz : H y ∈ Ioo (p - 3 * tau / 4) (p + 3 * tau / 4)
      · have hh : y ∈ V 2 '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ)) := by
          rw [(hUpper (H y) ⟨by linarith [hz.1], by linarith [hz.2]⟩).2]
          exact ⟨hR hy, rfl⟩
        obtain ⟨x, hx, hxy⟩ := hh
        refine Or.inr (Or.inr ⟨x, ⟨hx.1, ?_⟩, hxy⟩)
        rw [mem_singleton_iff.mp hx.2]
        exact ⟨hz.1.le, hz.2.le⟩
      · exact Or.inr (Or.inl hz)
    · have hh := (hRheight y hy).2
      linarith
  have hcapHeight (T : OpenPartialHomeomorph (E2 × ℝ) E3)
      (hTs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
      (hTh : ∀ x ∈ T.source, H (T x) = x.2)
      (s sigma : ℝ) (hsigma : |sigma| = 1) (y : E3)
      (hy : y ∈ P.capMap T s sigma 0 lambda '' Qminus) : |H y - s| < tau := by
    obtain ⟨q, _hq, rfl⟩ := hy
    have hmodel : (P.model q).1 ∈ closedBall (0 : E2) 1 :=
      mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q)
    rw [SurgeryCapProfile.capMap_apply,
      hTh ((P.model q).1, s + sigma * (0 + lambda * (P.model q).2))
        (hTs ⟨hmodel, mem_univ _⟩)]
    simp only [zero_add, add_sub_cancel_left, abs_mul, hsigma, one_mul, abs_of_pos hlambda]
    exact (mul_le_mul_of_nonneg_left (P.height_bound q) hlambda.le).trans_lt hsmallP
  have hupperFix (y : E3) (hy : y ∈ CU 2) : FL y = y := by
    have hh := hcapHeight (U 2) (hUs 2) (hUh 2) p (-1) (by norm_num) y hy
    apply (hFLfix y ?_).1
    intro hyK
    have hhK := hKLheight y hyK
    linarith [(abs_lt.mp hh).1]
  have hlowerFix (i : Fin 2) (y : E3) (hy : y ∈ CLV i) : FU y = y := by
    have hh := hcapHeight (VL i) (hVs (e i).castSucc) (hVh (e i).castSucc)
      m 1 (by norm_num) y hy
    apply (hFUfix y ?_).1
    intro hyK
    have hhK := hKUheight y hyK
    linarith [(abs_lt.mp hh).2]
  have hlowU (i : Fin 2) : CU i.castSucc = CLU i := by fin_cases i <;> rfl
  have hlowV (i : Fin 2) : CV (e i).castSucc = CLV i := by
    dsimp only [CV, CLV, VL]
    have hc : cut (e i).castSucc = m := by generalize e i = j; fin_cases j <;> rfl
    have hs : sign (e i).castSucc = 1 := by generalize e i = j; fin_cases j <;> rfl
    rw [hc, hs]
  let F := FL.trans FU
  have hFcapL (i : Fin 2) : F '' CU i.castSucc = CV (e i).castSucc := by
    simp only [F, Diffeomorph.coe_trans, image_comp]
    rw [hlowU i, (hFLcap i).1, hlowV i]
    exact EqOn.image_eq_self (hlowerFix i)
  have hFcapU : F '' CU 2 = CV 2 := by
    simp only [F, Diffeomorph.coe_trans, image_comp]
    rw [EqOn.image_eq_self hupperFix]
    exact hFUcap
  have hFR (y : E3) (hy : y ∈ R) : F y = y ∧ F.symm y = y := by
    have h0 := hFLR y hy
    have h1 := hFUR y hy
    change FU (FL y) = y ∧ FL.symm (FU.symm y) = y
    rw [h0.1, h1.1, h1.2, h0.2]
    exact ⟨rfl, rfl⟩
  have hthree (A : Fin 3 → Set E3) : (⋃ i : Fin 3, A i) = A 0 ∪ A 1 ∪ A 2 := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      · exact mem_iUnion.mpr ⟨0, h⟩
      · exact mem_iUnion.mpr ⟨1, h⟩
      · exact mem_iUnion.mpr ⟨2, h⟩
  have htwo (A : Fin 2 → Set E3) : (⋃ i : Fin 2, A i) = A 0 ∪ A 1 := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact mem_iUnion.mpr ⟨0, h⟩
      · exact mem_iUnion.mpr ⟨1, h⟩
  have hzero : (0 : Fin 2).castSucc = (0 : Fin 3) := by decide
  have hone : (1 : Fin 2).castSucc = (1 : Fin 3) := by decide
  have htwoV : (⋃ i : Fin 2, CV i.castSucc) = CV 0 ∪ CV 1 := by
    simpa only [hzero, hone] using htwo (fun i => CV i.castSucc)
  have hperm : CV (e 0).castSucc ∪ CV (e 1).castSucc = CV 0 ∪ CV 1 := by
    rw [← htwo (fun i => CV (e i).castSucc), ← htwoV]
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨e i, hi⟩
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi⟩
  have hFimage : F '' (R ∪ ⋃ i : Fin 3, CU i) = R ∪ ⋃ i : Fin 3, CV i := by
    rw [hthree CU, hthree CV, image_union,
      EqOn.image_eq_self (fun y hy => (hFR y hy).1), image_union, image_union]
    have h0 : F '' CU 0 = CV (e 0).castSucc := by simpa only [hzero] using hFcapL 0
    have h1 : F '' CU 1 = CV (e 1).castSucc := by simpa only [hone] using hFcapL 1
    rw [h0, h1, hFcapU, hperm]
  let K := KL ∪ KU
  have hK : IsCompact K := hKL.union hKU
  have hFfix (y : E3) (hy : y ∉ K) : F y = y ∧ F.symm y = y := by
    have h0 := hFLfix y (fun hh => hy (Or.inl hh))
    have h1 := hFUfix y (fun hh => hy (Or.inr hh))
    change FU (FL y) = y ∧ FL.symm (FU.symm y) = y
    rw [h0.1, h1.1, h1.2, h0.2]
    exact ⟨rfl, rfl⟩
  refine ⟨F, K, hFimage, ?_, hFR, hK, ?_, ?_⟩
  · rw [← hFimage]
    exact F.symm_image_image (R ∪ ⋃ i : Fin 3, CU i)
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hFfix y hyK).1)
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hFfix y hyK).2)

end PoincareConjecture.M25.Topology3D
