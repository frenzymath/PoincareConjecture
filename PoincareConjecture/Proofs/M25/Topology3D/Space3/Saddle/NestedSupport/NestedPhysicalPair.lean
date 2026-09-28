import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RelativeExteriorArc
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


structure NestedRelativeArcPacket where
  kappa : OpenPartialHomeomorph E2 E2
  hkappaSource : closedBall (0 : E2) 1 ⊆ kappa.source
  hkappa : ContDiffOn ℝ ∞ kappa kappa.source
  hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target
  alpha : Fin 2 → ℝ → E2
  l : ℝ
  r : ℝ
  eta : ℝ
  F : Set E2
  v : E2
  c : Fin 2 → UnitCircle → E2
  q : ℝ → UnitCircle
  W : Fin 2 → Set E2
  Uc : Set UnitCircle
  w : ℝ
  N : OpenPartialHomeomorph (UnitCircle × ℝ) E2
  hl : 0 < l
  hlr : l < r
  hr : r < 1
  heta : 0 < eta
  hetal : eta < l
  hetar : r + eta < 1
  hgap : l + eta < r - eta
  hF : IsClosed F
  hKF : kappa '' closedBall (0 : E2) 1 ⊆ F
  hAlpha : ∀ i, ContDiffOn ℝ ∞ (alpha i) (Ioo (-eta) (1 + eta))
  hAlphaInj : ∀ i, InjOn (alpha i) (Ioo (-eta) (1 + eta))
  hAlphaReg : ∀ i, ∀ t ∈ Ioo (-eta) (1 + eta), deriv (alpha i) t ≠ 0
  hEnds : ∀ i,
    alpha i 0 ∈ kappa '' sphere (0 : E2) 1 ∧
      alpha i 1 ∈ kappa '' sphere (0 : E2) 1
  hProper : ∀ i, alpha i '' Ioo (0 : ℝ) 1 ⊆
    (kappa '' closedBall (0 : E2) 1)ᶜ
  hGerms : EqOn (alpha 0) (alpha 1)
    (Ioo (-eta) (l + eta) ∪ Ioo (r - eta) (1 + eta))
  hTails : alpha 0 '' (Icc (0 : ℝ) l ∪ Icc r 1) ⊆ F
  hv : ‖v‖ = 1
  hc : ∀ i, IsPlanarEmbedding (c i)
  hcCommon : EqOn (c 0) (c 1)
    {p : UnitCircle | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ q
    (Ioo (l - eta) (r + eta))
  hqInj : InjOn q (Ioo (l - eta) (r + eta))
  hqReg : ∀ t ∈ Ioo (l - eta) (r + eta),
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) q t)
  hqImage : q '' Icc l r =
    {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ ≤ (3 / 4 : ℝ)}
  hqEnds : ({q l, q r} : Set UnitCircle) =
    {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ = (3 / 4 : ℝ)}
  hTracks : ∀ i, ∀ t ∈ Ioo (l - eta) (r + eta), c i (q t) = alpha i t
  hcK : ∀ i, Disjoint (range (c i))
    (kappa '' closedBall (0 : E2) 1)
  hcF : ∀ i, range (c i) ∩ F ⊆
    c 0 '' {p : UnitCircle | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  hWopen : ∀ i, IsOpen (W i)
  hWconn : ∀ i, IsConnected (W i)
  hWunbounded : ∀ i, ¬ Bornology.IsBounded (W i)
  hWcurve : ∀ i, Disjoint (W i) (range (c i))
  hFW : ∀ i, F \ (c 0 ''
    {p : UnitCircle | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}) ⊆ W i
  hUc : IsOpen Uc
  hAc : {p : UnitCircle | (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ} ⊆ Uc
  hUcJ : Uc ⊆ {p : UnitCircle | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  hw : 0 < w
  hNsource : Uc ×ˢ Icc (-w) w ⊆ N.source
  hN : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞ N N.source
  hNinv : ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
    N.symm N.target
  hNzero : ∀ p ∈ Uc, N (p, 0) = c 0 p
  hNpositive : ∀ i, N '' (Uc ×ˢ Ioo (0 : ℝ) w) ⊆ W i

private def nestedPacketDelta (p : NestedRelativeArcPacket) : Set E2 :=
  p.c 0 '' {q : UnitCircle | (3 / 4 : ℝ) ≤ ⟪p.v, (q : E2)⟫_ℝ}

private def nestedPacketK (p : NestedRelativeArcPacket) : Set E2 :=
  p.kappa '' closedBall (0 : E2) 1


theorem exists_saddle_nested_pair_of_relative_packets
    (hP : PlanarSchoenfliesService)
    (packet : Fin 2 → NestedRelativeArcPacket)
    (Kcommon : Set E2)
    (hKcommon : ∀ i : Fin 2, Kcommon ⊆ (packet i).F)
    (hCrossInner :
      (packet 0).alpha 1 '' Icc (0 : ℝ) 1 ⊆ (packet 1).F)
    (hCrossOuter :
      (packet 1).alpha 0 '' Icc (0 : ℝ) 1 ⊆ (packet 0).F)
    (ERef ETar : Set E2)
    (hRef : ERef = ⋃ i : Fin 2,
      (packet i).alpha 0 '' Icc (0 : ℝ) 1)
    (hTar : ETar = ⋃ i : Fin 2,
      (packet i).alpha 1 '' Icc (0 : ℝ) 1) :
    ∃ (C : Set E2)
      (J : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞),
      IsCompact C ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) ∧
      (∀ s : ℝ, s ≤ 0 → ∀ y : E2,
        J s y = y ∧ (J s).symm y = y) ∧
      (∀ s : ℝ, 1 ≤ s → ∀ y : E2,
        J s y = J 1 y ∧ (J s).symm y = (J 1).symm y) ∧
      (∀ s : ℝ,
        tsupport (fun y : E2 => J s y - y) ⊆ C ∧
        tsupport (fun y : E2 => (J s).symm y - y) ⊆ C) ∧
      (∀ s : ℝ, ∀ y : E2, y ∉ C →
        J s y = y ∧ (J s).symm y = y) ∧
      IsOpen Cᶜ ∧
      Kcommon ⊆ Cᶜ ∧
      (∀ i k : Fin 2,
        (packet i).alpha k '' (Icc (0 : ℝ) (packet i).l ∪
          Icc (packet i).r 1) ⊆ Cᶜ) ∧
      (∀ i : Fin 2, ∀ t ∈ Icc (0 : ℝ) 1,
        J 1 ((packet i).alpha 0 t) = (packet i).alpha 1 t ∧
        (J 1).symm ((packet i).alpha 1 t) = (packet i).alpha 0 t) ∧
      (∀ i : Fin 2,
        (J 1) '' ((packet i).alpha 0 '' Icc (0 : ℝ) 1) =
          (packet i).alpha 1 '' Icc (0 : ℝ) 1 ∧
        (J 1).symm '' ((packet i).alpha 1 '' Icc (0 : ℝ) 1) =
          (packet i).alpha 0 '' Icc (0 : ℝ) 1) ∧
      J 1 '' ERef = ETar ∧ (J 1).symm '' ETar = ERef := by
  classical
  have hcall (i : Fin 2) :
      ∃ (C0 : Set E2)
        (H : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
        (rho : ℝ),
        IsCompact C0 ∧
        C0 ⊆ (packet i).Fᶜ \ nestedPacketDelta (packet i) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E2 => H p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E2 => (H p.1).symm p.2) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ y : E2,
          H s y = y ∧ (H s).symm y = y) ∧
        (∀ s : ℝ, 1 ≤ s → ∀ y : E2,
          H s y = H 1 y ∧ (H s).symm y = (H 1).symm y) ∧
        (∀ s : ℝ,
          tsupport (fun y : E2 => H s y - y) ⊆ C0 ∧
          tsupport (fun y : E2 => (H s).symm y - y) ⊆ C0) ∧
        (∀ s : ℝ, ∀ y : E2, y ∉ C0 →
          H s y = y ∧ (H s).symm y = y) ∧
        IsOpen C0ᶜ ∧
        (packet i).F ∪ nestedPacketDelta (packet i) ⊆ C0ᶜ ∧
        0 < rho ∧ rho < (packet i).eta ∧
        (∀ k : Fin 2,
          (packet i).alpha k ''
            (Ioo (-rho) ((packet i).l + rho) ∪
              Ioo ((packet i).r - rho) (1 + rho)) ⊆ C0ᶜ) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          H 1 ((packet i).alpha 0 t) = (packet i).alpha 1 t ∧
          (H 1).symm ((packet i).alpha 1 t) = (packet i).alpha 0 t) ∧
        H 1 '' ((packet i).alpha 0 '' Icc (0 : ℝ) 1) =
          (packet i).alpha 1 '' Icc (0 : ℝ) 1 ∧
        (H 1).symm '' ((packet i).alpha 1 '' Icc (0 : ℝ) 1) =
          (packet i).alpha 0 '' Icc (0 : ℝ) 1 := by
    let p := packet i
    simpa only [nestedPacketDelta] using
      (exists_relative_exterior_arc_isotopy hP p.kappa p.hkappaSource p.hkappa
        p.hkappaInv p.alpha p.l p.r p.eta p.F p.v p.c p.q p.W p.Uc p.w p.N
        p.hl p.hlr p.hr p.heta p.hetal p.hetar p.hgap p.hF p.hKF p.hAlpha
        p.hAlphaInj p.hAlphaReg p.hEnds p.hProper p.hGerms p.hTails p.hv p.hc
        p.hcCommon p.hq p.hqInj p.hqReg p.hqImage p.hqEnds p.hTracks p.hcK
        p.hcF p.hWopen p.hWconn p.hWunbounded p.hWcurve p.hFW p.hUc p.hAc
        p.hUcJ p.hw p.hNsource p.hN p.hNinv p.hNzero p.hNpositive)
  choose C0 H rho hC0 hFree hH hHi hZero hOne hSupport hFix hOpen hCore
    hRho hRhoEta hBuffer hPoint hImage hImageInv using hcall
  let C : Set E2 := C0 0 ∪ C0 1
  have hC : IsCompact C := (hC0 0).union (hC0 1)
  have hCin (i : Fin 2) : C0 i ⊆ C := by
    intro y hy
    fin_cases i
    · exact Or.inl hy
    · exact Or.inr hy
  have hNoC (y : E2) (hy : ∀ i : Fin 2, y ∉ C0 i) : y ∉ C := by
    rintro (hy0 | hy1)
    · exact hy 0 hy0
    · exact hy 1 hy1
  have hCrossFixInner (s : ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      H 1 s ((packet 0).alpha 1 t) = (packet 0).alpha 1 t ∧
      (H 1 s).symm ((packet 0).alpha 1 t) = (packet 0).alpha 1 t := by
    apply hFix 1 s ((packet 0).alpha 1 t)
    intro hCi
    exact (hFree 1 hCi).1 (hCrossInner ⟨t, ht, rfl⟩)
  have hCrossFixOuter (s : ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      H 0 s ((packet 1).alpha 0 t) = (packet 1).alpha 0 t ∧
      (H 0 s).symm ((packet 1).alpha 0 t) = (packet 1).alpha 0 t := by
    apply hFix 0 s ((packet 1).alpha 0 t)
    intro hCi
    exact (hFree 0 hCi).1 (hCrossOuter ⟨t, ht, rfl⟩)
  have hJzero (s : ℝ) (hs : s ≤ 0) (y : E2) :
      ((H 0 s).trans (H 1 s)) y = y ∧
      (((H 0 s).trans (H 1 s)).symm) y = y := by
    constructor
    · change H 1 s (H 0 s y) = y
      rw [(hZero 0 s hs y).1, (hZero 1 s hs y).1]
    · change (H 0 s).symm ((H 1 s).symm y) = y
      rw [(hZero 1 s hs y).2, (hZero 0 s hs y).2]
  let J : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
    fun s => (H 0 s).trans (H 1 s)
  have hJs : ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) := by
    dsimp [J]
    exact (hH 1).comp (contDiff_fst.prodMk (hH 0))
  have hJi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) := by
    dsimp [J]
    exact (hHi 0).comp (contDiff_fst.prodMk (hHi 1))
  have hJfix (s : ℝ) (y : E2) (hy : y ∉ C) :
      J s y = y ∧ (J s).symm y = y := by
    have h0 := hFix 0 s y (fun hy0 => hy (hCin 0 hy0))
    have h1 := hFix 1 s y (fun hy1 => hy (hCin 1 hy1))
    constructor
    · change H 1 s (H 0 s y) = y
      rw [h0.1, h1.1]
    · change (H 0 s).symm ((H 1 s).symm y) = y
      rw [h1.2, h0.2]
  have hJone (s : ℝ) (hs : 1 ≤ s) (y : E2) :
      J s y = J 1 y ∧ (J s).symm y = (J 1).symm y := by
    constructor
    · change H 1 s (H 0 s y) = H 1 1 (H 0 1 y)
      rw [(hOne 0 s hs y).1, (hOne 1 s hs (H 0 1 y)).1]
    · change (H 0 s).symm ((H 1 s).symm y) =
        (H 0 1).symm ((H 1 1).symm y)
      rw [(hOne 1 s hs y).2, (hOne 0 s hs ((H 1 1).symm y)).2]
  have hSupport (s : ℝ) :
      tsupport (fun y : E2 => J s y - y) ⊆ C ∧
      tsupport (fun y : E2 => (J s).symm y - y) ⊆ C := by
    constructor
    · apply closure_minimal ?_ hC.isClosed
      intro y hy
      by_contra hyC
      exact hy (sub_eq_zero.mpr (hJfix s y hyC).1)
    · apply closure_minimal ?_ hC.isClosed
      intro y hy
      by_contra hyC
      exact hy (sub_eq_zero.mpr (hJfix s y hyC).2)
  have hKdisc : Kcommon ⊆ Cᶜ := by
    intro y hy
    apply hNoC
    intro i hyCi
    exact (hFree i hyCi).1 (hKcommon i hy)
  have hTailG (i : Fin 2) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) (packet i).l ∪ Icc (packet i).r 1) :
      t ∈ Ioo (-(packet i).eta) ((packet i).l + (packet i).eta) ∪
        Ioo ((packet i).r - (packet i).eta) (1 + (packet i).eta) := by
    rcases ht with ht | ht
    · exact Or.inl ⟨by linarith [ht.1, (packet i).heta],
        by linarith [ht.2, (packet i).heta]⟩
    · exact Or.inr ⟨by linarith [ht.1, (packet i).heta],
        by linarith [ht.2, (packet i).heta]⟩
  have hTailFs (i k : Fin 2) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) (packet i).l ∪ Icc (packet i).r 1) :
      (packet i).alpha k t ∈ (packet 0).F ∧
        (packet i).alpha k t ∈ (packet 1).F := by
    have hown : (packet i).alpha 0 t ∈ (packet i).F :=
      (packet i).hTails ⟨t, ht, rfl⟩
    have ht01 : t ∈ Icc (0 : ℝ) 1 := by
      rcases ht with ht | ht
      · exact ⟨ht.1, le_trans ht.2 ((packet i).hlr.le.trans (packet i).hr.le)⟩
      · exact ⟨le_trans (packet i).hl.le (packet i).hlr.le |>.trans ht.1, ht.2⟩
    have heq : (packet i).alpha 0 t = (packet i).alpha 1 t :=
      (packet i).hGerms (hTailG i t ht)
    fin_cases i <;> fin_cases k
    · exact ⟨hown, heq ▸ hCrossInner ⟨t, ht01, rfl⟩⟩
    · exact ⟨heq ▸ hown, hCrossInner ⟨t, ht01, rfl⟩⟩
    · exact ⟨hCrossOuter ⟨t, ht01, rfl⟩, hown⟩
    · exact ⟨heq ▸ hCrossOuter ⟨t, ht01, rfl⟩, heq ▸ hown⟩
  have hClosedTails (i k : Fin 2) :
      (packet i).alpha k '' (Icc (0 : ℝ) (packet i).l ∪
        Icc (packet i).r 1) ⊆ Cᶜ := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    apply hNoC
    intro j hj
    fin_cases j
    · exact (hFree 0 hj).1 (hTailFs i k t ht).1
    · exact (hFree 1 hj).1 (hTailFs i k t ht).2
  have hArc (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      J 1 ((packet i).alpha 0 t) = (packet i).alpha 1 t := by
    fin_cases i
    · change H 1 1 (H 0 1 ((packet 0).alpha 0 t)) = (packet 0).alpha 1 t
      rw [(hPoint 0 t ht).1]
      exact (hCrossFixInner 1 t ht).1
    · change H 1 1 (H 0 1 ((packet 1).alpha 0 t)) = (packet 1).alpha 1 t
      rw [(hCrossFixOuter 1 t ht).1]
      exact (hPoint 1 t ht).1
  have hArcInv (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (J 1).symm ((packet i).alpha 1 t) = (packet i).alpha 0 t := by
    rw [← hArc i t ht, (J 1).symm_apply_apply]
  have hArcImage (i : Fin 2) :
      J 1 '' ((packet i).alpha 0 '' Icc (0 : ℝ) 1) =
        (packet i).alpha 1 '' Icc (0 : ℝ) 1 ∧
      (J 1).symm '' ((packet i).alpha 1 '' Icc (0 : ℝ) 1) =
        (packet i).alpha 0 '' Icc (0 : ℝ) 1 := by
    constructor
    · rw [← image_comp]
      exact image_congr (fun t ht => hArc i t ht)
    · rw [← image_comp]
      exact image_congr (fun t ht => hArcInv i t ht)
  have hJimage : J 1 '' ERef = ETar := by
    rw [hRef, hTar, image_iUnion]
    apply iUnion_congr
    intro i
    exact (hArcImage i).1
  have hJimageInv : (J 1).symm '' ETar = ERef := by
    rw [hTar, hRef, image_iUnion]
    apply iUnion_congr
    intro i
    exact (hArcImage i).2
  refine ⟨C, J, hC, hJs, hJi, hJzero, hJone, hSupport, hJfix,
    hC.isClosed.isOpen_compl, hKdisc, hClosedTails, ?_, ?_, hJimage,
    hJimageInv⟩
  · intro i t ht
    exact ⟨hArc i t ht, hArcInv i t ht⟩
  · intro i
    exact hArcImage i






theorem exists_saddle_nested_pair_raw_output
    (hP : PlanarSchoenfliesService)
    (packet : Fin 2 → NestedRelativeArcPacket)
    (Kcommon : Set E2)
    (hKcommon : ∀ i : Fin 2, Kcommon ⊆ (packet i).F)
    (hCrossInner :
      (packet 0).alpha 1 '' Icc (0 : ℝ) 1 ⊆ (packet 1).F)
    (hCrossOuter :
      (packet 1).alpha 0 '' Icc (0 : ℝ) 1 ⊆ (packet 0).F)
    (ERef ETar : Set E2)
    (hRef : ERef = ⋃ i : Fin 2,
      (packet i).alpha 0 '' Icc (0 : ℝ) 1)
    (hTar : ETar = ⋃ i : Fin 2,
      (packet i).alpha 1 '' Icc (0 : ℝ) 1) :
    ∃ (J : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (CJ : Set E2), IsCompact CJ ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) ∧
      (∀ s : ℝ, s ≤ 0 → ∀ y : E2,
        J s y = y ∧ (J s).symm y = y) ∧
      (∀ s : ℝ, 1 ≤ s → ∀ y : E2,
        J s y = J 1 y ∧ (J s).symm y = (J 1).symm y) ∧
      (∀ s : ℝ,
        tsupport (fun y : E2 => J s y - y) ⊆ CJ ∧
        tsupport (fun y : E2 => (J s).symm y - y) ⊆ CJ) ∧
      Kcommon ⊆ CJᶜ ∧
      J 1 '' ERef = ETar ∧ (J 1).symm '' ETar = ERef := by
  obtain ⟨C, J, hC, hJ, hJinv, hJzero, hJone, hJsupport, _hJfix,
      _hCopen, hK, _hTails, _hPointwise, _hImages, hImage, hImageInv⟩ :=
    exists_saddle_nested_pair_of_relative_packets hP packet Kcommon hKcommon
      hCrossInner hCrossOuter ERef ETar hRef hTar
  exact ⟨J, C, hC, hJ, hJinv, hJzero, hJone, hJsupport, hK,
    hImage, hImageInv⟩

end PoincareConjecture.M25.Topology3D
