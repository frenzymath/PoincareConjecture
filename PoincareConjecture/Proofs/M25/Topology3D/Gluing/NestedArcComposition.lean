import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.NestedPhysicalPair

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_nested_pair_of_three_relative_packets
    (hP : PlanarSchoenfliesService)
    (packet : Fin 3 -> NestedRelativeArcPacket)
    (Kcommon ERef ETar : Set E2)
    (hKcommon : forall i : Fin 3, Kcommon ⊆ (packet i).F)
    (hBeta : EqOn ((packet 0).alpha 1) ((packet 2).alpha 1)
      (Icc (0 : ℝ) 1))
    (hRefOuter : (packet 1).alpha 0 '' Icc (0 : ℝ) 1 ⊆ (packet 0).F)
    (hTarOuter : (packet 1).alpha 1 '' Icc (0 : ℝ) 1 ⊆ (packet 2).F)
    (hBetaProtected : (packet 0).alpha 1 '' Icc (0 : ℝ) 1 ⊆ (packet 1).F)
    (hRef : ERef =
      (packet 0).alpha 0 '' Icc (0 : ℝ) 1 ∪
        (packet 1).alpha 0 '' Icc (0 : ℝ) 1)
    (hTar : ETar =
      (packet 2).alpha 0 '' Icc (0 : ℝ) 1 ∪
        (packet 1).alpha 1 '' Icc (0 : ℝ) 1) :
    ∃ (J : ℝ -> Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (CJ : Set E2), IsCompact CJ ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) ∧
      (forall s : ℝ, s ≤ 0 -> forall y : E2,
        J s y = y ∧ (J s).symm y = y) ∧
      (forall s : ℝ, 1 ≤ s -> forall y : E2,
        J s y = J 1 y ∧ (J s).symm y = (J 1).symm y) ∧
      (forall s : ℝ,
        tsupport (fun y : E2 => J s y - y) ⊆ CJ ∧
        tsupport (fun y : E2 => (J s).symm y - y) ⊆ CJ) ∧
      Kcommon ⊆ CJᶜ ∧
      J 1 '' ERef = ETar ∧ (J 1).symm '' ETar = ERef := by
  classical
  have hcall (i : Fin 3) :
      ∃ (C : Set E2)
        (H : ℝ -> Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞),
        IsCompact C ∧ C ⊆ (packet i).Fᶜ ∧
        ContDiff ℝ ∞ (fun p : ℝ × E2 => H p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E2 => (H p.1).symm p.2) ∧
        (forall s : ℝ, s ≤ 0 -> forall y : E2,
          H s y = y ∧ (H s).symm y = y) ∧
        (forall s : ℝ, 1 ≤ s -> forall y : E2,
          H s y = H 1 y ∧ (H s).symm y = (H 1).symm y) ∧
        (forall s : ℝ, forall y : E2, y ∉ C ->
          H s y = y ∧ (H s).symm y = y) ∧
        forall t : ℝ, t ∈ Icc (0 : ℝ) 1 ->
          H 1 ((packet i).alpha 0 t) = (packet i).alpha 1 t ∧
          (H 1).symm ((packet i).alpha 1 t) = (packet i).alpha 0 t := by
    let p := packet i
    obtain ⟨C, H, _rho, hC, hFree, hH, hHi, hZero, hOne, _hSupport,
        hFix, _hOpen, _hProtected, _hRho, _hRhoEta, _hBuffer, hPoint,
        _hImage, _hImageInv⟩ :=
      exists_relative_exterior_arc_isotopy hP p.kappa p.hkappaSource p.hkappa
        p.hkappaInv p.alpha p.l p.r p.eta p.F p.v p.c p.q p.W p.Uc p.w p.N
        p.hl p.hlr p.hr p.heta p.hetal p.hetar p.hgap p.hF p.hKF p.hAlpha
        p.hAlphaInj p.hAlphaReg p.hEnds p.hProper p.hGerms p.hTails p.hv p.hc
        p.hcCommon p.hq p.hqInj p.hqReg p.hqImage p.hqEnds p.hTracks p.hcK
        p.hcF p.hWopen p.hWconn p.hWunbounded p.hWcurve p.hFW p.hUc p.hAc
        p.hUcJ p.hw p.hNsource p.hN p.hNinv p.hNzero p.hNpositive
    exact ⟨C, H, hC, fun _ hy => (hFree hy).1, hH, hHi, hZero, hOne,
      hFix, hPoint⟩
  choose C H hC hFree hH hHi hZero hOne hFix hPoint using hcall
  let CJ : Set E2 := (C 0 ∪ C 1) ∪ C 2
  have hCJ : IsCompact CJ := ((hC 0).union (hC 1)).union (hC 2)
  have hAvoid (i : Fin 3) (y : E2) (hy : y ∉ CJ) : y ∉ C i := by
    intro hi
    apply hy
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  have hProtected (i : Fin 3) (s : ℝ) (y : E2) (hy : y ∈ (packet i).F) :
      H i s y = y ∧ (H i s).symm y = y :=
    hFix i s y (fun hi => hFree i hi hy)
  let J : ℝ -> Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
    fun s => ((H 0 s).trans (H 1 s)).trans (H 2 s).symm
  have hJs : ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) := by
    dsimp [J]
    exact (hHi 2).comp
      (contDiff_fst.prodMk ((hH 1).comp (contDiff_fst.prodMk (hH 0))))
  have hJi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) := by
    dsimp [J]
    exact (hHi 0).comp
      (contDiff_fst.prodMk ((hHi 1).comp (contDiff_fst.prodMk (hH 2))))
  have hJfix (s : ℝ) (y : E2) (hy : y ∉ CJ) :
      J s y = y ∧ (J s).symm y = y := by
    have h0 := hFix 0 s y (hAvoid 0 y hy)
    have h1 := hFix 1 s y (hAvoid 1 y hy)
    have h2 := hFix 2 s y (hAvoid 2 y hy)
    constructor
    · change (H 2 s).symm (H 1 s (H 0 s y)) = y
      rw [h0.1, h1.1, h2.2]
    · change (H 0 s).symm ((H 1 s).symm (H 2 s y)) = y
      rw [h2.1, h1.2, h0.2]
  have hJzero (s : ℝ) (hs : s ≤ 0) (y : E2) :
      J s y = y ∧ (J s).symm y = y := by
    constructor
    · change (H 2 s).symm (H 1 s (H 0 s y)) = y
      rw [(hZero 0 s hs y).1, (hZero 1 s hs y).1, (hZero 2 s hs y).2]
    · change (H 0 s).symm ((H 1 s).symm (H 2 s y)) = y
      rw [(hZero 2 s hs y).1, (hZero 1 s hs y).2, (hZero 0 s hs y).2]
  have hJone (s : ℝ) (hs : 1 ≤ s) (y : E2) :
      J s y = J 1 y ∧ (J s).symm y = (J 1).symm y := by
    constructor
    · change (H 2 s).symm (H 1 s (H 0 s y)) =
        (H 2 1).symm (H 1 1 (H 0 1 y))
      rw [(hOne 0 s hs y).1, (hOne 1 s hs (H 0 1 y)).1,
        (hOne 2 s hs (H 1 1 (H 0 1 y))).2]
    · change (H 0 s).symm ((H 1 s).symm (H 2 s y)) =
        (H 0 1).symm ((H 1 1).symm (H 2 1 y))
      rw [(hOne 2 s hs y).1, (hOne 1 s hs (H 2 1 y)).2,
        (hOne 0 s hs ((H 1 1).symm (H 2 1 y))).2]
  have hSupport (s : ℝ) :
      tsupport (fun y : E2 => J s y - y) ⊆ CJ ∧
      tsupport (fun y : E2 => (J s).symm y - y) ⊆ CJ := by
    constructor
    · apply closure_minimal ?_ hCJ.isClosed
      intro y hy
      by_contra hyC
      exact hy (sub_eq_zero.mpr (hJfix s y hyC).1)
    · apply closure_minimal ?_ hCJ.isClosed
      intro y hy
      by_contra hyC
      exact hy (sub_eq_zero.mpr (hJfix s y hyC).2)
  have hK : Kcommon ⊆ CJᶜ := by
    intro y hy hmem
    rcases hmem with (h0 | h1) | h2
    · exact hFree 0 h0 (hKcommon 0 hy)
    · exact hFree 1 h1 (hKcommon 1 hy)
    · exact hFree 2 h2 (hKcommon 2 hy)
  have hInner (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      J 1 ((packet 0).alpha 0 t) = (packet 2).alpha 0 t := by
    change (H 2 1).symm (H 1 1 (H 0 1 ((packet 0).alpha 0 t))) = _
    rw [(hPoint 0 t ht).1,
      (hProtected 1 1 _ (hBetaProtected ⟨t, ht, rfl⟩)).1,
      hBeta ht, (hPoint 2 t ht).2]
  have hOuter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      J 1 ((packet 1).alpha 0 t) = (packet 1).alpha 1 t := by
    change (H 2 1).symm (H 1 1 (H 0 1 ((packet 1).alpha 0 t))) = _
    rw [(hProtected 0 1 _ (hRefOuter ⟨t, ht, rfl⟩)).1,
      (hPoint 1 t ht).1, (hProtected 2 1 _ (hTarOuter ⟨t, ht, rfl⟩)).2]
  have hInnerInv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (J 1).symm ((packet 2).alpha 0 t) = (packet 0).alpha 0 t := by
    rw [← hInner t ht, (J 1).symm_apply_apply]
  have hOuterInv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (J 1).symm ((packet 1).alpha 1 t) = (packet 1).alpha 0 t := by
    rw [← hOuter t ht, (J 1).symm_apply_apply]
  have hInnerImage : J 1 '' ((packet 0).alpha 0 '' Icc (0 : ℝ) 1) =
      (packet 2).alpha 0 '' Icc (0 : ℝ) 1 := by
    rw [← image_comp]
    exact image_congr hInner
  have hOuterImage : J 1 '' ((packet 1).alpha 0 '' Icc (0 : ℝ) 1) =
      (packet 1).alpha 1 '' Icc (0 : ℝ) 1 := by
    rw [← image_comp]
    exact image_congr hOuter
  have hInnerImageInv : (J 1).symm '' ((packet 2).alpha 0 '' Icc (0 : ℝ) 1) =
      (packet 0).alpha 0 '' Icc (0 : ℝ) 1 := by
    rw [← image_comp]
    exact image_congr hInnerInv
  have hOuterImageInv : (J 1).symm '' ((packet 1).alpha 1 '' Icc (0 : ℝ) 1) =
      (packet 1).alpha 0 '' Icc (0 : ℝ) 1 := by
    rw [← image_comp]
    exact image_congr hOuterInv
  refine ⟨J, CJ, hCJ, hJs, hJi, hJzero, hJone, hSupport, hK, ?_, ?_⟩
  · rw [hRef, hTar, image_union, hInnerImage, hOuterImage]
  · rw [hTar, hRef, image_union, hInnerImageInv, hOuterImageInv]

end PoincareConjecture.M25.Topology3D
