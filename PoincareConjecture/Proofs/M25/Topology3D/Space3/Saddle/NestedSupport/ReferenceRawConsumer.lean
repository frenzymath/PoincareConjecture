import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.ReferenceLanePacket
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.NativeLevelGeometry

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

structure ReferenceRawConsumerData
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (La V Dc : Set UnitTwoSphere) (p : Fin 4 → UnitTwoSphere)
    (j : UnitTwoSphere → E3) (T : D3) (Ext Rim : Set E3)
    (L : E3 ≃L[ℝ] (E2 × ℝ)) (g : D2) (c : ℝ)
    (labelTar : Equiv.Perm (Fin 2)) (iTarget : Fin 2)
    (muRef muTar rho delta : ℝ)
    (sx sy : Fin 4 → ℝ) where
  iPos : Fin 2
  sigma : ℝ
  hsigma : sigma = 1 ∨ sigma = -1
  hSigma : sigma = if iPos = labelTar.symm iTarget then 1 else -1
  labelRef : Fin 2 ≃ Fin 2
  aRef : Fin 2 → ℝ
  vRef : Fin 2 → ℝ
  etaRef : ℝ
  alphaLow : Fin 2 → ℝ → UnitTwoSphere
  hAlphaDef : ∀ i t, alphaLow i t =
    q (labelRef i) (complexUnitCircleHomeomorph (Circle.exp (aRef i + vRef i * t)))
  hCompact : ∀ i : Fin 2,
    IsCompact (range (q i)) ∧ IsCompact (La \ range (q i))
  hp : Function.Injective p
  heta : 0 < etaRef
  hetaSmall : etaRef < 1 / 8
  hArc : ∀ i : Fin 2,
    0 < |vRef i| ∧ |vRef i| < 2 * Real.pi ∧
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (alphaLow i) ∧
    (∀ t : ℝ, Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (alphaLow i) t)) ∧
    Set.InjOn (alphaLow i) (Icc (-etaRef) (1 + etaRef)) ∧
    alphaLow i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
    alphaLow i 1 = p (finProdFinEquiv (i, (1 : Fin 2))) ∧
    Disjoint (alphaLow i '' Ioo (0 : ℝ) 1) Dc ∧
    (alphaLow i '' Icc (0 : ℝ) 1) ∩ Dc =
      {p (finProdFinEquiv (i, (0 : Fin 2))),
       p (finProdFinEquiv (i, (1 : Fin 2)))} ∧
    (∀ s ∈ Ioo (-etaRef) (0 : ℝ), alphaLow i s ∈ V) ∧
    (∀ s ∈ Ioo (1 : ℝ) (1 + etaRef), alphaLow i s ∈ V)
  hDisjoint : Disjoint (alphaLow 0 '' Icc (-etaRef) (1 + etaRef))
    (alphaLow 1 '' Icc (-etaRef) (1 + etaRef))
  hSourceUnion : La \ V = ⋃ i : Fin 2, alphaLow i '' Icc (0 : ℝ) 1
  hSourceRim : La ∩ (Dc \ V) = range p
  hLabel : labelRef.symm 0 = labelTar.symm iTarget
  alphaE : Fin 2 → ℝ → E3
  hAlphaE : ∀ i t, alphaE i t = T (j (alphaLow i t))
  hTransport :
    (⋃ i : Fin 2, alphaE i '' Icc (0 : ℝ) 1) = Ext ∧
    T.symm '' Ext = j '' (La \ V) ∧
    T '' (j '' (La ∩ (Dc \ V))) = Rim ∧
    T.symm '' Rim = j '' (range p)
  hPhysicalNormalized :
    (g '' {x : E2 | L.symm (g x, c) ∈ Ext} =
      ⋃ i : Fin 2, (fun t => (L (alphaE i t)).1) '' Icc (0 : ℝ) 1) ∧
    ({x : E2 | L.symm (g x, c) ∈ Ext} =
      ⋃ i : Fin 2, (fun t => g.symm ((L (alphaE i t)).1)) '' Icc (0 : ℝ) 1)
  X : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)
  hEndpoint : ∀ i : Fin 4,
    (X i).source = Ioo (-2 * delta) (2 * delta) ×ˢ
      Ioo (-(1 / 8 : ℝ)) (1 / 8) ∧
    (X i).target ⊆ {v : ℝ × ℝ |
      0 < sigma * sy i * v.1 ∧ 0 < sigma * sx i * v.2} ∧
    ContDiffOn ℝ ∞ (X i)
      (Ioo (-2 * delta) (2 * delta) ×ˢ Ioo (-(1 / 8 : ℝ)) (1 / 8)) ∧
    ContDiffOn ℝ ∞ (X i).symm (X i).target ∧
    (∀ p ∈ Ioo (-2 * delta) (2 * delta) ×ˢ
        Ioo (-(1 / 8 : ℝ)) (1 / 8),
      (X i) p =
        (sigma * sy i * Real.sqrt
            ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2),
          sigma * sx i * Real.sqrt
            ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2))) ∧
    (∀ v : ℝ × ℝ, (X i).symm v =
      (-v.1 ^ 2 + v.2 ^ 2,
        Real.sqrt (v.1 ^ 2 + v.2 ^ 2) / rho - 1)) ∧
    (∀ p ∈ Ioo (-2 * delta) (2 * delta) ×ˢ
        Ioo (-(1 / 8 : ℝ)) (1 / 8),
      ((X i) p).1 ^ 2 + ((X i) p).2 ^ 2 =
          rho ^ 2 * (1 + p.2) ^ 2 ∧
      -((X i) p).1 ^ 2 + ((X i) p).2 ^ 2 = p.1)
  hmuRef : 0 < muRef
  hmuTar : 0 < muTar
  hmuDistinct : muRef ≠ muTar

theorem exists_reference_raw_consumer_data
    (ws wm d rho delta : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32))
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta < rho ^ 2)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (j : UnitTwoSphere → E3) (k : ℝ)
    (La Lb V Dc : Set UnitTwoSphere)
    (hj : j = (fun q : UnitTwoSphere => nestedReferenceDiffeomorph d (q : E3)))
    (hLa : La = {q : UnitTwoSphere |
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
        k + d - delta})
    (hLb : Lb = {q : UnitTwoSphere |
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
        k + d + delta})
    (hV : V = e.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2})
    (hDc : Dc = e.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2})
    (hk : k = 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32)
    (hbuffer : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} ⊆ e.target)
    (hheight : ∀ q ∈ e.source,
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
        k + d - (e q).1 ^ 2 + (e q).2 ^ 2)
    (hupper : k + delta <
      1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32)
    (hVopen : IsOpen V) (hDcCompact : IsCompact Dc)
    (T : D3)
    (hExterior : T '' (j '' (La \ V)) = j '' (Lb \ V))
    (hExteriorInv : T.symm '' (j '' (Lb \ V)) = j '' (La \ V))
    (hRim : T '' (j '' (La ∩ (Dc \ V))) = j '' (Lb ∩ (Dc \ V)))
    (hRimInv : T.symm '' (j '' (Lb ∩ (Dc \ V))) =
      j '' (La ∩ (Dc \ V)))
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (hq : ∀ i : Fin 2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
      ∀ theta : UnitCircle,
        Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta))
    (hqd : ∀ i l : Fin 2, i ≠ l →
      Disjoint (range (q i)) (range (q l)))
    (hLevel : (⋃ i : Fin 2, range (q i)) = La)
    (labelTar : Equiv.Perm (Fin 2)) (iTarget : Fin 2)
    (L : E3 ≃L[ℝ] (E2 × ℝ)) (g : D2) (c : ℝ)
    (Ext Rim : Set E3) (hExt : Ext = j '' (Lb \ V))
    (hRimSet : Rim = j '' (Lb ∩ (Dc \ V)))
    (hHorizontal : ∀ y ∈ Ext, (L y).2 = c)
    (muRef muTar : ℝ) (hmuRef : 0 < muRef) (hmuTar : 0 < muTar)
    (hmuDistinct : muRef ≠ muTar)
    (hdeltaSmall : delta ≤ rho ^ 2 / 128)
    (sx sy : Fin 4 → ℝ)
    (hsx : ∀ i : Fin 4, (sx i) ^ 2 = 1)
    (hsy : ∀ i : Fin 4, (sy i) ^ 2 = 1) :
    ∃ p : Fin 4 → UnitTwoSphere,
      Nonempty (ReferenceRawConsumerData q La V Dc p j T Ext Rim L g c
        labelTar iTarget muRef muTar rho delta sx sy) := by
  classical
  have hheight' : ∀ q ∈ e.source,
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
        k + d - (e q).1 ^ 2 + (e q).2 ^ 2 := hheight
  have hNoBypass : ∀ B : Set UnitTwoSphere, B ⊆ La → IsCompact B →
      IsCompact (La \ B) → Disjoint B Dc → B = ∅ := by
    have hNB := reference_native_no_bypass_of_retained_roots
      ws wm d rho delta hwslo hwshi hwsroot hwmlo hwmhi hwmroot
      hrho hdelta hsmall e T
    dsimp only at hNB
    intro B hB hBcompact hBrest hBDc
    have hNBD := hNB hbuffer
      (by simpa only [hk] using hheight')
      (by simpa only [hk] using hupper)
      (by simpa only [hV] using hVopen)
      (by simpa only [hDc] using hDcCompact)
      (by simpa only [hj, hLa, hLb, hV, hk] using hExterior)
      (by simpa only [hj, hLa, hLb, hV, hDc, hk] using hRim)
    exact hNBD B (by simpa only [hLa, hk] using hB) hBcompact
      (by simpa only [hLa, hk] using hBrest) (by simpa only [hDc] using hBDc)
  let iTar : Fin 2 := labelTar.symm iTarget
  have hSelected := exists_reference_lane_selected_sign_parent
    e k d rho delta hrho hdelta hsmall hbuffer hheight' q
      (fun i => (hq i).1.continuous) (hqd 0 1 (by decide))
      iTar
  dsimp only at hSelected
  have hSelected' := hSelected (by simpa only [hLa] using hLevel)
    (by simpa only [hLa, hDc] using hNoBypass)
  obtain ⟨iPos, sigma, _, _, hsigma, hSigma, hSelectedParent⟩ := hSelected'
  have hConnector := saddle_nested_reference_lower_connectors
    e k d rho delta sigma hrho hdelta hsmall hsigma hbuffer hheight'
  dsimp only at hConnector
  let aa : ℝ := Real.sqrt ((rho ^ 2 - delta) / 2)
  let bb : ℝ := Real.sqrt ((rho ^ 2 + delta) / 2)
  let sg : Fin 2 → ℝ := ![1, -1]
  let sx0 : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy0 : Fin 4 → ℝ := ![1, 1, -1, -1]
  let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t =>
    e.symm (sigma * sg i * Real.sqrt ((vv t) ^ 2 + delta),
      sigma * sg i * vv t)
  let p : Fin 4 → UnitTwoSphere := fun i =>
    e.symm (sigma * sy0 i * bb, sigma * sx0 i * aa)
  have hConnector' :
      (∀ i : Fin 2, Continuous (gamma i) ∧ Function.Injective (gamma i)) ∧
      Disjoint (range (gamma 0)) (range (gamma 1)) ∧
      (∀ i : Fin 2,
        gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
        gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2)))) ∧
      La ∩ Dc = ⋃ i : Fin 2, range (gamma i) ∧
      La ∩ V = ⋃ i : Fin 2, gamma i '' Ioo (0 : unitInterval) 1 := by
    simpa only [gamma, p, aa, bb, sg, sx0, sy0, vv, hLa, hV, hDc,
      mul_assoc] using hConnector
  obtain ⟨hgamma, hgdisjoint, hend, hclosed, hopen⟩ := hConnector'
  have hParent : range (gamma iTar) ⊆ range (q 0) := by
    simpa only [gamma, aa, sg, vv, hLa, hV, hDc, mul_assoc] using hSelectedParent
  obtain ⟨labelRef, aRef, vRef, etaRef, hSource⟩ :=
    exists_reference_lane_source_arcs sigma hsigma iTar q hq hqd gamma
      hgamma hgdisjoint p hend La V Dc (by simpa only [hLa] using hLevel)
      hclosed hopen hNoBypass hParent
  dsimp only at hSource
  obtain ⟨hCompact, hp, heta, hetaSmall, _, hArc, hDisjoint,
    hSourceUnion, hSourceRim, _, hLabel⟩ := hSource
  let alphaLow : Fin 2 → ℝ → UnitTwoSphere := fun i t =>
    q (labelRef i) (complexUnitCircleHomeomorph (Circle.exp (aRef i + vRef i * t)))
  let alphaE : Fin 2 → ℝ → E3 := fun i t => T (j (alphaLow i t))
  have hjinj : Function.Injective j := by
    rw [hj]
    exact (nestedReferenceDiffeomorph d).injective.comp Subtype.val_injective
  have hExterior' : T '' (j '' (La \ V)) = Ext := hExterior.trans hExt.symm
  have hExteriorInv' : T.symm '' Ext = j '' (La \ V) := by
    rw [hExt]
    exact hExteriorInv
  have hRim' : T '' (j '' (La ∩ (Dc \ V))) = Rim :=
    hRim.trans hRimSet.symm
  have hRimInv' : T.symm '' Rim = j '' (La ∩ (Dc \ V)) := by
    rw [hRimSet]
    exact hRimInv
  have hTransport := reference_lane_transport_unions j hjinj T alphaLow La V Dc p Ext Rim
    hSourceUnion hSourceRim hExterior' hExteriorInv' hRim' hRimInv'
  dsimp only at hTransport
  obtain ⟨hForward, hInverse, hRimForward, hRimInverse⟩ := hTransport
  have hPhysical := reference_lane_physical_normalized_unions
    L g c alphaE Ext hHorizontal (by simpa only [alphaE] using hForward.symm)
  dsimp only at hPhysical
  obtain ⟨hPhys, hNorm⟩ := hPhysical
  obtain ⟨X, hX⟩ := exists_reference_signed_endpoint_source_charts
    rho delta hrho hdelta hdeltaSmall sigma hsigma sx sy hsx hsy
  refine ⟨p, ⟨{
    iPos := iPos, sigma := sigma, hsigma := hsigma,
    hSigma := by simpa only [iTar] using hSigma,
    labelRef := labelRef, aRef := aRef, vRef := vRef, etaRef := etaRef,
    alphaLow := alphaLow, hAlphaDef := by intro i t; rfl,
    hCompact := hCompact, hp := hp, heta := heta, hetaSmall := hetaSmall,
    hArc := by simpa only [alphaLow] using hArc,
    hDisjoint := by simpa only [alphaLow] using hDisjoint,
    hSourceUnion := by simpa only [alphaLow] using hSourceUnion,
    hSourceRim := hSourceRim, hLabel := by simpa only [iTar] using hLabel,
    alphaE := alphaE, hAlphaE := by intro i t; rfl,
    hTransport := ⟨hForward, hInverse, hRimForward, hRimInverse⟩,
    hPhysicalNormalized := ⟨hPhys, hNorm⟩,
    X := X, hEndpoint := hX,
    hmuRef := hmuRef, hmuTar := hmuTar, hmuDistinct := hmuDistinct
  }⟩⟩

end PoincareConjecture.M25.Topology3D
