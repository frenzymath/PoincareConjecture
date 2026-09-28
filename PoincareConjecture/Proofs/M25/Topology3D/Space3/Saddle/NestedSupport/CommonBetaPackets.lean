import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonCapExteriorFilling
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CapNormalAdapter
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.NestedPhysicalPair
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.NestedArcComposition
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

structure CommonBetaPacketInput where
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
  B : Fin 2 → BallNeighborhoodChart E2 E2
  c : Fin 2 → UnitCircle → E2
  K : Fin 2 → Set E2
  O : Fin 2 → Set E2
  T : Fin 2 → Set E2
  Delta : Fin 2 → Set E2
  q : ℝ → UnitCircle
  gamma : ℝ → E2
  Z : OpenPartialHomeomorph UnitCircle ℝ
  N0 : OpenPartialHomeomorph (ℝ × ℝ) E2
  path : ℝ → E2
  d : ℝ
  hl : 0 < l
  hlr : l < r
  hr : r < 1
  heta : 0 < eta
  hetal : eta < l
  hetar : r + eta < 1
  hgap : l + eta < r - eta
  hF : IsClosed F
  hFdecomp : ∀ i, F = K i ∪ O i ∪ T i
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
  hK : ∀ i, IsPreconnected (K i)
  hOutside : ∀ i, ∃ x ∈ K i, x ∉ (B i).closedRegion
  hCurve : ∀ i, range (c i) ⊆ (B i).closedRegion
  hCurveK : ∀ i, Disjoint (range (c i)) (K i)
  hcK : ∀ i, Disjoint (range (c i))
    (kappa '' closedBall (0 : E2) 1)
  hOther : ∀ i, O i ⊆ (B i).closedRegionᶜ
  hTail : ∀ i, T i ⊆ (B i).boundary
  hMeet : ∀ i, range (c i) ∩ T i ⊆ Delta i
  hDelta : ∀ i, Delta i = c 0 ''
    {p : UnitCircle | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  hCCommon : EqOn (c 0) (c 1)
    {p : UnitCircle | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  hZtarget : Z.target = Ioo (-eta) (1 + eta)
  hJcZ : {p : UnitCircle | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ} ⊆ Z.source
  hZ : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ Z Z.source
  hZi : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ Z.symm Z.target
  hCommon : ∀ i p, p ∈ Z.source → c i p = gamma (Z p)
  hN0source : Ioo (-eta) (1 + eta) ×ˢ ({0} : Set ℝ) ⊆ N0.source
  hN0 : ContDiffOn ℝ ∞ N0 N0.source
  hN0i : ContDiffOn ℝ ∞ N0.symm N0.target
  hN0zero : ∀ t ∈ Ioo (-eta) (1 + eta), N0 (t, 0) = gamma t
  hpathC : ContinuousAt path 0
  hpath0 : path 0 = gamma (1 / 2)
  hd : 0 < d
  hpathPreconn : IsPreconnected (path '' Ioc (0 : ℝ) d)
  hpathBoundary : ∀ i, Disjoint (path '' Ioc (0 : ℝ) d) (range (c i))
  hpathEnd : ∀ i, path d ∈ F \ Delta i
  hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ q (Ioo (l - eta) (r + eta))
  hqInj : InjOn q (Ioo (l - eta) (r + eta))
  hqReg : ∀ t ∈ Ioo (l - eta) (r + eta),
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) q t)
  hqImage : q '' Icc l r =
    {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ ≤ (3 / 4 : ℝ)}
  hqEnds : ({q l, q r} : Set UnitCircle) =
    {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ = (3 / 4 : ℝ)}
  hTracks : ∀ i, ∀ t ∈ Ioo (l - eta) (r + eta),
    c i (q t) = alpha i t

structure CommonBetaThreePacketInput where
  packetInput : Fin 3 → CommonBetaPacketInput
  Kcommon : Set E2
  ERef : Set E2
  ETar : Set E2
  hKcommon : ∀ i : Fin 3, Kcommon ⊆ (packetInput i).F
  hBeta : EqOn ((packetInput 0).alpha 1) ((packetInput 2).alpha 1)
    (Icc (0 : ℝ) 1)
  hRefOuter : (packetInput 1).alpha 0 '' Icc (0 : ℝ) 1 ⊆
    (packetInput 0).F
  hTarOuter : (packetInput 1).alpha 1 '' Icc (0 : ℝ) 1 ⊆
    (packetInput 2).F
  hBetaProtected : (packetInput 0).alpha 1 '' Icc (0 : ℝ) 1 ⊆
    (packetInput 1).F
  hRef : ERef =
    (packetInput 0).alpha 0 '' Icc (0 : ℝ) 1 ∪
      (packetInput 1).alpha 0 '' Icc (0 : ℝ) 1
  hTar : ETar =
    (packetInput 2).alpha 0 '' Icc (0 : ℝ) 1 ∪
      (packetInput 1).alpha 1 '' Icc (0 : ℝ) 1

theorem exists_saddle_common_beta_packet
    (hP : PlanarSchoenfliesService) (I : CommonBetaPacketInput) :
    ∃ packet : NestedRelativeArcPacket,
      packet.F = I.F ∧ packet.alpha = I.alpha ∧ packet.kappa = I.kappa := by
  classical
  have hfill (i : Fin 2) :
      ∃ D : BallNeighborhoodChart E2 E2,
        D.boundary = range (I.c i) ∧
        D.closedRegion ⊆ (I.B i).closedRegion ∧
        D.closedRegion ∩ (I.K i ∪ I.O i ∪ I.T i) ⊆ I.Delta i ∧
        IsOpen D.closedRegionᶜ ∧ IsConnected D.closedRegionᶜ ∧
        ¬ Bornology.IsBounded D.closedRegionᶜ ∧
        Disjoint D.closedRegionᶜ (range (I.c i)) ∧
        (I.K i ∪ I.O i ∪ I.T i) \ I.Delta i ⊆ D.closedRegionᶜ := by
    exact exists_saddle_common_cap_exterior_filling hP (I.B i) (I.c i)
      (I.hc i) (I.K i) (I.O i) (I.T i) (I.Delta i) (I.hK i)
      (I.hOutside i) (I.hCurve i) (I.hCurveK i) (I.hOther i)
      (I.hTail i) (I.hMeet i)
  choose D hDb _hDsub hDprotect hWopen hWconn hWunbounded hWcurve hWoutside
    using hfill
  have hpathEndOutside (i : Fin 2) : I.path I.d ∈ (D i).closedRegionᶜ := by
    apply hWoutside i
    have hFmem : I.path I.d ∈ I.K i ∪ I.O i ∪ I.T i := by
      rw [← I.hFdecomp i]
      exact (I.hpathEnd i).1
    exact ⟨hFmem, (I.hpathEnd i).2⟩
  have hpathExterior (i : Fin 2) :
      I.path '' Ioc (0 : ℝ) I.d ⊆ (D i).closedRegionᶜ := by
    have hboundary : Disjoint (I.path '' Ioc (0 : ℝ) I.d) (D i).boundary := by
      rw [hDb i]
      exact I.hpathBoundary i
    rcases (D i).preconnected_subset_inside_or_outside I.hpathPreconn hboundary with
      hinside | houtside
    · exfalso
      apply hpathEndOutside i
      rw [← (D i).inside_union_boundary]
      exact Or.inl (hinside ⟨I.d, ⟨I.hd, le_rfl⟩, rfl⟩)
    · exact houtside
  obtain ⟨Uc, w, N, hUc, hAc, hUcJ, hw, hNsource, hN, hNinv,
      hNzero, hNoldPositive⟩ :=
    exists_saddle_two_circle_positive_normal_collar D I.c I.hc hDb I.v
      I.eta I.heta I.gamma I.Z I.hZtarget I.hJcZ I.hZ I.hZi I.hCommon I.N0
      I.hN0source I.hN0 I.hN0i I.hN0zero I.path I.hpathC I.hpath0 I.d I.hd
      (fun t ht i => hpathExterior i ⟨t, ⟨ht.1, le_of_lt ht.2⟩, rfl⟩)
  have hPacketF : ∀ i, (I.F \ I.Delta i) ⊆ (D i).closedRegionᶜ := by
    intro i x hx
    apply hWoutside i
    rw [I.hFdecomp i] at hx
    exact ⟨hx.1, by simpa only [I.hDelta i] using hx.2⟩
  have hPacketC : ∀ i,
      range (I.c i) ∩ I.F ⊆
        I.c 0 '' {p : UnitCircle | (3 / 4 : ℝ) ≤ ⟪I.v, (p : E2)⟫_ℝ} := by
    intro i x hx
    have hxD : x ∈ (D i).closedRegion := by
      rw [← (D i).inside_union_boundary]
      exact Or.inr (hDb i ▸ hx.1)
    have hxDelta := hDprotect i ⟨hxD, by
      rw [← I.hFdecomp i]
      exact hx.2⟩
    simpa only [I.hDelta i] using hxDelta
  have hNpositive : ∀ i,
      N '' (Uc ×ˢ Ioo (0 : ℝ) w) ⊆ (D i).closedRegionᶜ := by
    intro i x hx hxD
    exact (hNoldPositive i hx) hxD
  let packet : NestedRelativeArcPacket := {
    kappa := I.kappa
    hkappaSource := I.hkappaSource
    hkappa := I.hkappa
    hkappaInv := I.hkappaInv
    alpha := I.alpha
    l := I.l
    r := I.r
    eta := I.eta
    F := I.F
    v := I.v
    c := I.c
    q := I.q
    W := fun i => (D i).closedRegionᶜ
    Uc := Uc
    w := w
    N := N
    hl := I.hl
    hlr := I.hlr
    hr := I.hr
    heta := I.heta
    hetal := I.hetal
    hetar := I.hetar
    hgap := I.hgap
    hF := I.hF
    hKF := I.hKF
    hAlpha := I.hAlpha
    hAlphaInj := I.hAlphaInj
    hAlphaReg := I.hAlphaReg
    hEnds := I.hEnds
    hProper := I.hProper
    hGerms := I.hGerms
    hTails := I.hTails
    hv := I.hv
    hc := I.hc
    hcCommon := I.hCCommon
    hq := I.hq
    hqInj := I.hqInj
    hqReg := I.hqReg
    hqImage := I.hqImage
    hqEnds := I.hqEnds
    hTracks := I.hTracks
    hcK := I.hcK
    hcF := hPacketC
    hWopen := hWopen
    hWconn := hWconn
    hWunbounded := hWunbounded
    hWcurve := hWcurve
    hFW := fun i => by
      intro x hx
      apply hPacketF i
      exact ⟨hx.1, by simpa only [I.hDelta i] using hx.2⟩
    hUc := hUc
    hAc := hAc
    hUcJ := hUcJ
    hw := hw
    hNsource := hNsource
    hN := hN
    hNinv := hNinv
    hNzero := hNzero
    hNpositive := hNpositive
  }
  exact ⟨packet, rfl, rfl, rfl⟩

theorem exists_saddle_common_beta_raw_pair
    (hP : PlanarSchoenfliesService) (I : CommonBetaThreePacketInput) :
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
      I.Kcommon ⊆ CJᶜ ∧
      J 1 '' I.ERef = I.ETar ∧ (J 1).symm '' I.ETar = I.ERef := by
  classical
  have hmake : ∀ i : Fin 3,
      ∃ packet : NestedRelativeArcPacket,
        packet.F = (I.packetInput i).F ∧
        packet.alpha = (I.packetInput i).alpha := by
    intro i
    obtain ⟨packet, hF, hAlpha, _hKappa⟩ :=
      exists_saddle_common_beta_packet hP (I.packetInput i)
    exact ⟨packet, hF, hAlpha⟩
  choose packet hPacketF hPacketAlpha using hmake
  have hKcommon : ∀ i : Fin 3, I.Kcommon ⊆ (packet i).F := by
    intro i
    simpa only [hPacketF i] using I.hKcommon i
  have hBeta : EqOn ((packet 0).alpha 1) ((packet 2).alpha 1)
      (Icc (0 : ℝ) 1) := by
    simpa only [hPacketAlpha 0, hPacketAlpha 2] using I.hBeta
  have hRefOuter : (packet 1).alpha 0 '' Icc (0 : ℝ) 1 ⊆
      (packet 0).F := by
    simpa only [hPacketAlpha 1, hPacketF 0] using I.hRefOuter
  have hTarOuter : (packet 1).alpha 1 '' Icc (0 : ℝ) 1 ⊆
      (packet 2).F := by
    simpa only [hPacketAlpha 1, hPacketF 2] using I.hTarOuter
  have hBetaProtected : (packet 0).alpha 1 '' Icc (0 : ℝ) 1 ⊆
      (packet 1).F := by
    simpa only [hPacketAlpha 0, hPacketF 1] using I.hBetaProtected
  have hRef : I.ERef =
      (packet 0).alpha 0 '' Icc (0 : ℝ) 1 ∪
        (packet 1).alpha 0 '' Icc (0 : ℝ) 1 := by
    simpa only [hPacketAlpha 0, hPacketAlpha 1] using I.hRef
  have hTar : I.ETar =
      (packet 2).alpha 0 '' Icc (0 : ℝ) 1 ∪
        (packet 1).alpha 1 '' Icc (0 : ℝ) 1 := by
    simpa only [hPacketAlpha 2, hPacketAlpha 1] using I.hTar
  exact exists_saddle_nested_pair_of_three_relative_packets hP packet
    I.Kcommon I.ERef I.ETar hKcommon hBeta hRefOuter hTarOuter
    hBetaProtected hRef hTar

end PoincareConjecture.M25.Topology3D
