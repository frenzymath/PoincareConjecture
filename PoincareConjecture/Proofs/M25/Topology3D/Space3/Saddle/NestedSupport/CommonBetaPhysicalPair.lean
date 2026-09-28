import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CommonBetaPackets
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.NestedCommonMiddleAssembly
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.MiddleExteriorCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.NestedPairFilledSidesCore
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CommonBetaSharedTemplates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CommonBetaOuterInputs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.CommonBetaInnerInputs














set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



private theorem commonBeta_pack_original_arcs
    (kappa : OpenPartialHomeomorph E2 E2)
    (alpha : Fin 2 → Fin 2 → ℝ → E2) (beta : ℝ → E2)
    (inner : Fin 2) (h : ℝ)
    (Iinner : Fin 2 → CommonBetaPacketInput) (Iouter : CommonBetaPacketInput)
    (hInnerAlpha : ∀ j, (Iinner j).alpha = ![alpha j inner, beta])
    (hInnerF : ∀ j, (Iinner j).F =
      (kappa '' closedBall (0 : E2) 1) ∪
        alpha j (Equiv.swap (0 : Fin 2) 1 inner) '' Icc (0 : ℝ) 1 ∪
        alpha j inner '' (Icc (0 : ℝ) (3 * h) ∪ Icc (1 - 3 * h) 1))
    (hOuterAlpha : Iouter.alpha = fun j => alpha j (Equiv.swap (0 : Fin 2) 1 inner))
    (hOuterF : Iouter.F =
      ((kappa '' closedBall (0 : E2) 1) ∪ beta '' Icc (0 : ℝ) 1) ∪
        alpha 0 (Equiv.swap (0 : Fin 2) 1 inner) ''
          (Icc (0 : ℝ) (3 * h) ∪ Icc (1 - 3 * h) 1) ∪
        alpha 1 (Equiv.swap (0 : Fin 2) 1 inner) ''
          (Icc (0 : ℝ) (3 * h) ∪ Icc (1 - 3 * h) 1)) :
    ∃ I : CommonBetaThreePacketInput,
      I.Kcommon = kappa '' closedBall (0 : E2) 1 ∧
      I.ERef = (⋃ i : Fin 2, alpha 0 i '' Icc (0 : ℝ) 1) ∧
      I.ETar = (⋃ i : Fin 2, alpha 1 i '' Icc (0 : ℝ) 1) := by
  let packet : Fin 3 → CommonBetaPacketInput := ![Iinner 0, Iouter, Iinner 1]
  have hK (i : Fin 3) : kappa '' closedBall (0 : E2) 1 ⊆ (packet i).F := by
    fin_cases i
    · change _ ⊆ (Iinner 0).F
      rw [hInnerF 0]
      exact fun _ hx => Or.inl (Or.inl hx)
    · change _ ⊆ Iouter.F
      rw [hOuterF]
      exact fun _ hx => Or.inl (Or.inl (Or.inl hx))
    · change _ ⊆ (Iinner 1).F
      rw [hInnerF 1]
      exact fun _ hx => Or.inl (Or.inl hx)
  have hBeta : EqOn ((packet 0).alpha 1) ((packet 2).alpha 1)
      (Icc (0 : ℝ) 1) := by
    change EqOn ((Iinner 0).alpha 1) ((Iinner 1).alpha 1) _
    rw [hInnerAlpha 0, hInnerAlpha 1]
    exact fun _ _ => rfl
  have hRefOuter : (packet 1).alpha 0 '' Icc (0 : ℝ) 1 ⊆ (packet 0).F := by
    change Iouter.alpha 0 '' _ ⊆ (Iinner 0).F
    rw [hOuterAlpha, hInnerF 0]
    exact fun _ hx => Or.inl (Or.inr hx)
  have hTarOuter : (packet 1).alpha 1 '' Icc (0 : ℝ) 1 ⊆ (packet 2).F := by
    change Iouter.alpha 1 '' _ ⊆ (Iinner 1).F
    rw [hOuterAlpha, hInnerF 1]
    exact fun _ hx => Or.inl (Or.inr hx)
  have hBetaProtected : (packet 0).alpha 1 '' Icc (0 : ℝ) 1 ⊆ (packet 1).F := by
    change (Iinner 0).alpha 1 '' _ ⊆ Iouter.F
    rw [hInnerAlpha 0, hOuterF]
    exact fun _ hx => Or.inl (Or.inl (Or.inr hx))
  have hFull (j : Fin 2) : (⋃ i : Fin 2, alpha j i '' Icc (0 : ℝ) 1) =
      alpha j 0 '' Icc (0 : ℝ) 1 ∪ alpha j 1 '' Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨0, hx⟩
      · exact mem_iUnion.mpr ⟨1, hx⟩
  have hOrder (j : Fin 2) : (⋃ i : Fin 2, alpha j i '' Icc (0 : ℝ) 1) =
      alpha j inner '' Icc (0 : ℝ) 1 ∪
        alpha j (Equiv.swap (0 : Fin 2) 1 inner) '' Icc (0 : ℝ) 1 := by
    rw [hFull j]
    fin_cases inner <;> simp [union_comm]
  let I : CommonBetaThreePacketInput := {
    packetInput := packet
    Kcommon := kappa '' closedBall (0 : E2) 1
    ERef := ⋃ i : Fin 2, alpha 0 i '' Icc (0 : ℝ) 1
    ETar := ⋃ i : Fin 2, alpha 1 i '' Icc (0 : ℝ) 1
    hKcommon := hK
    hBeta := hBeta
    hRefOuter := hRefOuter
    hTarOuter := hTarOuter
    hBetaProtected := hBetaProtected
    hRef := by
      change _ = (Iinner 0).alpha 0 '' _ ∪ Iouter.alpha 0 '' _
      rw [hInnerAlpha 0, hOuterAlpha]
      exact hOrder 0
    hTar := by
      change _ = (Iinner 1).alpha 0 '' _ ∪ Iouter.alpha 1 '' _
      rw [hInnerAlpha 1, hOuterAlpha]
      exact hOrder 1 }
  exact ⟨I, rfl, rfl, rfl⟩




private theorem commonBeta_physical_critical_images
    (u : UnitTwoSphere) (c : ℝ)
    (gRef : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (kappa : OpenPartialHomeomorph E2 E2)
    (hg : EqOn gRef kappa (closedBall (0 : E2) 2))
    (S : Fin 2 → Set E3) (alpha : Fin 2 → Fin 2 → ℝ → E2)
    (hUnion : ∀ j, (⋃ i : Fin 2, alpha j i '' Icc (0 : ℝ) 1) =
      {x : E2 | (heightPlaneCoordinates u).symm (x, c) ∈ S j} \
        (kappa '' ball (0 : E2) 1)) :
    (gRef '' closedBall (0 : E2) 1 = kappa '' closedBall (0 : E2) 1) ∧
      ∀ j, gRef '' nestedCommonE u c gRef S j 0 =
        (⋃ i : Fin 2, alpha j i '' Icc (0 : ℝ) 1) := by
  have hsub : closedBall (0 : E2) 1 ⊆ closedBall (0 : E2) 2 :=
    closedBall_subset_closedBall (by norm_num)
  have hclosed : gRef '' closedBall (0 : E2) 1 =
      kappa '' closedBall (0 : E2) 1 := by
    apply image_congr
    exact fun _ hx => hg (hsub hx)
  have hopen : gRef '' ball (0 : E2) 1 = kappa '' ball (0 : E2) 1 := by
    apply image_congr
    exact fun _ hx => hg (hsub (ball_subset_closedBall hx))
  refine ⟨hclosed, ?_⟩
  intro j
  have hext := (saddle_middle_exterior_coordinates u c gRef (S j)).2 0
  calc
    gRef '' nestedCommonE u c gRef S j 0 =
        {x : E2 | (heightPlaneCoordinates u).symm (x, c) ∈ S j} \
          (gRef '' ball (0 : E2) 1) := by
      simpa only [nestedCommonE, nestedCommonL, add_zero] using hext
    _ = (⋃ i : Fin 2, alpha j i '' Icc (0 : ℝ) 1) := by
      rw [hopen, ← hUnion j]


set_option maxHeartbeats 1500000 in

set_option linter.unusedVariables false in



theorem exists_saddle_common_beta_pair_of_original_nested_arcs
    (hP : PlanarSchoenfliesService)
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (mu : Fin 2 → ℝ) (hmu : ∀ j, 0 < mu j)
    (hmuSmall : ∀ j, mu j ≤ 1 / 128)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let F : Fin 2 → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
      fun j => Classical.choose (exists_saddle_angular_reconnection
        J2 hJ2 (mu j) (hmu j) (hmuSmall j) chi hchi
        hchiBounds hchiSupport hchiOne)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let K : Set E2 := kappa '' closedBall (0 : E2) 1
    let sign : Fin 2 → ℝ := ![1, -1]
    let Z : Fin 2 → Fin 2 → Set E2 := fun j i =>
      {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu j)}
    let Eta : Fin 2 → Fin 2 → Set E2 := fun j i =>
      kappa '' ((F j 1) '' Z j i)
    ∀ (nu : ℝ) (hnu : 0 < nu) (hnuSmall : nu < 1 / 16)
      (alpha : Fin 2 → Fin 2 → ℝ → E2)
      (hAlpha : ∀ j i, ContDiffOn ℝ ∞ (alpha j i) (Ioo (-nu) (1 + nu)))
      (hAlphaInj : ∀ j i, InjOn (alpha j i) (Ioo (-nu) (1 + nu)))
      (hAlphaReg : ∀ j i t, t ∈ Ioo (-nu) (1 + nu) → deriv (alpha j i) t ≠ 0)
      (hProper : ∀ j i, alpha j i '' Ioo (0 : ℝ) 1 ⊆ Kᶜ)
      (hInitial : ∀ j i t, |t| < nu →
        alpha j i t = kappa ((1 + t) • port (ep (i, 0))))
      (hTerminal : ∀ j i t, |t - 1| < nu →
        alpha j i t = kappa ((2 - t) • port (ep (i, 1))))
      (B : Fin 2 → Fin 2 → BallNeighborhoodChart E2 E2)
      (hBoundary : ∀ j i,
        (B j i).boundary = (alpha j i '' Icc (0 : ℝ) 1) ∪ Eta j i)
      (inner : Fin 2)
      (hNested : ∀ j, (B j inner).closedRegion ⊆
        (B j (Equiv.swap (0 : Fin 2) 1 inner)).inside),
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
        K ⊆ CJᶜ ∧
        J 1 '' (⋃ i : Fin 2, alpha 0 i '' Icc (0 : ℝ) 1) =
          (⋃ i : Fin 2, alpha 1 i '' Icc (0 : ℝ) 1) ∧
        (J 1).symm '' (⋃ i : Fin 2, alpha 1 i '' Icc (0 : ℝ) 1) =
          (⋃ i : Fin 2, alpha 0 i '' Icc (0 : ℝ) 1) := by
  classical
  dsimp only
  intro nu hnu hnuSmall alpha hAlpha hAlphaInj hAlphaReg hProper
    hInitial hTerminal B hBoundary inner hNested
  let F : Fin 2 → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
    fun j => Classical.choose (exists_saddle_angular_reconnection
      J2 hJ2 (mu j) (hmu j) (hmuSmall j) chi hchi
      hchiBounds hchiSupport hchiOne)
  let sign : Fin 2 → ℝ := ![1, -1]
  let Z : Fin 2 → Fin 2 → Set E2 := fun j i =>
    {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu j)}
  let Eta : Fin 2 → Fin 2 → Set E2 := fun j i =>
    kappa '' ((F j 1) '' Z j i)
  let outer : Fin 2 := Equiv.swap (0 : Fin 2) 1 inner
  let Long : Fin 2 → Set E2 := fun j =>
    {x | ‖x‖ ≤ 1 ∧ sign inner * (J2 x).2 < Real.sqrt ((J2 x).1 ^ 2 + mu j)}
  obtain ⟨h, hh, hhnu, hsmall, hSides, hAnnular, hInner, hInnerClosed⟩ :=
    exists_saddle_nested_pair_filled_sides_family kappa hkappaSource J2 hJ2
      mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne
      nu hnu hnuSmall alpha hAlpha hProper hInitial hTerminal B hBoundary inner hNested
  have hNorm (j : Fin 2) (x : E2) : ‖F j 1 x‖ = ‖x‖ := by
    have hF := Classical.choose_spec (exists_saddle_angular_reconnection
      J2 hJ2 (mu j) (hmu j) (hmuSmall j) chi hchi
      hchiBounds hchiSupport hchiOne)
    exact ((hF.2.2.2.1) 1 x).1
  have hZero (j : Fin 2) : F j 1 (0 : E2) = 0 := by
    apply norm_eq_zero.mp
    rw [hNorm, norm_zero]
  have hLongZero (j : Fin 2) : (0 : E2) ∈ Long j := by
    change ‖(0 : E2)‖ ≤ 1 ∧
      sign inner * (J2 0).2 < Real.sqrt ((J2 0).1 ^ 2 + mu j)
    rw [J2.map_zero]
    change ‖(0 : E2)‖ ≤ 1 ∧ sign inner * 0 < Real.sqrt (0 ^ 2 + mu j)
    simpa only [norm_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] using
      And.intro zero_le_one (Real.sqrt_pos.mpr (hmu j))
  let Filled : CommonBetaInnerFilledData kappa (fun j => B j inner) J2 h inner := {
    filled := fun j => F j 1
    longSide := Long
    hLong := fun j => (hSides j).2.1
    hZero := fun j => ⟨0, hLongZero j, hZero j⟩ }
  have hEta (j i : Fin 2) : Eta j i ⊆ kappa '' closedBall (0 : E2) 1 := by
    rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨F j 1 z, mem_closedBall_zero_iff.mpr ((hNorm j z).trans_le hz.1), rfl⟩
  obtain ⟨S, hBetaStart, hBetaRange⟩ := exists_saddle_common_beta_shared_short_data
    kappa hkappaSource hkappa hkappaInv J2 hJ2 h hh hsmall inner
  obtain ⟨Iinner, hInnerData, hInnerF⟩ := exists_saddle_common_beta_inner_inputs
    hP kappa hkappaSource hkappa hkappaInv J2 hJ2 h nu hh hhnu hsmall inner
      (fun j => alpha j inner) (fun j => alpha j outer)
      (fun j => B j inner) (fun j => B j outer)
      (fun j => Eta j inner) (fun j => Eta j outer)
      (fun j => hAlpha j inner) (fun j => hAlphaInj j inner)
      (fun j => hAlphaReg j inner) (fun j => hProper j inner)
      (fun j => hInitial j inner) (fun j => hTerminal j inner)
      (fun j => hAlpha j outer) (fun j => hBoundary j outer)
      (fun j => hBoundary j inner) hNested S Filled
      (fun j => hAnnular j inner) hInner hInnerClosed
  obtain ⟨Iouter, _hOuterKappa, hOuterAlpha, _hOuterL, _hOuterR, _hOuterEta, hOuterF⟩ :=
    exists_saddle_common_beta_outer_input kappa hkappaSource hkappa hkappaInv J2 hJ2
      h nu hh hhnu hsmall inner mu hmu hmuSmall (fun j => F j 1) hNorm
      (fun j => alpha j outer) S.beta (fun j => B j inner) (fun j => B j outer)
      (fun j => Eta j outer) (fun j => hAlpha j outer) (fun j => hAlphaInj j outer)
      (fun j => hAlphaReg j outer) (fun j => hProper j outer)
      (fun j => hInitial j outer) (fun j => hTerminal j outer)
      S.hBetaData.1 hBetaStart hBetaRange (fun j => hBoundary j outer)
      (fun j => hEta j outer) (fun j => hAnnular j outer)
      hInner hInnerClosed hNested (fun j => (hSides j).2.2.2)
  obtain ⟨I, hK, hRef, hTar⟩ := commonBeta_pack_original_arcs
    kappa alpha S.beta inner h Iinner Iouter (fun j => (hInnerData j).2.1)
    hInnerF hOuterAlpha hOuterF
  simpa only [hK, hRef, hTar] using exists_saddle_common_beta_raw_pair hP I

end PoincareConjecture.M25.Topology3D
