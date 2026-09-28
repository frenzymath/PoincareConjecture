import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalRimWordExclusionHelpers
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "D2" => closedBall (0 : V2) 1

structure OriginalResolutionWordExclusionData
    {X : Type*} [TopologicalSpace X]
    (f : V2 → X) (Fmark : Set X)
    (base : Fmark) (J : Subgroup (FundamentalGroup Fmark base))
    (c : Bool → P2 → V2) (τ : C3 → X) (b : ℝ) where
  A : Set V2
  M : Set V2
  C : Set V2
  L : Set V2
  R : Set V2
  s0 : Bool
  s1 : Bool
  u : V2
  v : V2
  pA : MarkedPLIntervalPath Fmark f (A ∩ Q2)
    (c false (0, farArmParameter (!s0))) (c false (1, farArmParameter (!s0)))
  pC : MarkedPLIntervalPath Fmark f (C ∩ Q2)
    (c true (1, farArmParameter (!s1))) (c true (0, farArmParameter (!s1)))
  pL : MarkedPLIntervalPath Fmark f L (c false (0, farArmParameter s0)) u
  pR : MarkedPLIntervalPath Fmark f R v (c false (1, farArmParameter s0))
  E0 : MarkedResolutionEndData Fmark (τ ∘ tubeArmOrientation s0 s1) b 0
  E1 : MarkedResolutionEndData Fmark (τ ∘ tubeArmOrientation s0 s1) b 1
  D0 : MarkedResolutionOldEndData E0
  D1 : MarkedResolutionOldEndData E1
  diskA : IsFinitePLBallPair P2 A ((A ∩ Q2) ∪ c false '' arm (farArmParameter (!s0)))
  diskM : IsFinitePLBallPair P2 M
    (((M ∩ Q2) ∪ c false '' arm (farArmParameter s0)) ∪ c true '' arm (farArmParameter s1))
  diskC : IsFinitePLBallPair P2 C ((C ∩ Q2) ∪ c true '' arm (farArmParameter (!s1)))
  disjointAM : Disjoint A M
  disjointMC : Disjoint M C
  disjointAC : Disjoint A C
  cover : ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = D2
  strip0A : (c false '' source) ∩ A = c false '' arm (farArmParameter (!s0))
  strip0M : (c false '' source) ∩ M = c false '' arm (farArmParameter s0)
  strip1M : (c true '' source) ∩ M = c true '' arm (farArmParameter s1)
  strip1C : (c true '' source) ∩ C = c true '' arm (farArmParameter (!s1))
  oppositeA : Disjoint A (c true '' source)
  oppositeC : Disjoint C (c false '' source)
  intervalA : IsFinitePLBallPair ℝ (A ∩ Q2)
    {c false (0, farArmParameter (!s0)), c false (1, farArmParameter (!s0))}
  intervalC : IsFinitePLBallPair ℝ (C ∩ Q2)
    {c true (0, farArmParameter (!s1)), c true (1, farArmParameter (!s1))}
  endpointsDistinct : u ≠ v
  intervalL : IsFinitePLBallPair ℝ L {c false (0, farArmParameter s0), u}
  intervalR : IsFinitePLBallPair ℝ R {v, c false (1, farArmParameter s0)}
  disjointLR : Disjoint L R
  middleRim : L ∪ R = M ∩ Q2
  leftArm0 : L ∩ c false '' arm (farArmParameter s0) = {c false (0, farArmParameter s0)}
  rightArm0 : R ∩ c false '' arm (farArmParameter s0) = {c false (1, farArmParameter s0)}
  leftArm1 : L ∩ c true '' arm (farArmParameter s1) = {u}
  rightArm1 : R ∩ c true '' arm (farArmParameter s1) = {v}
  H : Q2 ≃ₜ Q2
  H_finitePL : H.IsFinitePL
  H_base : (H squareRimBase : V2) = c false (0, farArmParameter (!s0))
  rho : Path E0.a E0.a
  complement : Path E0.a E1.a
  rho_val : ∀ t : unitInterval, (rho t : X) = f (H (squareRimLoop t))
  cases :
    ((u = c true (0, farArmParameter s1) ∧ v = c true (1, farArmParameter s1)) ∧
      ∃ (a : Path E0.a E1.a) (β : Path E1.r E1.l)
        (γ : Path E1.c E0.c) (d : Path E0.l E0.r),
        (∀ t : unitInterval, (a t : X) = f (pA.chart t)) ∧
        (∀ t : unitInterval, (β t : X) = f (pR.chart (unitInterval.symm t))) ∧
        (∀ t : unitInterval, (γ t : X) = f (pC.chart t)) ∧
        (∀ t : unitInterval, (d t : X) = f (pL.chart (unitInterval.symm t))) ∧
        complement = ((((((D0.AR.trans d.symm).trans D0.CL.symm).trans γ.symm).trans
          D1.CL).trans β.symm).trans D1.AR.symm) ∧
        rho.Homotopic (a.trans complement.symm) ∧
        ∀ (p : Path base E0.z) (q : Path base E1.z),
          basedPathWord (p.trans E0.ra) (q.trans E1.ra) a *
            basedPathWord (q.trans E1.rr) (q.trans E1.rl) β *
            basedPathWord (q.trans E1.rc) (p.trans E0.rc) γ *
            basedPathWord (p.trans E0.rl) (p.trans E0.rr) d ∉ J) ∨
    ((u = c true (1, farArmParameter s1) ∧ v = c true (0, farArmParameter s1)) ∧
      ∃ (a : Path E1.a E0.a) (β : Path E0.r E1.l)
        (γ : Path E1.c E0.c) (d : Path E0.l E1.r),
        (∀ t : unitInterval, (a t : X) = f (pA.chart (unitInterval.symm t))) ∧
        (∀ t : unitInterval, (β t : X) = f (pL.chart t)) ∧
        (∀ t : unitInterval, (γ t : X) = f (pC.chart t)) ∧
        (∀ t : unitInterval, (d t : X) = f (pR.chart t)) ∧
        complement = ((((((D0.AR.trans β).trans D1.CL.symm).trans γ).trans
          D0.CL).trans d).trans D1.AR.symm) ∧
        rho.Homotopic (a.symm.trans complement.symm) ∧
        ∀ (p : Path base E0.z) (q : Path base E1.z),
          basedPathWord (q.trans E1.ra) (p.trans E0.ra) a *
            basedPathWord (p.trans E0.rr) (q.trans E1.rl) β *
            basedPathWord (q.trans E1.rc) (p.trans E0.rc) γ *
            basedPathWord (p.trans E0.rl) (q.trans E1.rr) d ∉ J)

theorem nonempty_original_resolution_word_exclusion_data
    {X : Type*} [TopologicalSpace X] {Fmark : Set X}
    {base : Fmark} {J : Subgroup (FundamentalGroup Fmark base)} [J.Normal]
    (f : V2 → X) (hf : ContinuousOn f D2) (rim : C(Q2, Fmark))
    (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase))
    (houtside : basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J)
    (c : Bool → P2 → V2)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q2 ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (τ : C3 → X) (hτ : ContinuousOn τ tube)
    (hτmark : ∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → τ z ∈ Fmark)
    (hsheet0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (hsheet1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    {b : ℝ} (hb : b < 1) :
    Nonempty (OriginalResolutionWordExclusionData f Fmark base J c τ b) := by
  have hS : IsFinitePLBallPair P2 D2 Q2 :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hfmark : MapsTo f Q2 Fmark := by
    intro x hx
    rw [hboundary ⟨x, hx⟩]
    exact (rim ⟨x, hx⟩).property
  have hc (i : Bool) : ContinuousOn (c i) source := (hcPL i).continuousOn
  have hfQ := hf.mono hS.1
  obtain ⟨A, M, C, L, R, s0, s1, u, v, pA, pC, pL, pR, E0, E1,
    hA, hM, hC, hAM, hMC, hAC, hcover, h0A, h0M, h1M, h1C, hA1, hC0,
    hAI, hCI, huv, hLI, hRI, hLR, hLRQ, hLW, hRW, hLZ, hRZ, hcases⟩ :=
    exists_original_resolution_word_paths hS c hcPL hci hcS hcQ hdisj f
      hf hfmark τ hτ hτmark hsheet0 hsheet1 hb
  let τ' := τ ∘ tubeArmOrientation s0 s1
  have hτ' : ContinuousOn τ' tube := hτ.comp
    (tubeArmOrientation s0 s1).continuous.continuousOn
    (fun z hz ↦ (tubeArmOrientation_mem_tube s0 s1 z).mpr hz)
  have hτmark' (z : C3) (hz : z ∈ tube) (ht : z.2 = 0 ∨ z.2 = 1) : τ' z ∈ Fmark := by
    apply hτmark _ ((tubeArmOrientation_mem_tube s0 s1 z).mpr hz)
    simpa only [tubeArmOrientation_longitudinal] using ht
  obtain ⟨D0⟩ := nonempty_marked_resolution_old_end_data τ' hτ' hτmark' 0 (by simp) E0
  obtain ⟨D1⟩ := nonempty_marked_resolution_old_end_data τ' hτ' hτmark' 1 (by simp) E1
  have hD0 := marked_old_end_data_original_strip_values f (c false) (c true) τ
    (hc false) (hc true) hsheet0 hsheet1 s0 s1 0 E0 D0
  have hD1 := marked_old_end_data_original_strip_values f (c false) (c true) τ
    (hc false) (hc true) hsheet0 hsheet1 s0 s1 1 E1 D1
  have hane : c false (0, farArmParameter (!s0)) ≠ c false (1, farArmParameter (!s0)) := by
    have hfar : farArmParameter (!s0) ∈ Icc (-1 : ℝ) 1 := by
      cases s0 <;> norm_num [farArmParameter]
    intro he
    have hh := hci false (show (0, farArmParameter (!s0)) ∈ source from ⟨by norm_num, hfar⟩)
      (show (1, farArmParameter (!s0)) ∈ source from ⟨by norm_num, hfar⟩) he
    have := congrArg Prod.fst hh
    norm_num at this
  have hLrange (t : unitInterval) : pL.sourcePath t ∈ M ∩ Q2 :=
    hLRQ.subset (Or.inl (pL.chart t).property)
  have hRrange (t : unitInterval) : pR.sourcePath t ∈ M ∩ Q2 :=
    hLRQ.subset (Or.inr (pR.chart t).property)
  rcases hcases with ⟨⟨hu, hv⟩, a, β, γ, d, ha, hβ, hγ, hd, _⟩ |
    ⟨⟨hu, hv⟩, a, β, γ, d, ha, hβ, hγ, hd, _⟩
  · let LP := pL.sourcePath.cast rfl hu.symm
    let KP := pC.sourcePath.symm
    let NP := pR.sourcePath.cast hv.symm rfl
    obtain ⟨H, rho, B, hH, hbase, hB, hrho, hhom⟩ :=
      exists_original_rim_traversal_of_exterior_paths hS c hc hcQ hAM hAC hcover s0 s1
        h0A hA1 hAI hane pA.chart pA.chart_finitePL pA.chart_zero pA.chart_one
        0 1 (by simp) (by simp) LP KP NP hLrange
        (fun r ↦ (pC.chart (unitInterval.symm r)).property) hRrange
        f hfQ hfmark a ha
    let T := ((((((D0.AR.trans d.symm).trans D0.CL.symm).trans γ.symm).trans
      D1.CL).trans β.symm).trans D1.AR.symm)
    let P := ((((((originalStripEndPath (c false) (hc false) 0 s0).trans LP).trans
      (originalStripEndPath (c true) (hc true) 0 s1).symm).trans KP).trans
      (originalStripEndPath (c true) (hc true) 1 s1)).trans NP).trans
      (originalStripEndPath (c false) (hc false) 1 s0).symm
    have hTB : T = B := by
      apply Path.ext
      funext r
      apply Subtype.ext
      apply Eq.trans _ (hB r).symm
      have hT : ∀ r, (T r : X) = f (P r) := by
        dsimp only [T, P]
        repeat' apply path_trans_target_values f
        · exact fun s ↦ (hD0 s).1
        · intro s
          simpa [LP, MarkedPLIntervalPath.sourcePath] using hd (unitInterval.symm s)
        · exact fun s ↦ (hD0 (unitInterval.symm s)).2
        · exact fun s ↦ hγ (unitInterval.symm s)
        · exact fun s ↦ (hD1 s).2
        · intro s
          simpa [NP, MarkedPLIntervalPath.sourcePath] using hβ (unitInterval.symm s)
        · exact fun s ↦ (hD1 (unitInterval.symm s)).1
      exact hT r
    have hout (p : Path base E0.z) (q : Path base E1.z) :
        basedPathWord (p.trans E0.ra) (q.trans E1.ra) a *
          basedPathWord (q.trans E1.rr) (q.trans E1.rl) β *
          basedPathWord (q.trans E1.rc) (p.trans E0.rc) γ *
          basedPathWord (p.trans E0.rl) (p.trans E0.rr) d ∉ J := by
      have hex := original_square_rim_excluded_of_values f rim hboundary basepath houtside
        H rho hrho (p.trans E0.ra)
      rw [Path.whiskeredLoopClass_congr _ hhom] at hex
      have he : (a.trans B.symm).Homotopic
          (((((((a.trans D1.AR).trans β).trans D1.CL.symm).trans γ).trans D0.CL).trans d).trans
            D0.AR.symm) := by
        rw [← hTB]
        apply Path.Homotopic.Quotient.eq.mp
        simp only [T, Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
          Path.Homotopic.Quotient.trans_assoc]
      rw [Path.whiskeredLoopClass_congr _ he] at hex
      intro hin
      apply hex
      apply J.inv_mem_iff.mp
      change basedPathWord _ _ _ ∈ J
      rwa [old_resolution_end_word_case_a E0 E1 D0 D1 base p q a β γ d]
    exact ⟨{
      A := A, M := M, C := C, L := L, R := R, s0 := s0, s1 := s1, u := u, v := v
      pA := pA, pC := pC, pL := pL, pR := pR, E0 := E0, E1 := E1, D0 := D0, D1 := D1
      diskA := hA, diskM := hM, diskC := hC
      disjointAM := hAM, disjointMC := hMC, disjointAC := hAC, cover := hcover
      strip0A := h0A, strip0M := h0M, strip1M := h1M, strip1C := h1C
      oppositeA := hA1, oppositeC := hC0, intervalA := hAI, intervalC := hCI
      endpointsDistinct := huv, intervalL := hLI, intervalR := hRI
      disjointLR := hLR, middleRim := hLRQ, leftArm0 := hLW, rightArm0 := hRW
      leftArm1 := hLZ, rightArm1 := hRZ
      H := H, H_finitePL := hH, H_base := hbase, rho := rho, complement := B, rho_val := hrho
      cases := Or.inl ⟨⟨hu, hv⟩, a, β, γ, d, ha, hβ, hγ, hd, hTB.symm, hhom, hout⟩ }⟩
  · let LP := pL.sourcePath.cast rfl hu.symm
    let KP := pC.sourcePath
    let NP := pR.sourcePath.cast hv.symm rfl
    have ha' (r : unitInterval) : (a.symm r : X) = f (pA.chart r) := by
      simpa using ha (unitInterval.symm r)
    obtain ⟨H, rho, B, hH, hbase, hB, hrho, hhom⟩ :=
      exists_original_rim_traversal_of_exterior_paths hS c hc hcQ hAM hAC hcover s0 s1
        h0A hA1 hAI hane pA.chart pA.chart_finitePL pA.chart_zero pA.chart_one
        1 0 (by simp) (by simp) LP KP NP hLrange
        (fun r ↦ (pC.chart r).property) hRrange f hfQ hfmark a.symm ha'
    let T := ((((((D0.AR.trans β).trans D1.CL.symm).trans γ).trans
      D0.CL).trans d).trans D1.AR.symm)
    let P := ((((((originalStripEndPath (c false) (hc false) 0 s0).trans LP).trans
      (originalStripEndPath (c true) (hc true) 1 s1).symm).trans KP).trans
      (originalStripEndPath (c true) (hc true) 0 s1)).trans NP).trans
      (originalStripEndPath (c false) (hc false) 1 s0).symm
    have hTB : T = B := by
      apply Path.ext
      funext r
      apply Subtype.ext
      apply Eq.trans _ (hB r).symm
      have hT : ∀ r, (T r : X) = f (P r) := by
        dsimp only [T, P]
        repeat' apply path_trans_target_values f
        · exact fun s ↦ (hD0 s).1
        · exact hβ
        · exact fun s ↦ (hD1 (unitInterval.symm s)).2
        · exact hγ
        · exact fun s ↦ (hD0 s).2
        · exact hd
        · exact fun s ↦ (hD1 (unitInterval.symm s)).1
      exact hT r
    have hout (p : Path base E0.z) (q : Path base E1.z) :
        basedPathWord (q.trans E1.ra) (p.trans E0.ra) a *
          basedPathWord (p.trans E0.rr) (q.trans E1.rl) β *
          basedPathWord (q.trans E1.rc) (p.trans E0.rc) γ *
          basedPathWord (p.trans E0.rl) (q.trans E1.rr) d ∉ J := by
      have hex := original_square_rim_excluded_of_values f rim hboundary basepath houtside
        H rho hrho (p.trans E0.ra)
      rw [Path.whiskeredLoopClass_congr _ hhom] at hex
      have he : (a.trans B).Homotopic
          (((((((a.trans D0.AR).trans β).trans D1.CL.symm).trans γ).trans D0.CL).trans d).trans
            D1.AR.symm) := by
        rw [← hTB]
        apply Path.Homotopic.Quotient.eq.mp
        simp only [T, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]
      intro hin
      have hOld : basedPathWord (q.trans E1.ra) (q.trans E1.ra) (a.trans B) ∈ J := by
        rw [basedPathWord_congr _ _ he, old_resolution_end_word_case_b E0 E1 D0 D1 base p q a β γ d]
        exact hin
      have hRot : basedPathWord (p.trans E0.ra) (p.trans E0.ra) (B.trans a) ∈ J :=
        (basedPathWord_cycle_mem_iff J (q.trans E1.ra) (p.trans E0.ra) a B).mpr hOld
      have hInv : basedPathWord (p.trans E0.ra) (p.trans E0.ra) (a.symm.trans B.symm) ∈ J := by
        rw [← Path.trans_symm, basedPathWord_symm]
        exact J.inv_mem hRot
      exact hex (J.inv_mem_iff.mp hInv)
    exact ⟨{
      A := A, M := M, C := C, L := L, R := R, s0 := s0, s1 := s1, u := u, v := v
      pA := pA, pC := pC, pL := pL, pR := pR, E0 := E0, E1 := E1, D0 := D0, D1 := D1
      diskA := hA, diskM := hM, diskC := hC
      disjointAM := hAM, disjointMC := hMC, disjointAC := hAC, cover := hcover
      strip0A := h0A, strip0M := h0M, strip1M := h1M, strip1C := h1C
      oppositeA := hA1, oppositeC := hC0, intervalA := hAI, intervalC := hCI
      endpointsDistinct := huv, intervalL := hLI, intervalR := hRI
      disjointLR := hLR, middleRim := hLRQ, leftArm0 := hLW, rightArm0 := hRW
      leftArm1 := hLZ, rightArm1 := hRZ
      H := H, H_finitePL := hH, H_base := hbase, rho := rho, complement := B, rho_val := hrho
      cases := Or.inr ⟨⟨hu, hv⟩, a, β, γ, d, ha, hβ, hγ, hd, hTB.symm, hhom, hout⟩ }⟩

theorem OriginalResolutionWordExclusionData.nonempty_center_paths
    {X : Type*} [TopologicalSpace X] {Fmark : Set X}
    {base : Fmark} {J : Subgroup (FundamentalGroup Fmark base)}
    {f : V2 → X}
    {c : Bool → P2 → V2} {τ : C3 → X} {b : ℝ}
    (D : OriginalResolutionWordExclusionData f Fmark base J c τ b)
    (rim : C(Q2, Fmark)) (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase)) :
    Nonempty (Path base D.E0.z × Path base D.E1.z) := by
  obtain ⟨p⟩ := original_square_rim_nonempty_whisker f rim hboundary basepath D.H D.rho D.rho_val
  exact ⟨p.trans D.E0.ra.symm, (p.trans D.complement).trans D.E1.ra.symm⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
