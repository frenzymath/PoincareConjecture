import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalExteriorPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionEndHomotopies
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.TubeArmOrientation











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1




theorem exists_original_resolution_word_paths
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {S Q : Set E} (hS : IsFinitePLBallPair P2 S Q) (c : Bool → P2 → E)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source S)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    {Fmark : Set X} (f : E → X) (hf : ContinuousOn f S) (hfmark : MapsTo f Q Fmark)
    (τ : C3 → X) (hτ : ContinuousOn τ tube)
    (hτmark : ∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → τ z ∈ Fmark)
    (hsheet0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (hsheet1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    {b : ℝ} (hb : b < 1) :
    ∃ (A M C L R : Set E) (s0 s1 : Bool) (u v : E),
      let τ' := τ ∘ tubeArmOrientation s0 s1
      let a0 := c false (0, farArmParameter (!s0))
      let a1 := c false (1, farArmParameter (!s0))
      let oldL0 := c false (0, farArmParameter s0)
      let oldL1 := c false (1, farArmParameter s0)
      let oldR0 := c true (0, farArmParameter s1)
      let oldR1 := c true (1, farArmParameter s1)
      let c0 := c true (0, farArmParameter (!s1))
      let c1 := c true (1, farArmParameter (!s1))
      let WA := c false '' arm (farArmParameter (!s0))
      let WL := c false '' arm (farArmParameter s0)
      let WR := c true '' arm (farArmParameter s1)
      let WC := c true '' arm (farArmParameter (!s1))
      ∃ (pA : MarkedPLIntervalPath Fmark f (A ∩ Q) a0 a1)
        (pC : MarkedPLIntervalPath Fmark f (C ∩ Q) c1 c0)
        (pL : MarkedPLIntervalPath Fmark f L oldL0 u)
        (pR : MarkedPLIntervalPath Fmark f R v oldL1)
        (E0 : MarkedResolutionEndData Fmark τ' b 0)
        (E1 : MarkedResolutionEndData Fmark τ' b 1),
        IsFinitePLBallPair P2 A ((A ∩ Q) ∪ WA) ∧
        IsFinitePLBallPair P2 M (((M ∩ Q) ∪ WL) ∪ WR) ∧
        IsFinitePLBallPair P2 C ((C ∩ Q) ∪ WC) ∧
        Disjoint A M ∧ Disjoint M C ∧ Disjoint A C ∧
        ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = S ∧
        (c false '' source) ∩ A = WA ∧ (c false '' source) ∩ M = WL ∧
        (c true '' source) ∩ M = WR ∧ (c true '' source) ∩ C = WC ∧
        Disjoint A (c true '' source) ∧ Disjoint C (c false '' source) ∧
        IsFinitePLBallPair ℝ (A ∩ Q) {a0, a1} ∧
        IsFinitePLBallPair ℝ (C ∩ Q) {c0, c1} ∧ u ≠ v ∧
        IsFinitePLBallPair ℝ L {oldL0, u} ∧ IsFinitePLBallPair ℝ R {v, oldL1} ∧
        Disjoint L R ∧ L ∪ R = M ∩ Q ∧
        L ∩ WL = {oldL0} ∧ R ∩ WL = {oldL1} ∧ L ∩ WR = {u} ∧ R ∩ WR = {v} ∧
        (((u = oldR0 ∧ v = oldR1) ∧
          ∃ (a : Path E0.a E1.a) (β : Path E1.r E1.l)
            (γ : Path E1.c E0.c) (d : Path E0.l E0.r),
            (∀ t : I01, (a t : X) = f (pA.chart t)) ∧
            (∀ t : I01, (β t : X) = f (pR.chart (unitInterval.symm t))) ∧
            (∀ t : I01, (γ t : X) = f (pC.chart t)) ∧
            (∀ t : I01, (d t : X) = f (pL.chart (unitInterval.symm t))) ∧
            ∀ (base : Fmark) (p : Path base E0.z) (q : Path base E1.z),
              let Aword := basedPathWord (p.trans E0.ra) (q.trans E1.ra) a
              let Bword := basedPathWord (q.trans E1.rr) (q.trans E1.rl) β
              let Cword := basedPathWord (q.trans E1.rc) (p.trans E0.rc) γ
              let Dword := basedPathWord (p.trans E0.rl) (p.trans E0.rr) d
              basedPathWord (p.trans E0.ra) (p.trans E0.ra)
                  (((a.trans E1.U).trans γ).trans E0.U.symm) = Aword * Cword ∧
                basedPathWord (p.trans E0.ra) (p.trans E0.ra)
                  (((((((a.trans E1.L.symm).trans β.symm).trans E1.R).trans γ).trans
                    E0.R.symm).trans d.symm).trans E0.L) =
                    Aword * Bword⁻¹ * Cword * Dword⁻¹) ∨
         ((u = oldR1 ∧ v = oldR0) ∧
          ∃ (a : Path E1.a E0.a) (β : Path E0.r E1.l)
            (γ : Path E1.c E0.c) (d : Path E0.l E1.r),
            (∀ t : I01, (a t : X) = f (pA.chart (unitInterval.symm t))) ∧
            (∀ t : I01, (β t : X) = f (pL.chart t)) ∧
            (∀ t : I01, (γ t : X) = f (pC.chart t)) ∧
            (∀ t : I01, (d t : X) = f (pR.chart t)) ∧
            ∀ (base : Fmark) (p : Path base E0.z) (q : Path base E1.z),
              let Aword := basedPathWord (q.trans E1.ra) (p.trans E0.ra) a
              let Bword := basedPathWord (p.trans E0.rr) (q.trans E1.rl) β
              let Cword := basedPathWord (q.trans E1.rc) (p.trans E0.rc) γ
              let Dword := basedPathWord (p.trans E0.rl) (q.trans E1.rr) d
              basedPathWord (q.trans E1.ra) (q.trans E1.ra)
                  (((a.trans E0.U).trans γ.symm).trans E1.U.symm) = Aword * Cword⁻¹ ∧
                basedPathWord (q.trans E1.ra) (q.trans E1.ra)
                  (((((((a.trans E0.L.symm).trans d).trans E1.R).trans γ).trans
                    E0.R.symm).trans β).trans E1.L) = Aword * Dword * Cword * Bword)) := by
  obtain ⟨A, M, C, L, R, s0, s1, u, v, pA, pC, pL, pR,
    hA, hM, hC, hAM, hMC, hAC, hcover, h0A, h0M, h1M, h1C, hA1, hC0,
    hAI, hCI, hpair, huv, hL, hR, hLR, hLRQ, hLW, hRW, hLZ, hRZ⟩ :=
    exists_original_exterior_paths hS c hcPL hci hcS hcQ hdisj f hf hfmark
  let τ' := τ ∘ tubeArmOrientation s0 s1
  have hτ' : ContinuousOn τ' tube := hτ.comp
    (tubeArmOrientation s0 s1).continuous.continuousOn
    (fun z hz ↦ (tubeArmOrientation_mem_tube s0 s1 z).mpr hz)
  have hτmark' (z : C3) (hz : z ∈ tube) (ht : z.2 = 0 ∨ z.2 = 1) : τ' z ∈ Fmark := by
    apply hτmark _ ((tubeArmOrientation_mem_tube s0 s1 z).mpr hz)
    simpa only [tubeArmOrientation_longitudinal] using ht
  obtain ⟨E0, E1, hwordsA, hwordsB⟩ :=
    exists_marked_resolution_end_word_calculations τ' hτ' hτmark' hb
  have hcorners (t : I01) := reoriented_tube_old_arm_equations f (c false) (c true)
    τ hsheet0 hsheet1 s0 s1 t
  have hAa0 : pA.initial = E0.a := Subtype.ext
    (pA.initial_val.trans ((hcorners 0).1.trans E0.a_val.symm))
  have hAa1 : pA.terminal = E1.a := Subtype.ext
    (pA.terminal_val.trans ((hcorners 1).1.trans E1.a_val.symm))
  have hCc1 : pC.initial = E1.c := Subtype.ext
    (pC.initial_val.trans ((hcorners 1).2.2.2.trans E1.c_val.symm))
  have hCc0 : pC.terminal = E0.c := Subtype.ext
    (pC.terminal_val.trans ((hcorners 0).2.2.2.trans E0.c_val.symm))
  have hLr0 : pL.initial = E0.r := Subtype.ext
    (pL.initial_val.trans ((hcorners 0).2.2.1.trans E0.r_val.symm))
  have hRr1 : pR.terminal = E1.r := Subtype.ext
    (pR.terminal_val.trans ((hcorners 1).2.2.1.trans E1.r_val.symm))
  let γ : Path E1.c E0.c := pC.path.cast hCc1.symm hCc0.symm
  refine ⟨A, M, C, L, R, s0, s1, u, v, pA, pC, pL, pR, E0, E1,
    hA, hM, hC, hAM, hMC, hAC, hcover, h0A, h0M, h1M, h1C, hA1, hC0,
    hAI, hCI, huv, hL, hR, hLR, hLRQ, hLW, hRW, hLZ, hRZ, ?_⟩
  rcases hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hLl0 : pL.terminal = E0.l := Subtype.ext
      (pL.terminal_val.trans ((congrArg f hu).trans
        ((hcorners 0).2.1.trans E0.l_val.symm)))
    have hRl1 : pR.initial = E1.l := Subtype.ext
      (pR.initial_val.trans ((congrArg f hv).trans
        ((hcorners 1).2.1.trans E1.l_val.symm)))
    let a : Path E0.a E1.a := pA.path.cast hAa0.symm hAa1.symm
    let β : Path E1.r E1.l := pR.path.symm.cast hRr1.symm hRl1.symm
    let d : Path E0.l E0.r := pL.path.symm.cast hLl0.symm hLr0.symm
    refine Or.inl ⟨⟨hu, hv⟩, a, β, γ, d, pA.path_val,
      (fun t ↦ pR.path_val (unitInterval.symm t)), pC.path_val,
      (fun t ↦ pL.path_val (unitInterval.symm t)), ?_⟩
    intro base p q
    exact hwordsA base p q a β γ d
  · have hLl1 : pL.terminal = E1.l := Subtype.ext
      (pL.terminal_val.trans ((congrArg f hu).trans
        ((hcorners 1).2.1.trans E1.l_val.symm)))
    have hRl0 : pR.initial = E0.l := Subtype.ext
      (pR.initial_val.trans ((congrArg f hv).trans
        ((hcorners 0).2.1.trans E0.l_val.symm)))
    let a : Path E1.a E0.a := pA.path.symm.cast hAa1.symm hAa0.symm
    let β : Path E0.r E1.l := pL.path.cast hLr0.symm hLl1.symm
    let d : Path E0.l E1.r := pR.path.cast hRl0.symm hRr1.symm
    refine Or.inr ⟨⟨hu, hv⟩, a, β, γ, d,
      (fun t ↦ pA.path_val (unitInterval.symm t)), pL.path_val, pC.path_val, pR.path_val, ?_⟩
    intro base p q
    exact hwordsB base p q a β γ d

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
