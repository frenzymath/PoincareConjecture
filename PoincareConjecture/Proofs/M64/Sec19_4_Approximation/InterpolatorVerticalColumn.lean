import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorLocalLipschitz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem m64_loopPlane_vertical_basis_zero (x : LoopPlane) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : LoopPlane => p 0) x
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0 := by
  rw [mfderiv_eq_fderiv]
  have hderiv : fderiv ℝ (fun y : LoopPlane => y 0) x =
      (EuclideanSpace.proj 0 : LoopPlane →L[ℝ] ℝ) :=
    (show LoopPlane →L[ℝ] ℝ from EuclideanSpace.proj 0).fderiv
  rw [hderiv]
  change (EuclideanSpace.basisFun (Fin 2) ℝ 1) 0 = 0
  simp [EuclideanSpace.basisFun_apply]

theorem m64_loopPlane_horizontal_basis_one (x : LoopPlane) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : LoopPlane => p 1) x
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 1 := by
  rw [mfderiv_eq_fderiv]
  have hderiv : fderiv ℝ (fun y : LoopPlane => y 1) x =
      (EuclideanSpace.proj 1 : LoopPlane →L[ℝ] ℝ) :=
    (show LoopPlane →L[ℝ] ℝ from EuclideanSpace.proj 1).fderiv
  rw [hderiv]
  change (EuclideanSpace.basisFun (Fin 2) ℝ 1) 1 = 1
  simp [EuclideanSpace.basisFun_apply]

omit [T2Space M] in

theorem m64_interpolator_vertical_column_of_speed
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {U : Set (M × M)} {H : ℝ × (M × M) → M}
    (hU : IsOpen U)
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma Set.univ)
    (hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈ U)
    (j : Fin N) {x : LoopPlane} (hx : x ∈ m64PolygonCellSet j)
    {r : ℝ}
    (hpq : g.edist (gamma (x 0)) ((polygon.side j).map
      (x 0 - m63CellLeft N j)) < ENNReal.ofReal r)
    (hgeom : g.edist (gamma (x 0)) ((polygon.side j).map
      (x 0 - m63CellLeft N j)) < ENNReal.ofReal r →
      H (0, gamma (x 0), (polygon.side j).map (x 0 - m63CellLeft N j)) =
          gamma (x 0) ∧
        H (1, gamma (x 0), (polygon.side j).map (x 0 - m63CellLeft N j)) =
          (polygon.side j).map (x 0 - m63CellLeft N j) ∧
        g.IsGeodesicOn
          (fun t => H (t, gamma (x 0),
            (polygon.side j).map (x 0 - m63CellLeft N j)))
          (Ioo (-1 : ℝ) 2) ∧
        (∀ t ∈ Ioo (-1 : ℝ) 2,
          g.tangentNorm
            (H (t, gamma (x 0), (polygon.side j).map
              (x 0 - m63CellLeft N j)))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
              (fun s => H (s, gamma (x 0),
                (polygon.side j).map (x 0 - m63CellLeft N j))) t 1) =
              (g.edist (gamma (x 0))
                ((polygon.side j).map (x 0 - m63CellLeft N j))).toReal) ∧
        g.pathELength
            (fun t => H (t, gamma (x 0),
              (polygon.side j).map (x 0 - m63CellLeft N j))) 0 1 =
          g.edist (gamma (x 0)) ((polygon.side j).map
            (x 0 - m63CellLeft N j))) :
    g.tangentNorm
      (H (x 1, gamma (x 0), (polygon.side j).map
        (x 0 - m63CellLeft N j)))
      (mfderiv (𝓡 2) (𝓡 3)
        (fun p : LoopPlane => H (p 1, gamma (p 0),
          (polygon.side j).map (p 0 - m63CellLeft N j))) x
        (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
      (g.edist (gamma (x 0)) ((polygon.side j).map
        (x 0 - m63CellLeft N j))).toReal := by
  change m63CellLeft N j ≤ x 0 ∧
    x 0 ≤ m63CellLeft N j + m63CellLength N ∧
      0 ≤ x 1 ∧ x 1 ≤ 1 at hx
  have htime : x 1 ∈ Ioo (-1 : ℝ) 2 := by
    constructor <;> linarith [hx.2.2.1, hx.2.2.2]
  have hleft : x 0 - m63CellLeft N j ∈ (polygon.side j).domain := by
    apply (polygon.side j).interval_subset
    constructor <;> linarith [hx.1, hx.2.1]
  have hpairx : (gamma (x 0), (polygon.side j).map
      (x 0 - m63CellLeft N j)) ∈ U := hpair j x ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩
  have hp0 : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : LoopPlane => p 0) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
      (n := ∞) |>.of_le (m := 1) (by norm_num) |>.contMDiff.contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hp1 : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : LoopPlane => p 1) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff
      (n := ∞) |>.of_le (m := 1) (by norm_num) |>.contMDiff.contMDiffAt
      |>.mdifferentiableAt (by simp)
  let phi : LoopPlane → ℝ := fun p => p 0 - m63CellLeft N j
  have hphi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) phi x := by
    have hp0top : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun p : LoopPlane => p 0) x := by
      exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
        (n := ∞) |>.contMDiff.contMDiffAt
    have hc := hp0top.add (contMDiffAt_const (x := x)
      (c := -(m63CellLeft N j)))
    have hc1 := hc.of_le (m := 1) (by norm_num)
    have hcmd : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1
        (fun p : LoopPlane => p 0 + -(m63CellLeft N j)) x := by
      convert hc1 using 1
      rfl
    simpa only [phi, sub_eq_add_neg] using hcmd.mdifferentiableAt (by simp)
  have hgammaAt : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) gamma (x 0) :=
    (hgamma.contMDiffAt (isOpen_univ.mem_nhds (mem_univ _))).mdifferentiableAt
      (by simp)
  have hsideAt : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3)
      (polygon.side j).map (x 0 - m63CellLeft N j) :=
    (polygon.side j).smooth.contMDiffAt
      ((polygon.side j).domain_open.mem_nhds hleft) |>.mdifferentiableAt
      (by simp)
  let input : LoopPlane → ℝ × (M × M) := fun p =>
    (p 1, (gamma (p 0), (polygon.side j).map (phi p)))
  have hinput : MDifferentiableAt (𝓡 2)
      ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) input x := by
    exact hp1.prodMk ((hgammaAt.comp x hp0).prodMk
      (hsideAt.comp x hphi))
  have hpoint : (x 1, (gamma (x 0), (polygon.side j).map
      (x 0 - m63CellLeft N j))) ∈ Ioo (-1 : ℝ) 2 ×ˢ U :=
    ⟨htime, hpairx⟩
  have hHat : MDifferentiableAt
      ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) H
      (x 1, (gamma (x 0), (polygon.side j).map
        (x 0 - m63CellLeft N j))) :=
    (hH.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds hpoint)).mdifferentiableAt
      (by simp)
  let b : TangentSpace (𝓡 2) x := EuclideanSpace.basisFun (Fin 2) ℝ 1
  have hchain := mfderiv_comp_apply x hHat hinput b
  have hb0 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : LoopPlane => p 0) x b = 0 := by
    exact m64_loopPlane_vertical_basis_zero x
  have hb1 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : LoopPlane => p 1) x b = 1 := by
    exact m64_loopPlane_horizontal_basis_one x
  have hgamma_b : mfderiv (𝓡 2) (𝓡 3)
      (fun p : LoopPlane => gamma (p 0)) x b = 0 := by
    have hc := mfderiv_comp_apply x hgammaAt hp0 b
    rw [hb0] at hc
    simpa only [Function.comp_def, map_zero] using hc
  have hside_b : mfderiv (𝓡 2) (𝓡 3)
      (fun p : LoopPlane => (polygon.side j).map (phi p)) x b = 0 := by
    have hc := mfderiv_comp_apply x hsideAt hphi b
    rw [show mfderiv (𝓡 2) 𝓘(ℝ, ℝ) phi x b = 0 by
      dsimp only [phi]
      rw [mfderiv_eq_fderiv, fderiv_sub_const]
      have hproj : fderiv ℝ (fun p : LoopPlane => p 0) x =
          (EuclideanSpace.proj 0 : LoopPlane →L[ℝ] ℝ) :=
        (show LoopPlane →L[ℝ] ℝ from EuclideanSpace.proj 0).fderiv
      rw [hproj]
      change (EuclideanSpace.basisFun (Fin 2) ℝ 1) 0 = 0
      simp [EuclideanSpace.basisFun_apply]] at hc
    simpa only [Function.comp_def, map_zero] using hc
  have hbinput : mfderiv (𝓡 2)
      ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
      (fun p : LoopPlane => (p 1, (gamma (p 0),
        (polygon.side j).map (phi p)))) x b = (1, (0, 0)) := by
    have hprod := mfderiv_prodMk hp1
      ((hgammaAt.comp x hp0).prodMk (hsideAt.comp x hphi))
    have hev := congrArg (fun L => L b) hprod
    erw [mfderiv_prodMk (hgammaAt.comp x hp0) (hsideAt.comp x hphi)] at hev
    change _ = ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : LoopPlane => p 1) x) b,
      ((mfderiv (𝓡 2) (𝓡 3) (fun p : LoopPlane => gamma (p 0)) x) b,
        (mfderiv (𝓡 2) (𝓡 3)
          (fun p : LoopPlane => (polygon.side j).map (phi p)) x) b)) at hev
    simpa only [Function.comp_def, hb1, hgamma_b, hside_b] using hev
  let v : TangentSpace ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
      (x 1, (gamma (x 0), (polygon.side j).map
        (x 0 - m63CellLeft N j))) := (1, (0, 0))
  have hchain' : mfderiv (𝓡 2) (𝓡 3)
      (fun p : LoopPlane => H (p 1, gamma (p 0),
        (polygon.side j).map (p 0 - m63CellLeft N j))) x b =
      mfderiv ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) H
        (x 1, (gamma (x 0), (polygon.side j).map
          (x 0 - m63CellLeft N j))) v := by
    have hbeq : mfderiv (𝓡 2)
        ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) input x b = v := by
      simpa only [input] using hbinput
    have hceq := hchain.trans (congrArg
      (fun w => mfderiv ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
        (𝓡 3) H (input x) w) hbeq)
    simpa only [Function.comp_def, input] using hceq
  let time : ℝ → ℝ × (M × M) := fun t =>
    (t, (gamma (x 0), (polygon.side j).map (x 0 - m63CellLeft N j)))
  have htimeInput : MDifferentiableAt 𝓘(ℝ, ℝ)
      ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) time (x 1) := by
    exact mdifferentiableAt_id.prodMk
      (mdifferentiableAt_const.prodMk mdifferentiableAt_const)
  have htimeChain := mfderiv_comp_apply (x 1) hHat htimeInput (1 : ℝ)
  erw [mfderiv_prodMk mdifferentiableAt_id
      (mdifferentiableAt_const.prodMk mdifferentiableAt_const),
    mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_const] at htimeChain
  simp only [mfderiv_const, mfderiv_id] at htimeChain
  erw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply] at htimeChain
  have htimeChain' : mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
      (fun t : ℝ => H (t, gamma (x 0), (polygon.side j).map
        (x 0 - m63CellLeft N j))) (x 1) 1 =
      mfderiv ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) H
        (x 1, (gamma (x 0), (polygon.side j).map
          (x 0 - m63CellLeft N j))) v := by
    simpa [Function.comp_def, time, v] using htimeChain
  change g.tangentNorm
      (H (x 1, gamma (x 0), (polygon.side j).map
        (x 0 - m63CellLeft N j)))
      (mfderiv (𝓡 2) (𝓡 3)
        (fun p : LoopPlane => H (p 1, gamma (p 0),
          (polygon.side j).map (p 0 - m63CellLeft N j))) x b) = _
  rw [hchain', ← htimeChain']
  exact (hgeom hpq).2.2.2.1 (x 1) htime

end PoincareConjecture
