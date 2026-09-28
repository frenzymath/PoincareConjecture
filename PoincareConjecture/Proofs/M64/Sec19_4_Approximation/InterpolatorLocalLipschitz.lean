import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in

theorem m64_interpolator_contMDiffAt_of_cell
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {U : Set (M × M)} {H : ℝ × (M × M) → M}
    (hU : IsOpen U)
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma Set.univ)
    (hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈ U)
    (j : Fin N) {x : LoopPlane} (hx : x ∈ m64PolygonCellSet j) :
    ContMDiffAt (𝓡 2) (𝓡 n) 1
      (fun p : LoopPlane => H (p 1, gamma (p 0),
        (polygon.side j).map (p 0 - m63CellLeft N j))) x := by
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
  have hp0 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1
      (fun p : LoopPlane => p 0) x := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
      (n := ∞) |>.of_le (m := 1) (by norm_num) |>.contMDiff.contMDiffAt
  have hp1 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1
      (fun p : LoopPlane => p 1) x := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff
      (n := ∞) |>.of_le (m := 1) (by norm_num) |>.contMDiff.contMDiffAt
  have hp0top : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p : LoopPlane => p 0) x := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
      (n := ∞) |>.contMDiff.contMDiffAt
  let phi : LoopPlane → ℝ := fun p => p 0 - m63CellLeft N j
  have hphi : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ phi x := by
    have hc := hp0top.add (contMDiffAt_const (x := x)
      (c := -(m63CellLeft N j)))
    change ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p : LoopPlane => p 0 + -(m63CellLeft N j)) x
    exact hc
  have hgammaAt : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (x 0) :=
    hgamma.contMDiffAt (isOpen_univ.mem_nhds (mem_univ _))
  have hsideAt : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (polygon.side j).map (x 0 - m63CellLeft N j) :=
    (polygon.side j).smooth.contMDiffAt
      ((polygon.side j).domain_open.mem_nhds hleft)
  have hgammaComp : ContMDiffAt (𝓡 2) (𝓡 n) 1
      (fun p : LoopPlane => gamma (p 0)) x := hgammaAt.comp x hp0
  have hsideComp : ContMDiffAt (𝓡 2) (𝓡 n) ∞
      (fun p : LoopPlane => (polygon.side j).map (phi p)) x :=
    hsideAt.comp x hphi
  have hsideComp1 : ContMDiffAt (𝓡 2) (𝓡 n) 1
      (fun p : LoopPlane => (polygon.side j).map (phi p)) x :=
    hsideComp.of_le (m := 1) (by norm_num)
  have hinput : ContMDiffAt (𝓡 2)
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) 1
      (fun p : LoopPlane => (p 1, (gamma (p 0),
        (polygon.side j).map (phi p)))) x := by
    exact hp1.prodMk (hgammaComp.prodMk hsideComp1)
  have hpoint : (x 1, (gamma (x 0), (polygon.side j).map
      (x 0 - m63CellLeft N j))) ∈ Ioo (-1 : ℝ) 2 ×ˢ U :=
    ⟨htime, hpairx⟩
  have hHat := hH.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds hpoint)
  have hcomp := (hHat.of_le (m := 1) (by norm_num)).comp x hinput
  simpa only [Function.comp_def, phi] using hcomp

theorem m64_interpolator_lipschitzOn_nhds_of_cell
    (g : RiemannianMetric n M) {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {U : Set (M × M)} {H : ℝ × (M × M) → M}
    (hU : IsOpen U)
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma Set.univ)
    (hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈ U)
    (j : Fin N) {x : LoopPlane} (hx : x ∈ m64PolygonCellSet j) :
    ∃ K : ℝ≥0, ∃ V ∈ 𝓝 x, ∀ y ∈ V, ∀ z ∈ V,
      g.edist (H (y 1, gamma (y 0),
          (polygon.side j).map (y 0 - m63CellLeft N j)))
          (H (z 1, gamma (z 0),
            (polygon.side j).map (z 0 - m63CellLeft N j))) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
  exact m64_lipschitzOn_nhds_of_contMDiffAt g
    (m64_interpolator_contMDiffAt_of_cell polygon hU hH hgamma hpair j hx)

end PoincareConjecture
