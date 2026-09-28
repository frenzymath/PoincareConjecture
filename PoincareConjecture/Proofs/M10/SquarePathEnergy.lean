import PoincareConjecture.Proofs.M10.CurveEnergy
import PoincareConjecture.Proofs.M10.ActionLowerBound
import PoincareConjecture.Proofs.M10.UniformMetricComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

noncomputable def terminalSquareEnergy (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (s : ℝ) : ℝ :=
  (F.metric T).inner (G.squareFamily Z s)
    (curveVelocity (G.squareFamily Z) s) (curveVelocity (G.squareFamily Z) s)

set_option backward.isDefEq.respectTransparency false in

theorem squareFamily_contMDiffOn (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (G.squareFamily Z)
      {s | (Z, s) ∈ G.squareDomain} := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  exact G.square_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    (fun _ hs ↦ hs)

theorem terminalSquareEnergy_continuousOn (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    ContinuousOn (terminalSquareEnergy G Z) (Icc 0 (Real.sqrt τ)) := by
  have hU : IsOpen {s : ℝ | (Z, s) ∈ G.squareDomain} :=
    G.square_open.preimage (continuous_const.prodMk continuous_id)
  apply (curve_energy_continuousOn (F.metric T) hU
    ((squareFamily_contMDiffOn G Z).of_le (by decide))).mono
  intro s hs
  apply G.square_contains
  exact ⟨mem_univ _, hs.1, hs.2.trans_lt (Real.sqrt_lt_sqrt hτ.le hmax)⟩

theorem terminalSquareEnergy_eq_speed (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt τmax)) :
    terminalSquareEnergy G Z s = (2 * s) ^ 2 *
      (F.metric T).inner (G.gamma Z (s ^ 2))
        (curveVelocity (G.gamma Z) (s ^ 2)) (curveVelocity (G.gamma Z) (s ^ 2)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hmax : 0 < τmax := Real.sqrt_pos.mp (hs.1.trans hs.2)
  have hsmax : s ^ 2 < τmax := by nlinarith [Real.sq_sqrt hmax.le, hs.1, hs.2]
  have heq : G.squareFamily Z =ᶠ[𝓝 s] (fun r : ℝ ↦ G.gamma Z (r ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact G.square_agrees Z r ⟨hr.1.le, hr.2⟩
  rw [terminalSquareEnergy, curve_energy_eq_of_eventuallyEq (F.metric T) heq]
  apply curve_energy_comp_square
  have hg := G.gamma_smooth.contMDiffAt (x := (Z, s ^ 2))
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ Z, sq_pos_of_pos hs.1, hsmax⟩)
  exact (hg.comp (s ^ 2) (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt
    (by simp)

end PoincareConjecture.M10
