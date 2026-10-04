import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity.Euler
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity

/-!
# Smooth local minimizers on ancient surfaces

Square time maps the entire real line into the ancient flow domain, including
the initial endpoint. The actual scalar potential is smooth by the frozen
ancient-flow hypotheses, so the coordinate Euler regularity applies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareMT.AncientKappaSolution

open ReducedLengthMinimum.Variational

variable {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Every actual local H1 chart minimizer on an ancient surface is smooth,
including both endpoints in the square-time parameter. -/
theorem chart_minimum_contMDiffOn (K : AncientKappaSolution 2 M)
    {a b : ℝ} (hab : a < b) (x : M) (γ : ℝ → M)
    (hγ : ContinuousOn γ (Icc a b))
    (hsrc : MapsTo γ (Icc a b) (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
    (w : IntervalL2 (EuclideanSpace ℝ (Fin 2)) a b)
    (hw : ∀ s ∈ Icc a b, extChartAt (𝓡 2) x (γ s) =
      extChartAt (𝓡 2) x (γ a) + ∫ r in a..s, w r)
    (hmin : IsChartH1Minimizer K.flow 0 x a b γ w) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ γ (Icc a b) := by
  have hpre : ((fun r : ℝ => 0 - r ^ 2) ⁻¹' Iic (0 : ℝ)) = univ := by
    ext r
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    nlinarith [sq_nonneg r]
  have htime (s : ℝ) (_hs : s ∈ Icc a b) :
      s ∈ interior ((fun r : ℝ => 0 - r ^ 2) ⁻¹' Iic (0 : ℝ)) := by
    rw [hpre, interior_univ]
    exact mem_univ s
  have hchart := (chart_minimum_smooth_momentum K.flow 0
    K.regularizedPotential_contMDiff hab x γ hγ hsrc htime w hw hmin).1
  let e := extChartAt (𝓡 2) x
  have hsrc' : MapsTo γ (Icc a b) e.source := by
    simpa only [e, extChartAt_source] using hsrc
  have htarget : MapsTo (e ∘ γ) (Icc a b) e.target :=
    fun s hs => e.map_source (hsrc' hs)
  have hcomp := (contMDiffOn_extChartAt_symm (I := 𝓡 2) x).comp
    hchart.contMDiffOn htarget
  apply hcomp.congr
  intro s hs
  exact (e.left_inv (hsrc' hs)).symm

end PoincareMT.AncientKappaSolution
