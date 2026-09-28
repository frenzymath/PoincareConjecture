import PoincareConjecture.Proofs.M03.Existence.CoordinateFrameNative
import PoincareConjecture.Proofs.M03.Existence.ChartJetCompatibilityNative









set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem chartInverse_mfderiv_eq_inverse_chart_mfderiv (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) :
    mfderiv 𝓘(ℝ, E) (𝓡 n) (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p x) =
      (mfderiv (𝓡 n) 𝓘(ℝ, E) (extChartAt (𝓡 n) p) x).inverse := by
  have hs : x ∈ (extChartAt (𝓡 n) p).source := by
    simpa only [extChartAt_source] using hx
  have hleft := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hs
  have hright := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hs
  have hinverse := (ContinuousLinearMap.inverse_eq hleft hright).symm
  change (mfderivWithin 𝓘(ℝ, E) (𝓡 n) (extChartAt (𝓡 n) p).symm
      (Set.range (𝓡 n)) (extChartAt (𝓡 n) p x) : E →L[ℝ] E) =
      (mfderiv (𝓡 n) 𝓘(ℝ, E) (extChartAt (𝓡 n) p) x : E →L[ℝ] E).inverse at hinverse
  change (mfderiv 𝓘(ℝ, E) (𝓡 n) (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p x) : E →L[ℝ] E) =
      (mfderiv (𝓡 n) 𝓘(ℝ, E) (extChartAt (𝓡 n) p) x : E →L[ℝ] E).inverse
  simpa using hinverse

theorem mvfderiv_scalar_chartFrame (p : M) (f : M → ℝ) {x : M}
    (hx : x ∈ (chartAt E p).source)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) (a : Fin n) :
    mvfderiv (𝓡 n) f x (chartFrame p a x) =
      fderiv ℝ (fun z => f ((extChartAt (𝓡 n) p).symm z))
        (extChartAt (𝓡 n) p x) ((PiLp.basisFun 2 ℝ (Fin n)) a) := by
  have hs : x ∈ (extChartAt (𝓡 n) p).source := by
    simpa only [extChartAt_source] using hx
  have ht := (extChartAt (𝓡 n) p).map_source hs
  have hback : (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p x) = x :=
    (extChartAt (𝓡 n) p).left_inv hs
  have hi : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p x) := by
    apply mdifferentiableWithinAt_univ.mp
    simpa using mdifferentiableWithinAt_extChartAt_symm ht
  have hcomp := mvfderiv_comp_apply_of_eq (extChartAt (𝓡 n) p x) hf hi hback
    ((PiLp.basisFun 2 ℝ (Fin n)) a)
  calc
    _ = mvfderiv (𝓡 n) f x
        ((mfderiv 𝓘(ℝ, E) (𝓡 n) (extChartAt (𝓡 n) p).symm
          (extChartAt (𝓡 n) p x)) ((PiLp.basisFun 2 ℝ (Fin n)) a)) := by
      rw [chartInverse_mfderiv_eq_inverse_chart_mfderiv p hx]
      rfl
    _ = mvfderiv 𝓘(ℝ, E) (f ∘ (extChartAt (𝓡 n) p).symm)
        (extChartAt (𝓡 n) p x) ((PiLp.basisFun 2 ℝ (Fin n)) a) := hcomp.symm
    _ = _ := by
      simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace, Function.comp_def] <;>
        rfl

def chartMetricCoefficients (g : RiemannianMetric n M) (p : M) (z : E) :
    Matrix (Fin n) (Fin n) ℝ :=
  (frameMetricJet g (chartFrame p) ((extChartAt (𝓡 n) p).symm z)).value

theorem frameMetricJet_value_eq_chartMetricCoefficients
    (g : RiemannianMetric n M) (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) :
    (frameMetricJet g (chartFrame p) x).value =
      chartMetricCoefficients g p (extChartAt (𝓡 n) p x) := by
  have hs : x ∈ (extChartAt (𝓡 n) p).source := by
    simpa only [extChartAt_source] using hx
  simp only [chartMetricCoefficients, (extChartAt (𝓡 n) p).left_inv hs]

theorem frameMetricJet_first_eq_chartCoefficient_derivative
    (g : RiemannianMetric n M) (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) (a i j : Fin n) :
    (frameMetricJet g (chartFrame p) x).first a i j =
      fderiv ℝ (fun z => chartMetricCoefficients g p z i j)
        (extChartAt (𝓡 n) p x) ((PiLp.basisFun 2 ℝ (Fin n)) a) := by
  have hF (k : Fin n) := (chartFrame_contMDiffOn p k).contMDiffAt
    ((chartAt E p).open_source.mem_nhds hx)
  have hvalue := frameMetricJet_value_contMDiffAt g (chartFrame p) hF
  have hentry := contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hvalue i) j
  exact mvfderiv_scalar_chartFrame p
    (fun y => g.inner y (chartFrame p i y) (chartFrame p j y)) hx
    (hentry.mdifferentiableAt (by simp)) a

theorem frameMetricJet_second_eq_chartCoefficient_derivative
    (g : RiemannianMetric n M) (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) (a b i j : Fin n) :
    (frameMetricJet g (chartFrame p) x).second a b i j =
      fderiv ℝ (fun z => fderiv ℝ (fun w => chartMetricCoefficients g p w i j) z
        ((PiLp.basisFun 2 ℝ (Fin n)) b))
        (extChartAt (𝓡 n) p x) ((PiLp.basisFun 2 ℝ (Fin n)) a) := by
  have hs : x ∈ (extChartAt (𝓡 n) p).source := by
    simpa only [extChartAt_source] using hx
  have ht := (extChartAt (𝓡 n) p).map_source hs
  have hF (k : Fin n) := (chartFrame_contMDiffOn p k).contMDiffAt
    ((chartAt E p).open_source.mem_nhds hx)
  have hfirst := frameMetricJet_first_contMDiffAt g (chartFrame p) hF b i j
  have houter := mvfderiv_scalar_chartFrame p
    (fun y => (frameMetricJet g (chartFrame p) y).first b i j) hx
    (hfirst.mdifferentiableAt (by simp)) a
  have htarget : (extChartAt (𝓡 n) p).target ∈ 𝓝 (extChartAt (𝓡 n) p x) := by
    simpa using extChartAt_target_mem_nhdsWithin_of_mem ht
  have hevent :
      (fun z => (frameMetricJet g (chartFrame p)
        ((extChartAt (𝓡 n) p).symm z)).first b i j) =ᶠ[𝓝 (extChartAt (𝓡 n) p x)]
      (fun z => fderiv ℝ (fun w => chartMetricCoefficients g p w i j) z
        ((PiLp.basisFun 2 ℝ (Fin n)) b)) := by
    filter_upwards [htarget] with z hz
    have hy : (extChartAt (𝓡 n) p).symm z ∈ (chartAt E p).source := by
      simpa only [extChartAt_source] using (extChartAt (𝓡 n) p).map_target hz
    have h := frameMetricJet_first_eq_chartCoefficient_derivative g p hy b i j
    simpa only [(extChartAt (𝓡 n) p).right_inv hz] using h
  calc
    _ = fderiv ℝ (fun z => (frameMetricJet g (chartFrame p)
        ((extChartAt (𝓡 n) p).symm z)).first b i j)
        (extChartAt (𝓡 n) p x) ((PiLp.basisFun 2 ℝ (Fin n)) a) := houter
    _ = _ := congrArg (fun L : E →L[ℝ] ℝ => L ((PiLp.basisFun 2 ℝ (Fin n)) a))
      hevent.fderiv_eq

private theorem metricJet2_eq_of_components {q r : MetricJet2 (n := n)}
    (hvalue : q.value = r.value) (hfirst : q.first = r.first)
    (hsecond : q.second = r.second) : q = r := by
  cases q
  cases r
  cases hvalue
  cases hfirst
  cases hsecond
  rfl

theorem frameMetricJet_eq_coordinateMetricJet
    (g : RiemannianMetric n M) (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) :
    frameMetricJet g (chartFrame p) x =
      coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n)) (chartMetricCoefficients g p)
        (extChartAt (𝓡 n) p x) := by
  apply metricJet2_eq_of_components
  · exact frameMetricJet_value_eq_chartMetricCoefficients g p hx
  · funext a i j
    exact frameMetricJet_first_eq_chartCoefficient_derivative g p hx a i j
  · funext a b i j
    exact frameMetricJet_second_eq_chartCoefficient_derivative g p hx a b i j

theorem ricci_eq_coordinateRicciJet
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (p : M)
    {x : M} (hx : x ∈ (chartAt E p).source) (i j : Fin n) :
    D.ricci x (chartFrame p i x) (chartFrame p j x) =
      ricciJet (coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
        (chartMetricCoefficients g p) (extChartAt (𝓡 n) p x)) i j := by
  rw [ricci_eq_ricciJet_chartFrame D p hx, frameMetricJet_eq_coordinateMetricJet g p hx]

end PoincareConjecture.DeTurckNative

end
