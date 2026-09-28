import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Jacobi.ManifoldComparison











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.ConjugateFrame

open ConnectionAlongCurve ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def chartCoefficient (g : RiemannianMetric n M) (q : ℝ → M)
    (P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (a : M) (t : ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q t)
  let Q := L.comp (P t)
  Q.inverse.comp ((jacobiCurvature (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
    (extChartAt (𝓡 n) a (q t)) (deriv ((extChartAt (𝓡 n) a) ∘ q) t)).comp Q)

set_option maxHeartbeats 1000000 in
theorem chartCoefficient_apply (D : LeviCivitaData g)
    {q : ℝ → M}
    (P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {a : M} {t : ℝ} (ha : q t ∈ (extChartAt (𝓡 n) a).source)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t) (u : EuclideanSpace ℝ (Fin n)) :
    chartCoefficient g q P a t u = (P t).inverse (D.curvature (q t) (P t u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q t)
  have hv : deriv ((extChartAt (𝓡 n) a) ∘ q) t =
      L (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
    have hd := mfderiv_comp t (mdifferentiableAt_extChartAt
      (by simpa only [extChartAt_source] using ha)) (hq.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    exact congrArg (fun f => f 1) hd
  have hB := (g.contDiffOn_chartCoefficients a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds ((extChartAt (𝓡 n) a).map_source ha))
  have hΓ := (contDiffAt_christoffelBilinear hB
    (g.isInvertible_chartCoefficients a ((extChartAt (𝓡 n) a).map_source ha))).differentiableAt
      (by simp)
  dsimp only [chartCoefficient, ContinuousLinearMap.comp_apply]
  change ((L.comp (P t)).inverse)
    (jacobiCurvature (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (extChartAt (𝓡 n) a (q t)) (deriv ((extChartAt (𝓡 n) a) ∘ q) t) (L (P t u))) = _
  rw [jacobiCurvature_apply hΓ, hv]
  have hcurv := coordinateCurvature_in_chart g D a ha (P t u)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
  change coordinateCurvature (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
    (extChartAt (𝓡 n) a (q t)) (L (P t u)) (L (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
      (L (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) = L (D.curvature (q t) (P t u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) at hcurv
  rw [hcurv]
  have hL : L.IsInvertible := isInvertible_mfderiv_extChartAt ha
  rw [hL.inverse_comp_apply_of_left, hL.inverse_apply_self]

theorem contDiffAt_chartCoefficient
    {q : ℝ → M}
    {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {a : M} {t : ℝ} (ha : q t ∈ (extChartAt (𝓡 n) a).source)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hPi : (P t).IsInvertible)
    (hP : ∀ u, ContDiffAt ℝ ∞ (chartField q a (fun s => P s u)) t) :
    ContDiffAt ℝ ∞ (chartCoefficient g q P a) t := by
  let L : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun s => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q s)
  let Q : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun s => (L s).comp (P s)
  have hQ : ContDiffAt ℝ ∞ Q t := contDiffAt_operator_of_apply hP
  have hL : (L t).IsInvertible := isInvertible_mfderiv_extChartAt ha
  have hi := ((hL.comp hPi).contDiffAt_map_inverse (n := ∞)).comp t hQ
  have hqc := contDiffAt_chart_curve hq ha
  have hdq : ContDiffAt ℝ ∞ (deriv ((extChartAt (𝓡 n) a) ∘ q)) t :=
    (hqc.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hC := (contDiffAt_jacobiCurvature
    ((g.contDiffOn_chartCoefficients a).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds ((extChartAt (𝓡 n) a).map_source ha)))
    (g.isInvertible_chartCoefficients a ((extChartAt (𝓡 n) a).map_source ha))).comp t
      (hqc.prodMk hdq)
  exact hi.clm_comp (hC.clm_comp hQ)

def coefficient (g : RiemannianMetric n M) (q : ℝ → M)
    (P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  chartCoefficient g q P (q t) t

theorem contDiffAt_coefficient (D : LeviCivitaData g)
    {q : ℝ → M} {I : Set ℝ}
    {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    {t : ℝ} (ht : t ∈ I) (hPi : (P t).IsInvertible)
    (hP : ∀ u, ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t) :
    ContDiffAt ℝ ∞ (coefficient g q P) t := by
  have hqt := fun s hs => hq.contMDiffAt (hI.mem_nhds (show s ∈ I from hs))
  have hs := contDiffAt_chartCoefficient (g := g) (mem_extChartAt_source _)
    (hqt t ht) hPi hP
  have heq : coefficient g q P =ᶠ[𝓝 t] chartCoefficient g q P (q t) := by
    filter_upwards [hI.mem_nhds ht, (hqt t ht).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (q t)).mem_nhds (mem_extChartAt_source _))]
      with s hsI hs
    apply ContinuousLinearMap.ext
    intro u
    exact (chartCoefficient_apply D P (mem_extChartAt_source _) (hqt s hsI) u).trans
      (chartCoefficient_apply D P hs (hqt s hsI) u).symm
  exact hs.congr_of_eventuallyEq heq

end PoincareConjecture.ConjugateFrame
