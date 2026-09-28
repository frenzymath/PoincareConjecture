import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakMinimizerInteriorSmooth
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitStrongEquation

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak CoordinateExponential ConnectionVariation
  ConjugateVariation

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem M64ObservedWeakAnnulus.exists_harmonic_chart_of_energy_minimum
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q)
    (hA : ContinuousOn A.map S) {a : LoopPlane} (ha : a ∈ S) :
    ∃ (b : M) (u : LoopPlane → EuclideanSpace ℝ (Fin n)) (R : ℝ),
      0 < R ∧ Metric.closedBall a R ⊆ S ∧
      ContDiffOn ℝ ∞ u (Metric.ball a R) ∧
      MapsTo u (Metric.closedBall a R) (extChartAt (𝓡 n) b).target ∧
      EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (Metric.closedBall a R) ∧
      ∀ p ∈ Metric.ball a R, (∑ i : Fin 2,
        covDerivAlong (christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)) u
          (fun q => fderiv ℝ u q (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) p) = 0 := by
  obtain ⟨b, L, R, hR, hRS, hchart, hu0, -, hW, hw⟩ :=
    A.exists_local_chart_columns he.continuous hread hA ha
  obtain ⟨u, hu, heq⟩ := m64_exists_continuous_extension Metric.isClosed_closedBall hu0
  have hcoord (p : LoopPlane) (hp : p ∈ Metric.closedBall a R) :
      u p = extChartAt (𝓡 n) b (A.map p) := (heq hp).trans (hchart p hp).2
  have huT : MapsTo u (Metric.closedBall a R) (extChartAt (𝓡 n) b).target := by
    intro p hp
    rw [hcoord p hp]
    exact (extChartAt (𝓡 n) b).map_source (hchart p hp).1
  have hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (Metric.closedBall a R) := by
    intro p hp
    change (extChartAt (𝓡 n) b).symm (u p) = A.map p
    rw [hcoord p hp, (extChartAt (𝓡 n) b).left_inv (hchart p hp).1]
  have hwu (i : Fin 2) (j : Fin n) : HasWeakPartialDeriv i
      (fun p => L (A.column i p) j) (fun p => u p j) (Metric.ball a R) := by
    apply m64WeakPartialDeriv_ae_congr ?_ (Eventually.of_forall fun _ => rfl) (hw i j)
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with p hp
    exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j)
      (heq (Metric.ball_subset_closedBall hp)).symm
  have hlocal (p : LoopPlane) (hp : p ∈ Metric.ball a R) :
      ContDiffAt ℝ ∞ u p ∧ (∑ i : Fin 2,
        covDerivAlong (christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)) u
          (fun q => fderiv ℝ u q (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) p) = 0 := by
    obtain ⟨s, hs, hsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (Metric.isOpen_ball.mem_nhds hp)
    have hsmallR : Metric.closedBall p s ⊆ Metric.closedBall a R :=
      hsmall.trans Metric.ball_subset_closedBall
    have hsmallB : Metric.ball p s ⊆ Metric.ball a R :=
      Metric.ball_subset_closedBall.trans hsmall
    have hcritical := A.weak_critical_coordinates g he hei Q hQ hb hdiag hmin b hs
      (hsmallR.trans hRS) hu (fun q hq => huT (hsmallR hq))
      (fun i => (hW i).mono_measure (Measure.restrict_mono hsmallB le_rfl))
      (fun i j => (hwu i j).restrict Metric.isOpen_ball hsmallB)
      (fun q hq => hmap (hsmallR hq))
    have hsmooth := M60.suWeakAlphaCoordinate_smooth_alpha_one g b u
      (fun i q => L (A.column i q)) p ((s / 4) * Real.exp (-1)) hcritical
    exact ⟨hsmooth, M60.suWeakAlphaCoordinate_harmonic_of_smooth hcritical hsmooth⟩
  exact ⟨b, u, R, hR, hRS, (fun p hp => (hlocal p hp).1.contDiffWithinAt), huT,
    hmap, (fun p hp => (hlocal p hp).2)⟩

end PoincareConjecture
