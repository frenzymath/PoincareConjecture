import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityWeakCritical
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusContinuousWeakMinimizer
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalSmooth

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem M64ObservedWeakAnnulus.contMDiffOn_of_energy_minimum
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q)
    (hA : ContinuousOn A.map S) : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map S := by
  intro a ha
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
  have hcritical := A.weak_critical_coordinates g he hei Q hQ hb hdiag hmin b
    hR hRS hu huT hW hwu hmap
  have hsmooth := M60.suWeakAlphaCoordinate_smooth_alpha_one g b u
    (fun i p => L (A.column i p)) a ((R / 4) * Real.exp (-1)) hcritical
  have haR : a ∈ Metric.closedBall a R := Metric.mem_closedBall_self hR.le
  have hi := (contMDiffOn_extChartAt_symm (n := ∞) b _ (huT haR)).contMDiffAt
    ((isOpen_extChartAt_target b).mem_nhds (huT haR))
  have hlocal : ContMDiffAt (𝓡 2) (𝓡 n) ∞ A.map a := by
    apply (hi.comp a (contMDiffAt_iff_contDiffAt.mpr hsmooth)).congr_of_eventuallyEq
    filter_upwards [Metric.closedBall_mem_nhds a hR] with p hp
    exact (hmap hp).symm
  exact hlocal.contMDiffWithinAt

theorem m64Annulus_exists_interior_smooth_weak_energy_minimizer
    [CompactSpace M] [T2Space M]
    {g : RiemannianMetric n M} (A0 : M64Annulus g c0 c1) :
    ∃ (m : ℕ) (e : M → EuclideanSpace ℝ (Fin m))
      (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (A : M64ObservedWeakAnnulus (n := n) e c0 c1),
      ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n) e ∧ Continuous Q ∧
      (∀ q v, 0 ≤ Q q v v) ∧ (∀ q v w, Q q v w = Q q w v) ∧
      (∀ (q : M) (v : TangentSpace (𝓡 n) q),
        Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v) ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map S ∧
      (∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q) ∧
      ∀ B : M64Annulus g c0 c1,
        A.energy Q ≤ ∫ p in S, m60EnergyDensity g B.map p := by
  obtain ⟨m, e, Q, A, he, hei, hread, hQ, hpos, hsymm, hdiag, hA, hmin, hbound⟩ :=
    m64Annulus_exists_interior_continuous_weak_energy_minimizer A0
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  have hsmooth := A.contMDiffOn_of_energy_minimum g (he.of_le (by simp)) hei.isEmbedding
    hread Q hQ (fun q => hC _ (mem_range_self q)) hdiag hmin hA
  exact ⟨m, e, Q, A, he, hei, hread, hQ, hpos, hsymm, hdiag, hsmooth, hmin, hbound⟩

end PoincareConjecture
