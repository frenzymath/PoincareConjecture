import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseRescaledEquation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "E" => EuclideanSpace ℝ (Fin ((n + 1) + 1))




theorem auxiliaryCircle_free_phase_coordinates_contDiffAt
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (hB : Continuous B)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree,
      A.annulus.weightedEnergy B modulus ≤ C.annulus.weightedEnergy B modulus)
    (q : Q.charts.Point) {u : LoopPlane → E} {W : Fin 2 → LoopPlane → E}
    {p0 : LoopPlane} {R : ℝ} (hR : 0 < R) (hRS : closedBall p0 R ⊆ S)
    (hu : Continuous u)
    (huT : MapsTo u (closedBall p0 R) (extChartAt (𝓡 ((n + 1) + 1)) q).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball p0 R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball p0 R))
    (hmap : EqOn ((extChartAt (𝓡 ((n + 1) + 1)) q).symm ∘ u)
      A.annulus.map (closedBall p0 R)) : ContDiffAt ℝ ∞ u p0 := by
  let s := Real.sqrt modulus
  let D := m64SourceScale s (Real.sqrt_pos.mpr hmodulus).ne'
  obtain ⟨radius, hcritical⟩ := auxiliaryCircle_free_phase_rescaled_critical
    P Q e he hei Robs hRobs A g B hB hb hdiag hmodulus hminimum q hR hRS hu huT hW hw hmap
  have hsm := M60.suWeakAlphaCoordinate_smooth_alpha_one g q (u ∘ D)
    (fun i p => m64SourceScaleFactor s i • W i (D p)) (D.symm p0) radius hcritical
  have hcomp : (u ∘ D) ∘ D.symm = u := by funext p; simp
  have hsm' := hsm.comp p0 D.symm.contDiff.contDiffAt
  rwa [hcomp] at hsm'



theorem auxiliaryCircle_free_phase_contMDiffOn
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    (Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (hB : Continuous B)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree,
      A.annulus.weightedEnergy B modulus ≤ C.annulus.weightedEnergy B modulus)
    (hA : ContinuousOn A.annulus.map S) :
    ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.annulus.map S := by
  intro a ha
  obtain ⟨q, L, R, hR, hRS, hchart, hu0, -, hW, hw⟩ :=
    A.annulus.exists_local_chart_columns he.continuous hread hA ha
  obtain ⟨u, hu, heq⟩ := m64_exists_continuous_extension isClosed_closedBall hu0
  have hcoord (p : LoopPlane) (hp : p ∈ closedBall a R) :
      u p = extChartAt (𝓡 ((n + 1) + 1)) q (A.annulus.map p) :=
    (heq hp).trans (hchart p hp).2
  have huT : MapsTo u (closedBall a R) (extChartAt (𝓡 ((n + 1) + 1)) q).target := by
    intro p hp
    rw [hcoord p hp]
    exact (extChartAt (𝓡 ((n + 1) + 1)) q).map_source (hchart p hp).1
  have hmap : EqOn ((extChartAt (𝓡 ((n + 1) + 1)) q).symm ∘ u)
      A.annulus.map (closedBall a R) := by
    intro p hp
    change (extChartAt (𝓡 ((n + 1) + 1)) q).symm (u p) = A.annulus.map p
    rw [hcoord p hp, (extChartAt (𝓡 ((n + 1) + 1)) q).left_inv (hchart p hp).1]
  have hwu (i : Fin 2) (j : Fin ((n + 1) + 1)) : HasWeakPartialDeriv i
      (fun p => L (A.annulus.column i p) j) (fun p => u p j) (ball a R) := by
    apply m64WeakPartialDeriv_ae_congr ?_ (Eventually.of_forall fun _ => rfl) (hw i j)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hp
    exact congrArg (fun v : E => v j) (heq (ball_subset_closedBall hp)).symm
  have hsm := auxiliaryCircle_free_phase_coordinates_contDiffAt P Q e he hei
    Robs hRobs A g B hB hb hdiag hmodulus hminimum q hR hRS hu huT hW hwu hmap
  have haR : a ∈ closedBall a R := mem_closedBall_self hR.le
  have hi := (contMDiffOn_extChartAt_symm (n := ∞) q _ (huT haR)).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds (huT haR))
  have hlocal : ContMDiffAt (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.annulus.map a := by
    apply (hi.comp a (contMDiffAt_iff_contDiffAt.mpr hsm)).congr_of_eventuallyEq
    filter_upwards [closedBall_mem_nhds a hR] with p hp
    exact (hmap hp).symm
  exact hlocal.contMDiffWithinAt

end PoincareConjecture.M64
