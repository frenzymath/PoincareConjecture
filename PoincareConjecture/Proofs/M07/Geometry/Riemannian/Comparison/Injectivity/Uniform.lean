import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.CanonicalPowers
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.CenterPacking
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Noncollapse
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PackingScale
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PrecompactData
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.BallDiffeomorphism















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric



def localInjectivityRadius (n : ℕ) (K R v : ℝ) : ℝ :=
  let s := min R (Poincare.ODE.Jacobi.comparisonRadius K)
  packingInjectivityRadius n s (smallerBallVolumeBound n K R v (s / 4))

theorem localInjectivityRadius_pos (n : ℕ) (K : ℝ) {R : ℝ} (hR : 0 < R) (v : ℝ) :
    0 < localInjectivityRadius n K R v :=
  packingInjectivityRadius_pos n
    (lt_min hR (Poincare.ODE.Jacobi.comparisonRadius_pos K)) _

theorem localInjectivityRadius_lt (n : ℕ) (K : ℝ) {R : ℝ} (hR : 0 < R) (v : ℝ) :
    localInjectivityRadius n K R v < R :=
  (packingInjectivityRadius_lt n
    (lt_min hR (Poincare.ODE.Jacobi.comparisonRadius_pos K)) _).trans_le (min_le_left _ _)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem exists_precompact_exponential_injective_of_noncollapse
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {K R v : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K) (hR : 0 < R) (hv : 0 < v)
    (hcompact : IsCompact (closure (g.ball p (2 * R))))
    (hcurv : ∀ x ∈ g.ball p (2 * R), D.curvatureTensorNorm x ≤ K)
    (hvol : letI : LocallyCompactSpace M :=
        ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p R)) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let s := min R (Poincare.ODE.Jacobi.comparisonRadius K)
    let ρ := localInjectivityRadius n K R v
    ∃ L : E ≃L[ℝ] E, ∃ e : E → M,
      (∀ a b, g.pullbackCoefficients c.symm (c p) (L a) (L b) = inner ℝ a b) ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
      HasFDerivAt (fun w => c (e w)) L.toContinuousLinearMap 0 ∧
      (∀ w ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t : ℝ => e (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 R} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (e (t • w))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • w)) t 1) = ‖w‖ ∧
          g.edist p (e (t • w)) ≤ ENNReal.ofReal ‖w‖ * ENNReal.ofReal t) ∧
      (∀ x ∈ Metric.ball 0 s, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e x)) ∧
      InjOn e (Metric.closedBall 0 ρ) := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  dsimp only
  let s := min R (Poincare.ODE.Jacobi.comparisonRadius K)
  let w := smallerBallVolumeBound n K R v (s / 4)
  let N := packingCount n s w
  let ρ := packingInjectivityRadius n s w
  have hs : 0 < s := lt_min hR (Poincare.ODE.Jacobi.comparisonRadius_pos K)
  have hsR : s ≤ R := min_le_left _ _
  have hsK : s ≤ Poincare.ODE.Jacobi.comparisonRadius K := min_le_right _ _
  have hsubR : g.ball p R ⊆ g.ball p (2 * R) := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hcompactR : IsCompact (closure (g.ball p R)) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono hsubR)
  have hsubs : g.ball p s ⊆ g.ball p R := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hsR)
  have hcompacts : IsCompact (closure (g.ball p s)) :=
    hcompactR.of_isClosed_subset isClosed_closure (closure_mono hsubs)
  obtain ⟨hw, hsmallvol⟩ := g.smallerBall_volume_lower_bound_of_curvatureTensorNorm_le
    D p hn hK hR hv hcompact hcurv hvol (s := s / 4) (by linarith) (by linarith)
  obtain ⟨L, e, hL, he, he0, hed, hgeo, hgauss, hb, hloop, _, hmaps⟩ :=
    g.exists_precompact_exponential_with_injectivity_data D p hR hK hcompactR
      (fun x hx => hcurv x (hsubR hx))
  refine ⟨L, e, hL, he, he0, hed, hgeo, fun x hx => (hb x hx).1, ?_⟩
  change InjOn e (Metric.closedBall 0 ρ)
  by_contra hnot
  obtain ⟨z, hzpos, hzρ, hzreturn⟩ := hloop ρ
    (packingInjectivityRadius_pos n hs w) (twice_packingInjectivityRadius_lt n hs w) hnot
  have hthreshold := norm_two_smul_le_loopPowerThreshold n hzρ
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball hsR
  have hbij := fun x hx => (hb x hx).1
  have hbounds := fun x hx a => (hb x hx).2 a
  have hes := he.mono hsub
  have hspeeds (a) (ha : a ∈ Metric.ball 0 s) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    ((hgeo a (hsub ha)).2 t ht).1
  obtain ⟨y, hy, hyp⟩ := g.exists_distinct_radial_loop_powers D hs hsK hes
    hbounds (fun x hx a => hgauss x (hsub hx) a)
    (fun x hx => hcurv _ (hsubR (hsubs (hmaps s hs hsR hx))))
    (fun a ha t ht => (hspeeds a ha t ht).le)
    N (packingCount_pos n s w) ((2 : ℝ) • z)
    (smul_ne_zero (by norm_num) (norm_pos_iff.mp hzpos)) (hzreturn.trans he0.symm) hthreshold
  have hpack := g.mul_volumeMeasure_ball_le_of_center_fiber p hs hcompacts L e hL hes he0 hed
    (fun a ha t ht => (hgeo a (hsub ha)).1 t (hsub ht)) hspeeds hbounds
    (r := s / 4) (by linarith) (by linarith) y hy
    (fun i => (hyp i).1.trans he0)
    (fun i => loop_endpoint_center_lift_margin hs (norm_nonneg _) N hthreshold
      i.val (by omega) (y i) (hyp i).2)
  have hmass := packingMass_lt_count_mul_volume n s hw
  exact (not_lt_of_ge hpack) (hmass.trans_le (mul_le_mul_right hsmallvol _))





theorem exists_uniform_precompact_exponential_diffeomorph
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {K R v : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K) (hR : 0 < R) (hv : 0 < v)
    (hcompact : IsCompact (closure (g.ball p (2 * R))))
    (hcurv : ∀ x ∈ g.ball p (2 * R), D.curvatureTensorNorm x ≤ K)
    (hvol : letI : LocallyCompactSpace M :=
        ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p R)) :
    let ρ := localInjectivityRadius n K R v
    0 < ρ ∧ ρ < R ∧
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
    ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      Φ.source = Metric.ball 0 ρ ∧ Φ.target = g.ball p ρ ∧ Φ 0 = p ∧
      (∀ a b, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (extChartAt (𝓡 n) p p) (L a) (L b) = inner ℝ a b) ∧
      HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w)) L.toContinuousLinearMap 0 ∧
      (∀ w ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t : ℝ => Φ (t • w))
          {t : ℝ | t • w ∈ Metric.ball 0 R}) ∧
      ∀ w ∈ Metric.ball 0 ρ, g.edist p (Φ w) = ENNReal.ofReal ‖w‖ := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  dsimp only
  let ρ := localInjectivityRadius n K R v
  have hρ : 0 < ρ := localInjectivityRadius_pos n K hR v
  have hρR : ρ < R := localInjectivityRadius_lt n K hR v
  obtain ⟨L, e, hL, he, he0, hed, hgeo, hbij, hinj⟩ :=
    g.exists_precompact_exponential_injective_of_noncollapse D p hn hK hR hv
      hcompact hcurv hvol
  have hcompactR : IsCompact (closure (g.ball p R)) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono (fun x hx =>
      hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith : R ≤ 2 * R))))
  have hρs : ρ < min R (Poincare.ODE.Jacobi.comparisonRadius K) :=
    packingInjectivityRadius_lt n
      (lt_min hR (Poincare.ODE.Jacobi.comparisonRadius_pos K)) _
  obtain ⟨Φ, hΦ, hsource, htarget, hradial⟩ :=
    g.exists_ball_partialDiffeomorph_of_precompact_exponential p hR hcompactR L e
      hL he he0 hed (fun w hw => (hgeo w hw).1)
      (fun w hw => by simpa using ((hgeo w hw).2 1 (by simp)).2) hρ hρR
      (fun w hw => hbij w (Metric.ball_subset_ball hρs.le hw)) hinj
  refine ⟨hρ, hρR, L, Φ, hsource, htarget, ?_, hL, ?_, ?_, ?_⟩
  · rw [hΦ, he0]
  · simpa only [hΦ] using hed
  · simpa only [hΦ] using (fun w hw => (hgeo w hw).1)
  · simpa only [hΦ] using hradial

end PoincareConjecture.RiemannianMetric
