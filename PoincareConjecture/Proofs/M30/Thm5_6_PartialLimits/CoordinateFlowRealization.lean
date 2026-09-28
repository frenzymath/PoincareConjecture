import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.CoordinateMetricFamily
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.WithinFlowService













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

private theorem opens_extChartAt_target
    {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n))) (p : U) :
    (extChartAt (𝓡 n) p).target = (U : Set (EuclideanSpace ℝ (Fin n))) := by
  simp [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr]

private theorem pullbackCoefficients_opensChart
    {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n)))
    (g : RiemannianMetric n U) (p x : U) :
    g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (x : EuclideanSpace ℝ (Fin n)) = g.inner x := by
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x)
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
  have hc : extChartAt (𝓡 n) p = extChartAt (𝓡 n) x := by
    simp [extChartAt, Opens.chartAt_eq]
  rw [hc]
  ext v w
  change g.inner ((extChartAt (𝓡 n) x).symm x)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm x v)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm x w) = g.inner x v w
  have hx : (extChartAt (𝓡 n) x).symm (x : EuclideanSpace ℝ (Fin n)) = x :=
    (extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)
  change mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
    (x : EuclideanSpace ℝ (Fin n)) = ContinuousLinearMap.id ℝ _ at hd
  rw [hd, hx]
  rfl

set_option synthInstance.maxHeartbeats 100000 in




theorem exists_flow_of_coordinate_coefficients
    (hFlow : WithinBilinearFlowService.{0})
    {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n)))
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (Fseq : ℕ → RicciFlow n U J)
    (Bseq : ℕ → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (J ×ˢ (U : Set (EuclideanSpace ℝ (Fin n)))))
    (hcoeff : ∀ k t, t ∈ J → ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      ((Fseq k).metric t).inner x v w = Bseq k (t, x) v w)
    (hsymm : ∀ t ∈ J, ∀ x ∈ U, ∀ v w, B (t, x) v w = B (t, x) w v)
    (hlower : ∀ t ∈ J, ∀ x ∈ U, ∃ c : ℝ, 0 < c ∧
      ∀ v, c * ‖v‖ ^ 2 ≤ B (t, x) v v)
    (hjets : ∀ m (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ J ×ˢ (U : Set (EuclideanSpace ℝ (Fin n))) →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (Bseq k)
          (J ×ˢ (U : Set (EuclideanSpace ℝ (Fin n)))))
        (iteratedFDerivWithin ℝ m B
          (J ×ˢ (U : Set (EuclideanSpace ℝ (Fin n))))) atTop K) :
    ∃ F : RicciFlow n U J, ∀ t ∈ J,
      ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
        (F.metric t).inner x v w = B (t, x) v w := by
  obtain ⟨t₀, ht₀⟩ := (Fseq 0).nontrivial.nonempty
  obtain ⟨g, hg, hgcoeff⟩ :=
    exists_smooth_metricFamily_of_coefficients U t₀ ht₀ B hB hsymm hlower
  obtain ⟨F, hF⟩ := hFlow Fseq g hJ hg (by
    intro p m K hK hKdomain
    rw [opens_extChartAt_target U p] at hKdomain ⊢
    have hsource (k : ℕ) : EqOn
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq k).metric z.1).pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2)
        (Bseq k) (J ×ˢ (U : Set (EuclideanSpace ℝ (Fin n)))) := by
      intro z hz
      dsimp only
      rw [pullbackCoefficients_opensChart U ((Fseq k).metric z.1) p ⟨z.2, hz.2⟩]
      ext v w
      exact hcoeff k z.1 hz.1 ⟨z.2, hz.2⟩ v w
    have htarget : EqOn
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          (g z.1).pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2)
        B (J ×ˢ (U : Set (EuclideanSpace ℝ (Fin n)))) := by
      intro z hz
      dsimp only
      rw [pullbackCoefficients_opensChart U (g z.1) p ⟨z.2, hz.2⟩]
      ext v w
      exact hgcoeff z.1 hz.1 ⟨z.2, hz.2⟩ v w
    exact ((hjets m K hK hKdomain).congr
      (Eventually.of_forall fun k =>
        ((hsource k).iteratedFDerivWithin m).symm.mono hKdomain)).congr_right
      ((htarget.iteratedFDerivWithin m).symm.mono hKdomain))
  refine ⟨F, ?_⟩
  simpa only [hF] using hgcoeff

end PoincareConjecture.M30
