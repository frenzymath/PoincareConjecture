import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.UniformConeDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RayDensity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RiemannianLink












noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}


def rescaledClosedAnnulus (p : X) (L a b : ℝ) : Set X :=
  {x | a ≤ dist p x / L ∧ dist p x / L ≤ b}


def asymptoticConeClosedAnnulus (hcomparison : RayComparison p) (a b : ℝ) :
    Set (AsymptoticCone p hcomparison) :=
  {z | a ≤ (asymptoticConeRadius hcomparison z : ℝ) ∧
    (asymptoticConeRadius hcomparison z : ℝ) ≤ b}



theorem isCompact_asymptoticConeClosedAnnulus [ProperSpace X]
    (hcomparison : RayComparison p) (a b : ℝ) :
    IsCompact (asymptoticConeClosedAnnulus hcomparison a b) := by
  have hradius : Continuous (fun z : AsymptoticCone p hcomparison =>
      (asymptoticConeRadius hcomparison z : ℝ)) :=
    continuous_subtype_val.comp (lipschitzWith_asymptoticConeRadius hcomparison).continuous
  apply (isCompact_asymptoticConeRadius_sublevel hcomparison b.toNNReal).of_isClosed_subset
  · change IsClosed ((fun z : AsymptoticCone p hcomparison =>
      (asymptoticConeRadius hcomparison z : ℝ)) ⁻¹' Icc a b)
    exact isClosed_Icc.preimage hradius
  · intro z hz
    exact NNReal.coe_le_coe.mp (hz.2.trans (Real.le_coe_toNNReal b))


def annulusConeRelation (hcomparison : RayComparison p) (L τ : ℝ)
    (x : X) (z : AsymptoticCone p hcomparison) : Prop :=
  ∃ γ : basedMinimizingRays p,
    asymptoticConeRayProjection hcomparison ((dist p x / L).toNNReal, γ) = z ∧
    dist x (rayExtension γ (dist p x)) / L < τ


theorem annulusConeRelation_radius (hcomparison : RayComparison p)
    {L τ : ℝ} (hL : 0 < L) {x : X} {z : AsymptoticCone p hcomparison}
    (h : annulusConeRelation hcomparison L τ x z) :
    (asymptoticConeRadius hcomparison z : ℝ) = dist p x / L := by
  obtain ⟨γ, rfl, _⟩ := h
  change ((dist p x / L).toNNReal : ℝ) = dist p x / L
  exact Real.coe_toNNReal _ (div_nonneg dist_nonneg hL.le)



theorem annulusConeRelation_surjective (hcomparison : RayComparison p)
    {L τ a b : ℝ} (hL : 0 < L) (hτ : 0 < τ)
    (z : asymptoticConeClosedAnnulus hcomparison a b) :
    ∃ x : rescaledClosedAnnulus p L a b,
      annulusConeRelation hcomparison L τ (x : X) (z : AsymptoticCone p hcomparison) := by
  obtain ⟨v, hv⟩ := surjective_asymptoticConeProjection hcomparison z.1
  obtain ⟨γ, hγ⟩ := surjective_asymptoticLinkProjection hcomparison v.2
  have hprojection : asymptoticConeRayProjection hcomparison (v.1, γ) = z.1 := by
    unfold asymptoticConeRayProjection
    rw [hγ]
    exact hv
  have hradius : asymptoticConeRadius hcomparison z.1 = v.1 := by
    rw [← hv, asymptoticConeRadius_projection]
  have hdist : dist p (rayExtension γ ((v.1 : ℝ) * L)) = (v.1 : ℝ) * L := by
    simpa only [rayExtension_zero, zero_sub, abs_neg,
      abs_of_nonneg (mul_nonneg v.1.coe_nonneg hL.le)] using
      rayExtension_dist γ (le_refl 0) (mul_nonneg v.1.coe_nonneg hL.le)
  have hratio : dist p (rayExtension γ ((v.1 : ℝ) * L)) / L = (v.1 : ℝ) := by
    rw [hdist, mul_div_cancel_right₀ _ hL.ne']
  have hx : rayExtension γ ((v.1 : ℝ) * L) ∈ rescaledClosedAnnulus p L a b := by
    change a ≤ dist p _ / L ∧ dist p _ / L ≤ b
    rw [hratio]
    simpa only [asymptoticConeClosedAnnulus, mem_ofPred_eq, hradius] using z.2
  refine ⟨⟨rayExtension γ ((v.1 : ℝ) * L), hx⟩, γ, ?_, ?_⟩
  · rw [hratio, Real.toNNReal_coe]
    exact hprojection
  · rw [hdist, dist_self, zero_div]
    exact hτ

private theorem annulusConeRelation_distortion
    (hcomparison : RayComparison p) {L τ δ b : ℝ} (hL : 0 < L)
    (hlimit : ∀ r s : ℝ≥0, r ≤ b.toNNReal → s ≤ b.toNNReal →
      ∀ γ η : basedMinimizingRays p,
        |dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L -
          dist (asymptoticConeRayProjection hcomparison (r, γ))
            (asymptoticConeRayProjection hcomparison (s, η))| < δ)
    {x y : X} {z w : AsymptoticCone p hcomparison}
    (hxbound : dist p x / L ≤ b) (hybound : dist p y / L ≤ b)
    (hx : annulusConeRelation hcomparison L τ x z)
    (hy : annulusConeRelation hcomparison L τ y w) :
    |dist x y / L - dist z w| < 2 * τ + δ := by
  obtain ⟨γ, hγ, hx⟩ := hx
  obtain ⟨η, hη, hy⟩ := hy
  have htime (q : X) : ((dist p q / L).toNNReal : ℝ) * L = dist p q := by
    rw [Real.coe_toNNReal _ (div_nonneg dist_nonneg hL.le), div_mul_cancel₀ _ hL.ne']
  have herror := hlimit (dist p x / L).toNNReal (dist p y / L).toNNReal
    (Real.toNNReal_mono hxbound) (Real.toNNReal_mono hybound) γ η
  rw [htime, htime, hγ, hη] at herror
  have hsource : |dist x y / L - dist (rayExtension γ (dist p x)) (rayExtension η (dist p y)) / L| ≤
      dist x (rayExtension γ (dist p x)) / L + dist y (rayExtension η (dist p y)) / L := by
    rw [← sub_div, abs_div, abs_of_pos hL, ← add_div]
    exact div_le_div_of_nonneg_right
      (by simpa only [Real.dist_eq] using
        dist_dist_dist_le x y (rayExtension γ (dist p x)) (rayExtension η (dist p y))) hL.le
  calc
    _ ≤ |dist x y / L - dist (rayExtension γ (dist p x)) (rayExtension η (dist p y)) / L| +
        |dist (rayExtension γ (dist p x)) (rayExtension η (dist p y)) / L - dist z w| :=
      abs_sub_le _ _ _
    _ ≤ (dist x (rayExtension γ (dist p x)) / L + dist y (rayExtension η (dist p y)) / L) +
        |dist (rayExtension γ (dist p x)) (rayExtension η (dist p y)) / L - dist z w| :=
      add_le_add hsource le_rfl
    _ < _ := by linarith

end Poincare.AncientVolume.ScalarRatio

open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio





theorem exists_annulusConeRelation_approximation_of_metricComplete
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M)
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Nonempty (rescaledClosedAnnulus p L a b) ∧
      (∀ x : rescaledClosedAnnulus p L a b,
        ∃ z : asymptoticConeClosedAnnulus hcomparison a b,
          annulusConeRelation hcomparison L (ε / 4) (x : M) z) ∧
      (∀ z : asymptoticConeClosedAnnulus hcomparison a b,
        ∃ x : rescaledClosedAnnulus p L a b,
          annulusConeRelation hcomparison L (ε / 4) (x : M) z) ∧
      (∀ (x : rescaledClosedAnnulus p L a b)
        (z : asymptoticConeClosedAnnulus hcomparison a b),
        annulusConeRelation hcomparison L (ε / 4) (x : M) z →
          (asymptoticConeRadius hcomparison z : ℝ) = (g.edist p (x : M)).toReal / L) ∧
      ∀ (x y : rescaledClosedAnnulus p L a b)
        (z w : asymptoticConeClosedAnnulus hcomparison a b),
        annulusConeRelation hcomparison L (ε / 4) (x : M) z →
        annulusConeRelation hcomparison L (ε / 4) (y : M) w →
        |(g.edist (x : M) (y : M)).toReal / L - dist z w| < ε := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
  obtain ⟨R, hR, happrox⟩ := g.exists_uniform_ray_approximation_on_annuli D hc hsec p
    ha (ha.trans_le hab) (show 0 < ε / 4 by positivity)
  obtain ⟨S, _, huniform⟩ := exists_uniform_cone_distance_bound hcomparison b.toNNReal
    (show 0 < ε / 2 by positivity)
  obtain ⟨γ₀⟩ := g.nonempty_basedMinimizingRays hc p
  let z₀ : asymptoticConeClosedAnnulus hcomparison a b :=
    ⟨asymptoticConeRayProjection hcomparison (a.toNNReal, γ₀), by
      change a ≤ (a.toNNReal : ℝ) ∧ (a.toNNReal : ℝ) ≤ b
      rw [Real.coe_toNNReal _ ha.le]
      exact ⟨le_rfl, hab⟩⟩
  refine ⟨max R S, hR.trans_le (le_max_left _ _), ?_⟩
  intro L hL
  have hLpos : 0 < L := (hR.trans_le (le_max_left R S)).trans_le hL
  have hsurj := annulusConeRelation_surjective hcomparison hLpos
    (show 0 < ε / 4 by positivity) (a := a) (b := b)
  obtain ⟨x₀, _⟩ := hsurj z₀
  refine ⟨⟨x₀⟩, ?_, hsurj, ?_, ?_⟩
  · intro x
    obtain ⟨ray, hzero, hmin, hnear⟩ := happrox L ((le_max_left R S).trans hL) (x : M)
      ((le_div_iff₀ hLpos).mp x.2.1) ((div_le_iff₀ hLpos).mp x.2.2)
    let γ := g.basedMinimizingRayOfEdist ray hzero hmin
    let z := asymptoticConeRayProjection hcomparison ((dist p (x : M) / L).toNNReal, γ)
    have hz : z ∈ asymptoticConeClosedAnnulus hcomparison a b := by
      change a ≤ ((dist p (x : M) / L).toNNReal : ℝ) ∧
        ((dist p (x : M) / L).toNNReal : ℝ) ≤ b
      rw [Real.coe_toNNReal _ (div_nonneg dist_nonneg hLpos.le)]
      exact x.2
    refine ⟨⟨z, hz⟩, γ, rfl, ?_⟩
    rw [g.rayExtension_basedMinimizingRayOfEdist ray hzero hmin dist_nonneg]
    exact hnear
  · intro x z hrel
    exact annulusConeRelation_radius hcomparison hLpos hrel
  · intro x y z w hx hy
    have hlimit (r s : ℝ≥0) (hr : r ≤ b.toNNReal) (hs : s ≤ b.toNNReal)
        (γ η : basedMinimizingRays p) :
        |dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L -
          dist (asymptoticConeRayProjection hcomparison (r, γ))
            (asymptoticConeRayProjection hcomparison (s, η))| < ε / 2 := by
      have h := huniform L ((le_max_right R S).trans hL) r s hr hs γ η
      rw [abs_of_nonneg h.1]
      exact h.2
    have h := annulusConeRelation_distortion hcomparison hLpos hlimit x.2.2 y.2.2 hx hy
    change |dist (x : M) (y : M) / L -
      dist (z : AsymptoticCone p hcomparison) (w : AsymptoticCone p hcomparison)| < ε
    linarith only [h]

end PoincareConjecture.RiemannianMetric
