import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RankGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Rescaling
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.PointedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.RiemannianLimit








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff Poincare.Alexandrov Poincare.CurvatureIntegral
open scoped Manifold ContDiff Bundle
universe u
namespace PoincareConjecture.RiemannianMetric

private theorem pointedGHConvergesUnbounded_comp
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (h : PointedGHConvergesUnbounded X Y) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    PointedGHConvergesUnbounded (fun j => X (φ j)) Y := by
  intro r hr
  obtain ⟨δ, hδ, hpos, ⟨⟨C, hC⟩, hdist⟩⟩ := h r hr
  exact ⟨fun j => δ (φ j), hδ.comp hφ, fun j => hpos (φ j),
    ⟨C, fun j => hC (φ j)⟩, hdist.comp hφ⟩

private theorem dist_eq_mul_rescaled_inverse_square
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) {r : ℝ} (hr : 0 < r) (x y : M) :
    (g.edist x y).toReal =
      r * ((rescaledMetric g (r ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hr))).edist x y).toReal := by
  rw [rescaledMetric_edist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sqrt_inv, Real.sqrt_sq hr.le]
  field_simp



theorem rank_growth_of_four_badAscentRadius_rescaling_at_scaled_spire
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q : ∀ j, M j)
    {V Y : BasedMetricSpaceBundle.{u}} [ProperSpace V.carrier] [ProperSpace Y.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {σ θ cminus c cplus b ρ cap : ℝ}
    (hσ : 0 < σ)
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ))
    (hminus : cminus < c) (hplus : c < cplus)
    (hρ : 0 < ρ) (hρb : ρ < σ * b / 2) (hbcap : b ≤ cap)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (B : V.carrier → ℝ)
    (hmax : ∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
        HasLocalDistanceAscent cminus x y) → a ≤ B x)
    (hspire : ∀ y : V.carrier, y ≠ V.base → σ * B y ≤ dist y V.base)
    (hqball : ∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ)
    (hqref : ∀ j, letI := (g j).toMetricSpace
      badAscentRadius c b (q j) ≤ badAscentRadius c b (p j))
    (hqmin : ∀ j, letI := (g j).toMetricSpace
      ∀ z : M j, dist (p j) z ≤ ρ →
        badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z)
    (hapos : ∀ j, 0 < (letI := (g j).toMetricSpace; badAscentRadius c b (q j))) :
    let a : ℕ → ℝ := fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j)
    let G := fun j => rescaledMetric (g j) ((4 * a j) ^ 2)⁻¹
      (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hapos j))))
    PointedGHConvergesUnbounded (fun j => (G j).toBasedMetricSpace (q j)) Y →
      Tendsto (fun j => 4 * a j) atTop (𝓝 0) ∧
      (∀ᶠ j in atTop, 4 * a j ≤ 1) ∧
      (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
        ∀ y : Y.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
      (∀ NV NY : ℕ, ComparisonAnglePackingBound V.carrier θ NV →
        ComparisonAnglePackingBound Y.carrier θ NY →
          minLocalAnglePackingRank V.carrier θ < minLocalAnglePackingRank Y.carrier θ) := by
  dsimp only
  intro hnewconv
  let a : ℕ → ℝ := fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j)
  have ht (j : ℕ) : 0 < 4 * a j := mul_pos (by norm_num) (hapos j)
  let G := fun j => rescaledMetric (g j) ((4 * a j) ^ 2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos (ht j)))
  let Z : ℕ → BasedMetricSpaceBundle.{u} := fun j => (G j).toBasedMetricSpace (q j)
  exact rank_growth_of_mul_near_min_badAscentRadius_at_scaled_spire
    g D hcomplete hsec p q holdconv hσ hθ hθpi hc hcθ hminus hplus hρ hρb hbcap
    hascent B hmax hspire hqball hqref hqmin 4 (by norm_num)
    (fun j => 4 * a j) ht (fun _ => rfl)
    (Z := Z) (fun j => Equiv.refl (M j)) (fun _ => rfl)
    (fun j x y => dist_eq_mul_rescaled_inverse_square (g j) (ht j) x y) hnewconv



theorem exists_rescaled_pointed_limit_with_rank_growth_at_scaled_spire
    (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ N : ℕ,
      ∀ {M : ℕ → Type} [∀ j, TopologicalSpace (M j)]
        [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
        [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
        [∀ j, IsManifold (𝓡 n) ∞ (M j)],
      ∀ (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
        (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
        (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
        (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
          -1 ≤ (D j).sectionalCurvature x v w)
        (p q : ∀ j, M j)
        {V : BasedMetricSpaceBundle.{0}} [ProperSpace V.carrier],
      PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V →
      ∀ {σ cminus c cplus b ρ cap : ℝ},
      0 < σ → 0 ≤ c → c < Real.cos (2 * θ) → cminus < c → c < cplus →
      0 < ρ → ρ < σ * b / 2 → b ≤ cap →
      (∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
        HasLocalDistanceAscent cplus V.base y) →
      ∀ B : V.carrier → ℝ,
      (∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
        (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
          HasLocalDistanceAscent cminus x y) → a ≤ B x) →
      (∀ y : V.carrier, y ≠ V.base → σ * B y ≤ dist y V.base) →
      (∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ) →
      (∀ j, letI := (g j).toMetricSpace
        badAscentRadius c b (q j) ≤ badAscentRadius c b (p j)) →
      (∀ j, letI := (g j).toMetricSpace
        ∀ z : M j, dist (p j) z ≤ ρ →
          badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z) →
      ∀ hapos : ∀ j, 0 < (letI := (g j).toMetricSpace; badAscentRadius c b (q j)),
      let a : ℕ → ℝ := fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j)
      let G := fun j => rescaledMetric (g j) ((4 * a j) ^ 2)⁻¹
        (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hapos j))))
      ∃ φ : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
        StrictMono φ ∧ (∀ j, 4 * a (φ j) ≤ 1) ∧
        ProperSpace S.completedLimit.carrier ∧
        (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
          γ 0 = x ∧ γ 1 = y ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist x y) ∧
        PointedGHConvergesUnbounded
          (fun j => (G (φ j)).toBasedMetricSpace (q (φ j))) S.completedLimit ∧
        CurvatureGEnegOne S.completedLimit.carrier ∧
        ComparisonAnglePackingBound V.carrier θ N ∧
        ComparisonAnglePackingBound S.completedLimit.carrier θ N ∧
        (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
          ∀ y : S.completedLimit.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
        minLocalAnglePackingRank V.carrier θ <
          minLocalAnglePackingRank S.completedLimit.carrier θ := by
  classical
  obtain ⟨N, hN⟩ :=
    exists_comparisonAngle_packing_bound_of_sectional_pointed_limit.{0} n hθ
  refine ⟨N, ?_⟩
  intro M _ _ _ _ _ g D hcomplete hsec p q V _ holdconv
    σ cminus c cplus b ρ cap hσ hc hcθ hminus hplus hρ hρb hbcap hascent
    B hmax hspire hqball hqref hqmin hapos
  dsimp only
  let a : ℕ → ℝ := fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j)
  let r : ℕ → ℝ := fun j => 4 * a j
  have hr (j : ℕ) : 0 < r j := mul_pos (by norm_num) (hapos j)
  let G := fun j => rescaledMetric (g j) (r j ^ 2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos (hr j)))
  let DS := fun j => rescaledMetric_connection (g j) (D j) (r j ^ 2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos (hr j)))
  obtain ⟨hazero, _⟩ := tendsto_radius_and_dist_zero_of_selected_centers_at_scaled_spire
    g D hcomplete hsec p q holdconv hσ hc hminus hplus hρ hρb hbcap
    hascent B hmax hspire hqball hqref
  have hrzero : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_zero] using hazero.const_mul 4
  have hsmall : ∀ᶠ j in atTop, r j ≤ 1 :=
    (hrzero.eventually_lt_const zero_lt_one).mono (fun _ h => h.le)
  obtain ⟨ψ, hψ, hψsmall⟩ := Filter.extraction_of_frequently_atTop hsmall.frequently
  have hfactor (j : ℕ) : 1 ≤ (r (ψ j) ^ 2)⁻¹ :=
    (one_le_inv₀ (sq_pos_of_pos (hr (ψ j)))).mpr
      (by nlinarith only [hr (ψ j), hψsmall j])
  obtain ⟨ξ, S, hξ, hproper, hgeo, hnewconv⟩ :=
    exists_subseq_proper_geodesic_pointed_limit_of_metric_rescaling
      (fun j => g (ψ j)) (fun j => q (ψ j)) hn
      (fun j => hcomplete (ψ j)) (fun j => D (ψ j)) (fun j => hsec (ψ j))
      (fun j => (r (ψ j) ^ 2)⁻¹) hfactor
  let φ : ℕ → ℕ := ψ ∘ ξ
  have hφ : StrictMono φ := hψ.comp hξ
  let : ProperSpace S.completedLimit.carrier := hproper
  have hretained (j : ℕ) : r (φ j) ≤ 1 := hψsmall (ξ j)
  have hnew : PointedGHConvergesUnbounded
      (fun j => (G (φ j)).toBasedMetricSpace (q (φ j))) S.completedLimit := hnewconv
  have hcompG (j : ℕ) : MetricComplete (G (φ j)) :=
    metricComplete_rescaledMetric (g (φ j)) _ _ (hcomplete (φ j))
  have hsecG (j : ℕ) (x : M (φ j)) (v w : TangentSpace (𝓡 n) x) :
      -1 ≤ (DS (φ j)).sectionalCurvature x v w := by
    have hpos : 0 < (r (φ j) ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos (hr (φ j)))
    have hfrac : (1 : ℝ) / (r (φ j) ^ 2)⁻¹ ≤ 1 :=
      (div_le_one hpos).mpr (hfactor (ξ j))
    exact (neg_le_neg hfrac).trans
      (rescaledMetric_sectionalCurvature_lower_bound (g (φ j)) (D (φ j))
        _ hpos 1 (hsec (φ j)) x v w)
  have hcurv : CurvatureGEnegOne S.completedLimit.carrier :=
    curvatureGEnegOne_of_sectional_pointed_limit
      (fun j => G (φ j)) (fun j => q (φ j)) (fun j => DS (φ j))
      hcompG hsecG hnew
  have hpackV : ComparisonAnglePackingBound V.carrier θ N :=
    hN g p D hcomplete hsec holdconv
  have hpackY : ComparisonAnglePackingBound S.completedLimit.carrier θ N :=
    hN (fun j => G (φ j)) (fun j => q (φ j)) (fun j => DS (φ j))
      hcompG hsecG hnew
  have holdsub := pointedGHConvergesUnbounded_comp holdconv φ hφ.tendsto_atTop
  have hgrowth := rank_growth_of_four_badAscentRadius_rescaling_at_scaled_spire
    (fun j => g (φ j)) (fun j => D (φ j)) (fun j => hcomplete (φ j))
    (fun j => hsec (φ j)) (fun j => p (φ j)) (fun j => q (φ j))
    holdsub hσ hθ hθpi hc hcθ hminus hplus hρ hρb hbcap hascent B hmax hspire
    (fun j => hqball (φ j)) (fun j => hqref (φ j)) (fun j => hqmin (φ j))
    (fun j => hapos (φ j)) hnew
  exact ⟨φ, S, hφ, hretained, hproper, hgeo, hnew, hcurv, hpackV, hpackY,
    hgrowth.2.2.1, hgrowth.2.2.2 N N hpackV hpackY⟩


theorem rank_growth_of_four_badAscentRadius_rescaling
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p q : ∀ j, M j)
    {V Y : BasedMetricSpaceBundle.{u}} [ProperSpace V.carrier] [ProperSpace Y.carrier]
    (holdconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V)
    {θ cminus c cplus b ρ cap : ℝ}
    (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hc : 0 ≤ c) (hcθ : c < Real.cos (2 * θ))
    (hminus : cminus < c) (hplus : c < cplus)
    (hρ : 0 < ρ) (hρb : ρ < b / 2) (hbcap : b ≤ cap)
    (hascent : ∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
      HasLocalDistanceAscent cplus V.base y)
    (B : V.carrier → ℝ)
    (hmax : ∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
        HasLocalDistanceAscent cminus x y) → a ≤ B x)
    (hspire : ∀ y : V.carrier, y ≠ V.base → B y ≤ dist y V.base)
    (hqball : ∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ)
    (hqref : ∀ j, letI := (g j).toMetricSpace
      badAscentRadius c b (q j) ≤ badAscentRadius c b (p j))
    (hqmin : ∀ j, letI := (g j).toMetricSpace
      ∀ z : M j, dist (p j) z ≤ ρ →
        badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z)
    (hapos : ∀ j, 0 < (letI := (g j).toMetricSpace; badAscentRadius c b (q j))) :
    let a : ℕ → ℝ := fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j)
    let G := fun j => rescaledMetric (g j) ((4 * a j) ^ 2)⁻¹
      (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hapos j))))
    PointedGHConvergesUnbounded (fun j => (G j).toBasedMetricSpace (q j)) Y →
      Tendsto (fun j => 4 * a j) atTop (𝓝 0) ∧
      (∀ᶠ j in atTop, 4 * a j ≤ 1) ∧
      (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
        ∀ y : Y.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
      (∀ NV NY : ℕ, ComparisonAnglePackingBound V.carrier θ NV →
        ComparisonAnglePackingBound Y.carrier θ NY →
          minLocalAnglePackingRank V.carrier θ < minLocalAnglePackingRank Y.carrier θ) := by
  exact rank_growth_of_four_badAscentRadius_rescaling_at_scaled_spire
    (σ := 1) g D hcomplete hsec p q holdconv zero_lt_one hθ hθpi hc hcθ hminus hplus
    hρ (by simpa only [one_mul] using hρb) hbcap hascent B hmax
    (fun y hy => by simpa only [one_mul] using hspire y hy)
    hqball hqref hqmin hapos


theorem exists_rescaled_pointed_limit_with_rank_growth
    (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ N : ℕ,
      ∀ {M : ℕ → Type} [∀ j, TopologicalSpace (M j)]
        [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
        [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
        [∀ j, IsManifold (𝓡 n) ∞ (M j)],
      ∀ (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
        (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
        (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
        (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
          -1 ≤ (D j).sectionalCurvature x v w)
        (p q : ∀ j, M j)
        {V : BasedMetricSpaceBundle.{0}} [ProperSpace V.carrier],
      PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) V →
      ∀ {cminus c cplus b ρ cap : ℝ},
      0 ≤ c → c < Real.cos (2 * θ) → cminus < c → c < cplus →
      0 < ρ → ρ < b / 2 → b ≤ cap →
      (∀ y : V.carrier, 0 < dist V.base y → dist V.base y ≤ b →
        HasLocalDistanceAscent cplus V.base y) →
      ∀ B : V.carrier → ℝ,
      (∀ x : V.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
        (∀ y : V.carrier, 0 < dist x y → dist x y < 2 * a →
          HasLocalDistanceAscent cminus x y) → a ≤ B x) →
      (∀ y : V.carrier, y ≠ V.base → B y ≤ dist y V.base) →
      (∀ j, ((g j).edist (p j) (q j)).toReal ≤ ρ) →
      (∀ j, letI := (g j).toMetricSpace
        badAscentRadius c b (q j) ≤ badAscentRadius c b (p j)) →
      (∀ j, letI := (g j).toMetricSpace
        ∀ z : M j, dist (p j) z ≤ ρ →
          badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z) →
      ∀ hapos : ∀ j, 0 < (letI := (g j).toMetricSpace; badAscentRadius c b (q j)),
      let a : ℕ → ℝ := fun j => letI := (g j).toMetricSpace; badAscentRadius c b (q j)
      let G := fun j => rescaledMetric (g j) ((4 * a j) ^ 2)⁻¹
        (inv_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) (hapos j))))
      ∃ φ : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
        StrictMono φ ∧ (∀ j, 4 * a (φ j) ≤ 1) ∧
        ProperSpace S.completedLimit.carrier ∧
        (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
          γ 0 = x ∧ γ 1 = y ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist x y) ∧
        PointedGHConvergesUnbounded
          (fun j => (G (φ j)).toBasedMetricSpace (q (φ j))) S.completedLimit ∧
        CurvatureGEnegOne S.completedLimit.carrier ∧
        ComparisonAnglePackingBound V.carrier θ N ∧
        ComparisonAnglePackingBound S.completedLimit.carrier θ N ∧
        (∀ k : ℕ, HasSmallAngleConfiguration θ V.base k →
          ∀ y : S.completedLimit.carrier, HasSmallAngleConfiguration θ y (k + 1)) ∧
        minLocalAnglePackingRank V.carrier θ <
          minLocalAnglePackingRank S.completedLimit.carrier θ := by
  obtain ⟨N, hN⟩ := exists_rescaled_pointed_limit_with_rank_growth_at_scaled_spire
    n hn θ hθ hθpi
  refine ⟨N, ?_⟩
  intro M _ _ _ _ _ g D hcomplete hsec p q V _ holdconv
    cminus c cplus b ρ cap hc hcθ hminus hplus hρ hρb hbcap hascent
    B hmax hspire hqball hqref hqmin hapos
  exact hN g D hcomplete hsec p q holdconv (σ := 1) zero_lt_one hc hcθ hminus hplus
    hρ (by simpa only [one_mul] using hρb) hbcap hascent B hmax
    (fun y hy => by simpa only [one_mul] using hspire y hy)
    hqball hqref hqmin hapos

end PoincareConjecture.RiemannianMetric
