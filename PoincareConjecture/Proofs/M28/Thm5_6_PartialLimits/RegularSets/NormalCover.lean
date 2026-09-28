import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.VolumeCover
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.NormalCharts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.DistanceLower












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M28



structure RegularNormalChartCover {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) (δ R ρ : ℝ) (N : ℕ) where
  centre : Fin (N + 1) → M
  chart : Fin (N + 1) → PartialDiffeomorph (𝓡 n) (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) M ∞
  centre_zero : centre 0 = p
  centre_mem : ∀ i, centre i ∈ regularComponent g p (4 * δ)
  source : ∀ i, (chart i).source = Metric.ball 0 R
  target : ∀ i, (chart i).target = g.ball (centre i) R
  map_zero : ∀ i, chart i 0 = centre i
  normalized : ∀ i, ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
    (∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) (centre i)).symm
      (extChartAt (𝓡 n) (centre i) (centre i)) (L v) (L w) = inner ℝ v w) ∧
    HasFDerivAt (fun w => extChartAt (𝓡 n) (centre i) (chart i w)) L.toContinuousLinearMap 0
  radial_geodesic : ∀ i, ∀ w ∈ Metric.ball 0 R,
    g.IsGeodesicOn (fun t => chart i (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 R}
  radial_distance : ∀ i, ∀ w ∈ Metric.ball 0 R,
    g.edist (centre i) (chart i w) = ENNReal.ofReal ‖w‖
  coefficients : ∀ i, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ w,
    (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients (chart i) x w w ∧
      g.pullbackCoefficients (chart i) x w w ≤ (9 / 4 : ℝ) * ‖w‖ ^ 2
  distances : ∀ i, ∀ x ∈ Metric.ball 0 (ρ / 2), ∀ y ∈ Metric.ball 0 (ρ / 2),
    Real.sqrt (1 / 4 : ℝ) * dist x y ≤ (g.edist (chart i x) (chart i y)).toReal ∧
      (g.edist (chart i x) (chart i y)).toReal ≤ Real.sqrt (9 / 4 : ℝ) * dist x y
  compact_image : ∀ i, IsCompact ((chart i) '' Metric.closedBall 0 (ρ / 8))
  cover : regularComponent g p (4 * δ) ⊆ ⋃ i, (chart i) '' Metric.closedBall 0 (ρ / 8)
  target_regular : ∀ i, (chart i).target ⊆ regularComponent g p (2 * δ)

private theorem exists_surjective_fin_with_base {α : Type*} [Fintype α]
    (a : α) {N : ℕ} (hN : Fintype.card α ≤ N) :
    ∃ f : Fin (N + 1) → α, f 0 = a ∧ Function.Surjective f := by
  classical
  let : Nonempty α := ⟨a⟩
  let e : α ↪ Fin N :=
    { toFun := fun x => ⟨(Fintype.equivFin α x).val,
        (Fintype.equivFin α x).isLt.trans_le hN⟩
      inj' := fun x y h => (Fintype.equivFin α).injective
        (Fin.ext (congrArg (fun z : Fin N => z.val) h)) }
  refine ⟨Fin.cases a (Function.invFun e), rfl, ?_⟩
  intro x
  exact ⟨(e x).succ, Function.leftInverse_invFun e.injective x⟩





theorem exists_uniform_regular_normal_cover
    (n : ℕ) {K δ r₀ κ V : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K)
    (hδ : 0 < δ) (hr₀ : 0 < r₀) (hκ : 0 < κ) (hV : 0 ≤ V) :
    ∃ R ρ : ℝ, ∃ N : ℕ, 0 < ρ ∧ 2 * ρ < R ∧ R < δ ∧ ρ ≤ r₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [SecondCountableTopology M] [PreconnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M),
      p ∈ regularPoints g (4 * δ) →
      (∀ x ∈ regularComponent g p (2 * δ), D.curvatureTensorNorm x ≤ K) →
      (∀ s : ℝ, 0 < s → s ≤ r₀ → ∀ q ∈ regularComponent g p s,
        (∀ x ∈ g.ball q s, |D.curvatureTensorNorm x| ≤ s⁻¹ ^ 2) →
        ENNReal.ofReal (κ * s ^ n) ≤ g.volumeMeasure (g.ball q s)) →
      g.volumeMeasure univ ≤ ENNReal.ofReal V →
      Nonempty (RegularNormalChartCover g p δ R ρ N) := by
  classical
  obtain ⟨R, ρ', hρ', hρ'R, hRδ, hcharts⟩ :=
    exists_uniform_regular_normal_charts n hn hK hδ hr₀ hκ
  have hKone : 0 < K + 1 := by linarith
  let ρ := min ρ' (min r₀ (K + 1)⁻¹)
  have hρ : 0 < ρ := lt_min hρ' (lt_min hr₀ (inv_pos.mpr hKone))
  have hρle : ρ ≤ ρ' := min_le_left _ _
  have hρr₀ : ρ ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hρK : ρ ≤ (K + 1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hρR : 2 * ρ < R := (mul_le_mul_of_nonneg_left hρle (by norm_num)).trans_lt hρ'R
  have hpack : 0 < (ρ / 8) / 2 := by positivity
  have hpackr₀ : (ρ / 8) / 2 ≤ r₀ := by linarith
  have hpackK : (ρ / 8) / 2 ≤ (K + 1)⁻¹ := by linarith
  have hKinv : K + 1 ≤ ((ρ / 8) / 2)⁻¹ := by
    simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr hKone) hpack).mpr hpackK
  have hKbound : K ≤ ((ρ / 8) / 2)⁻¹ ^ 2 :=
    (show K ≤ (K + 1) ^ 2 by nlinarith only [hK, sq_nonneg K]).trans
      (pow_le_pow_left₀ hKone.le hKinv 2)
  let N : ℕ := ⌈V / (κ * ((ρ / 8) / 2) ^ n)⌉₊ + 1
  refine ⟨R, ρ, N, hρ, hρR, hRδ, hρr₀, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D p hp hcurv hnoncollapse hupper
  have hlower : ∀ q ∈ regularComponent g p (4 * δ),
      ENNReal.ofReal (κ * ((ρ / 8) / 2) ^ n) ≤
        g.volumeMeasure (g.ball q ((ρ / 8) / 2)) := by
    intro q hq
    apply hnoncollapse ((ρ / 8) / 2) hpack hpackr₀ q
      (regularComponent_antitone g p (by linarith) hq)
    intro x hx
    have hxreg : x ∈ regularComponent g p (2 * δ) :=
      ball_subset_regularComponent g hq hpack (by linarith) hx
    rw [abs_of_nonneg (show 0 ≤ D.curvatureTensorNorm x from Real.sqrt_nonneg _)]
    exact (hcurv x hxreg).trans hKbound
  obtain ⟨C, hC, hcard, _hsep, hcover⟩ :=
    exists_finset_regularComponent_cover g p (4 * δ) (r := ρ / 8)
      (v := κ * ((ρ / 8) / 2) ^ n)
      (by positivity) (by positivity) hV hupper hlower
  let S := insert p C
  have hS : (↑S : Set M) ⊆ regularComponent g p (4 * δ) := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact mem_regularComponent g hp
    · exact hC hq
  obtain ⟨f, hfzero, hf⟩ := exists_surjective_fin_with_base
    (⟨p, Finset.mem_insert_self _ _⟩ : S) (N := N) (by
      simpa only [Fintype.card_coe, N] using
        (Finset.card_insert_le p C).trans (Nat.add_le_add_right hcard 1))
  choose L Φ hsource htarget hzero hL hderiv hgeo hdist hcoeff hregular using
    fun q : S => hcharts M g D p hcurv hnoncollapse q (hS q.property)
  have hcoeff' (q : S) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ Metric.closedBall 0 (2 * ρ)) (w : EuclideanSpace ℝ (Fin n)) :
      (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients (Φ q) x w w ∧
        g.pullbackCoefficients (Φ q) x w w ≤ (9 / 4 : ℝ) * ‖w‖ ^ 2 :=
    hcoeff q x (Metric.closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_left hρle (by norm_num)) hx) w
  have hcore : regularComponent g p (4 * δ) ⊆
      ⋃ q : S, (Φ q) '' Metric.closedBall 0 (ρ / 8) := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hcover hx)
    let q' : S := ⟨q, Finset.mem_insert_of_mem hq⟩
    have hxtarget : x ∈ (Φ q').target := by
      rw [htarget]
      exact hxq.trans_le (ENNReal.ofReal_le_ofReal (by linarith : ρ / 8 ≤ R))
    have hwsource : (Φ q').symm x ∈ Metric.ball 0 R := by
      rw [← hsource]
      exact (Φ q').map_target hxtarget
    have heq := (Φ q').right_inv hxtarget
    refine mem_iUnion.mpr ⟨q', (Φ q').symm x, ?_, heq⟩
    have hnorm := (congrArg (g.edist (q' : M)) heq).symm.trans
      (hdist q' ((Φ q').symm x) hwsource)
    have hsmall : ENNReal.ofReal ‖(Φ q').symm x‖ < ENNReal.ofReal (ρ / 8) := by
      rw [← hnorm]
      exact hxq
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < ρ / 8)).mp hsmall).le
  refine ⟨{
    centre := fun i => f i
    chart := fun i => Φ (f i)
    centre_zero := congrArg Subtype.val hfzero
    centre_mem := fun i => hS (f i).property
    source := fun i => hsource (f i)
    target := fun i => htarget (f i)
    map_zero := fun i => hzero (f i)
    normalized := fun i => ⟨L (f i), hL (f i), hderiv (f i)⟩
    radial_geodesic := fun i => hgeo (f i)
    radial_distance := fun i => hdist (f i)
    coefficients := fun i => hcoeff' (f i)
    distances := ?_
    compact_image := ?_
    cover := ?_
    target_regular := fun i => hregular (f i) }⟩
  · intro i x hx y hy
    apply g.toReal_edist_bounds_of_normal_pullback_bounds (f i) (Φ (f i))
      (by positivity) (by linarith) (by norm_num) (by norm_num)
      (hsource (f i)) (htarget (f i)) (hdist (f i))
      (fun z hz v => hcoeff' (f i) z ?_ v) hx hy
    exact Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz)
  · intro i
    apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (ρ / 8)).image_of_continuousOn
    apply (Φ (f i)).contMDiffOn.continuousOn.mono
    rw [hsource]
    exact Metric.closedBall_subset_ball (by linarith)
  · intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcore hx)
    obtain ⟨i, rfl⟩ := hf q
    exact mem_iUnion.mpr ⟨i, hq⟩

end PoincareConjecture.M28
