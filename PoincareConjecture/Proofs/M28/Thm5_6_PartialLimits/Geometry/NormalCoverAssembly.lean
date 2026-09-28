import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.IndexedCovering











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M28

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




theorem exists_normalChartCover_of_normal_charts
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) {r R ρ : ℝ} {N : ℕ}
    (hr : 0 < r) (hρ : 0 < ρ) (hρR : 2 * ρ < R)
    (hcover : ∃ C : Finset M, (↑C : Set M) ⊆ g.ball p r ∧ C.card ≤ N ∧
      g.ball p r ⊆ ⋃ q ∈ C, g.ball q (ρ / 4))
    (hcharts : ∀ q ∈ g.ball p r,
      ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 R ∧ Φ.target = g.ball q R ∧ Φ 0 = q ∧
        (∀ u w, g.pullbackCoefficients (extChartAt (𝓡 n) q).symm
          (extChartAt (𝓡 n) q q) (L u) (L w) = inner ℝ u w) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) q (Φ w)) L.toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 R,
          g.IsGeodesicOn (fun t => Φ (t • w)) {t : ℝ | t • w ∈ Metric.ball 0 R}) ∧
        (∀ w ∈ Metric.ball 0 R, g.edist q (Φ w) = ENNReal.ofReal ‖w‖) ∧
        ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ w,
          (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients Φ x w w ∧
            g.pullbackCoefficients Φ x w w ≤ (9 / 4 : ℝ) * ‖w‖ ^ 2) :
    Nonempty (NormalChartCover (fun _ => g) p (-1) 1 r R ρ (1 / 4) (9 / 4) (N + 1)) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨C, hC, hcard, hcover⟩ := hcover
  let S := insert p C
  have hp : p ∈ g.ball p r := by
    change g.edist p p < ENNReal.ofReal r
    have hself : g.edist p p = 0 := Manifold.riemannianEDist_self
    rw [hself]
    exact ENNReal.ofReal_pos.mpr hr
  have hS : (↑S : Set M) ⊆ g.ball p r := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hC hq
  obtain ⟨f, hfzero, hf⟩ := exists_surjective_fin_with_base
    (⟨p, Finset.mem_insert_self _ _⟩ : S) (N := N + 1) (by
      simpa only [Fintype.card_coe] using
        (Finset.card_insert_le p C).trans (Nat.add_le_add_right hcard 1))
  choose L Φ hsource htarget hzero hL hderiv hgeo hdist hcoeff using
    fun q : S => hcharts q (hS q.property)
  have hcore : g.ball p r ⊆ ⋃ q : S, Φ q '' Metric.closedBall 0 (ρ / 4) := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hcover hx)
    let q' : S := ⟨q, Finset.mem_insert_of_mem hq⟩
    have hxtarget : x ∈ (Φ q').target := by
      rw [htarget]
      exact hxq.trans_le (ENNReal.ofReal_le_ofReal (by linarith : ρ / 4 ≤ R))
    have hwsource : (Φ q').symm x ∈ Metric.ball 0 R := by
      rw [← hsource]
      exact (Φ q').map_target hxtarget
    have heq := (Φ q').right_inv hxtarget
    refine mem_iUnion.mpr ⟨q', (Φ q').symm x, ?_, heq⟩
    have hnorm := (congrArg (g.edist (q' : M)) heq).symm.trans
      (hdist q' ((Φ q').symm x) hwsource)
    have hsmall : ENNReal.ofReal ‖(Φ q').symm x‖ < ENNReal.ofReal (ρ / 4) := by
      rw [← hnorm]
      exact hxq
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < ρ / 4)).mp hsmall).le
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
    coefficients := fun i _ _ => hcoeff (f i)
    distances := ?_
    compact_image := ?_
    cover := ?_ }⟩
  · intro i x hx y hy
    apply g.toReal_edist_bounds_of_normal_pullback_bounds (f i) (Φ (f i))
      (by positivity) (by linarith) (by norm_num) (by norm_num)
      (hsource (f i)) (htarget (f i)) (hdist (f i))
      (fun z hz v => hcoeff (f i) z ?_ v) hx hy
    exact Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hz)
  · intro i
    apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (ρ / 4)).image_of_continuousOn
    apply (Φ (f i)).contMDiffOn.continuousOn.mono
    rw [hsource]
    exact Metric.closedBall_subset_ball (by linarith)
  · intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcore hx)
    obtain ⟨i, rfl⟩ := hf q
    exact mem_iUnion.mpr ⟨i, hq⟩

end PoincareConjecture.M28
