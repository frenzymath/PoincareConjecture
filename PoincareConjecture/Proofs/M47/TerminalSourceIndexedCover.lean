import PoincareConjecture.Proofs.M47.TerminalSourceNormalFiniteCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]

structure TerminalSourceIndexedChartCover
    (g : RiemannianMetric 3 M) (p : M) (A R rho : ℝ) (N : ℕ) where
  chart : Fin (N + 1) → TerminalSourceChart g R
  centre_zero : (chart 0).centre = p
  centre_mem : ∀ i, (chart i).centre ∈ g.ball p A
  compact_image : ∀ i, IsCompact ((chart i).chart '' Metric.closedBall (0 : E) (rho / 4))
  cover : g.ball p A ⊆ ⋃ i, (chart i).chart '' Metric.closedBall (0 : E) (rho / 4)

private theorem exists_surjective_fin_with_zero {α : Type*} [Fintype α]
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

theorem terminalSource_exists_indexed_chart_cover
    (g : RiemannianMetric 3 M) (p : M) {A R rho : ℝ} {N : ℕ}
    (S : Finset M) (hbase : p ∈ S) (hS : (↑S : Set M) ⊆ g.ball p A)
    (hcard : S.card ≤ N) (chart : S → TerminalSourceChart g R)
    (hcentre : ∀ q, (chart q).centre = q.val)
    (hcompact : ∀ q, IsCompact ((chart q).chart '' Metric.closedBall (0 : E) (rho / 4)))
    (hcover : g.ball p A ⊆ ⋃ q : S, (chart q).chart '' Metric.closedBall (0 : E) (rho / 4)) :
    ∃ indexed : TerminalSourceIndexedChartCover g p A R rho N,
      ∃ f : Fin (N + 1) → S, f 0 = ⟨p, hbase⟩ ∧ Function.Surjective f ∧
        ∀ i, indexed.chart i = chart (f i) := by
  classical
  obtain ⟨f, hf0, hf⟩ := exists_surjective_fin_with_zero (⟨p, hbase⟩ : S)
    (by simpa only [Fintype.card_coe] using hcard)
  have hindexed : g.ball p A ⊆
      ⋃ i : Fin (N + 1), (chart (f i)).chart '' Metric.closedBall (0 : E) (rho / 4) := by
    intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨i, rfl⟩ := hf q
    exact mem_iUnion.mpr ⟨i, hq⟩
  refine ⟨{
    chart := fun i => chart (f i)
    centre_zero := (hcentre (f 0)).trans (congrArg Subtype.val hf0)
    centre_mem := fun i => hcentre (f i) ▸ hS (f i).property
    compact_image := fun i => hcompact (f i)
    cover := hindexed }, f, hf0, hf, fun _ => rfl⟩

variable [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]

theorem terminalSourceNormal_nonempty_indexed_chart_cover
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (p : M)
    {A R rho K : ℝ} (hA : 0 < A) (hrho : 0 < rho) (hrhoR : rho / 4 < R)
    (hK : 0 ≤ K) (hcompact : IsCompact (closure (g.ball p (5 * A))))
    (hcurv : ∀ x ∈ g.ball p (5 * A), D.curvatureTensorNorm x ≤ K)
    (hcharts : ∀ q ∈ g.ball p A, ∃ C : TerminalSourceChart g R, C.centre = q) :
    let d := min (A / 2) (rho / 4)
    Nonempty (TerminalSourceIndexedChartCover g p A R rho
      (⌈RiemannianMetric.modelVolume 3 K (3 * A) /
        RiemannianMetric.modelVolume 3 K (d / 2)⌉₊ + 1)) := by
  obtain ⟨S, hbase, hS, hcard, chart, hcentre, hcores, hcover⟩ :=
    terminalSourceNormal_exists_finite_chart_cover g D p hA hrho hrhoR hK
      hcompact hcurv hcharts
  obtain ⟨indexed, _⟩ := terminalSource_exists_indexed_chart_cover g p S hbase hS hcard
    chart hcentre hcores hcover
  exact ⟨indexed⟩

end PoincareConjecture.M47
