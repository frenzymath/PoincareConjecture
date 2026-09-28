import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.AnnularCover
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.MovingPoints
import Mathlib.Data.Finset.Sum
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CenterSelection
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.MaximalRadius
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.PointedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.RiemannianLimit
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.Rebase
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RankGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.AnnularStability









noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Set Filter Topology
namespace Poincare.CurvatureIntegral

theorem exists_finite_annular_spire_ball_refinement
    {Y : Type*} [MetricSpace Y] {K : Set Y} (hK : IsCompact K)
    (F S : Finset Y) (B : Y → ℝ)
    (hB : ∀ y ∈ F, 0 < B y)
    (hcover : K \ (S : Set Y) ⊆ ⋃ y ∈ F, Metric.ball y (B y / 4) \ {y})
    (σ : S → ℝ) (hσ : ∀ i, 0 < σ i) :
    ∃ E : Finset K, ∃ e : K → ℝ,
      (∀ z ∈ E, 0 < e z ∧
        ((∃ i : S, dist i.val z.val + 4 * e z < σ i) ∨
          ∃ y ∈ F, ∃ r : ℝ, 0 < r ∧ r ≤ B y / 3 ∧
            (113 / 96 : ℝ) * r + 4 * e z < dist y z.val ∧
            dist y z.val + 4 * e z < (19 / 16 : ℝ) * r)) ∧
      K ⊆ ⋃ z ∈ E, Metric.ball z.val (e z) := by
  classical
  have hlocal (x : K) : ∃ e : ℝ, 0 < e ∧
      ((∃ i : S, dist i.val x.val + 4 * e < σ i) ∨
        ∃ y ∈ F, ∃ r : ℝ, 0 < r ∧ r ≤ B y / 3 ∧
          (113 / 96 : ℝ) * r + 4 * e < dist y x.val ∧
          dist y x.val + 4 * e < (19 / 16 : ℝ) * r) := by
    by_cases hxS : x.val ∈ S
    · let i : S := ⟨x.val, hxS⟩
      refine ⟨σ i / 8, div_pos (hσ i) (by norm_num), Or.inl ⟨i, ?_⟩⟩
      change dist x.val x.val + 4 * (σ i / 8) < σ i
      rw [dist_self]
      linarith [hσ i]
    · obtain ⟨y, hyF, hy⟩ := mem_iUnion₂.mp (hcover ⟨x.property, hxS⟩)
      have hdy : 0 < dist y x.val := dist_pos.mpr (by
        intro h
        exact hy.2 (by simpa only [mem_singleton_iff] using h.symm))
      have hdB : dist y x.val < B y / 4 := Metric.mem_ball'.mp hy.1
      have hBy := hB y hyF
      obtain ⟨T, hT, hTx⟩ := exists_finite_radial_annulus_cover
        (isCompact_singleton : IsCompact ({x.val} : Set Y)) y
        (by norm_num : (0 : ℝ) < 113 / 96)
        (by norm_num : (113 / 96 : ℝ) < 19 / 16)
        (show 0 < B y / 3 by positivity)
        (show ({x.val} : Set Y) ⊆ {z | 0 < dist y z ∧ dist y z < (19 / 16) * (B y / 3)} by
          intro z hz
          rcases mem_singleton_iff.mp hz with rfl
          exact ⟨hdy, by linarith⟩)
      obtain ⟨r, hrT, hlo, hhi⟩ := mem_iUnion₂.mp (hTx (mem_singleton x.val))
      let e : ℝ := min (dist y x.val - (113 / 96) * r)
        ((19 / 16) * r - dist y x.val) / 8
      have he : 0 < e := by
        apply div_pos
        · exact lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
        · norm_num
      refine ⟨e, he, Or.inr ⟨y, hyF, r, (hT r hrT).1, (hT r hrT).2, ?_, ?_⟩⟩
      · have hmin := min_le_left (dist y x.val - (113 / 96) * r)
          ((19 / 16) * r - dist y x.val)
        dsimp [e]
        linarith
      · have hmin := min_le_right (dist y x.val - (113 / 96) * r)
          ((19 / 16) * r - dist y x.val)
        dsimp [e]
        linarith
  choose e he htag using hlocal
  have hballcover : K ⊆ ⋃ z : K, Metric.ball z.val (e z) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (he ⟨x, hx⟩)⟩
  obtain ⟨E, hE⟩ := hK.elim_finite_subcover
    (fun z : K => Metric.ball z.val (e z)) (fun _ => Metric.isOpen_ball) hballcover
  exact ⟨E, e, fun z _ => ⟨he z, htag z⟩, hE⟩

private theorem exists_finite_annuli_and_spire_cover_of_ball_transfer
    {X : ℕ → Poincare.GromovHausdorff.BasedMetricSpaceBundle.{0}}
    {Y : Poincare.GromovHausdorff.BasedMetricSpaceBundle.{0}}
    (f : ∀ j, Y.carrier → (X j).carrier)
    (hpair : ∀ y z, Tendsto (fun j => dist (f j y) (f j z)) atTop (𝓝 (dist y z)))
    {R : ℝ} (hK : IsCompact (Metric.closedBall Y.base R))
    (htransfer : ∀ {ι : Type} [Finite ι] (y : ι → Y.carrier) (r : ι → ℝ),
      Metric.closedBall Y.base R ⊆ ⋃ i, Metric.ball (y i) (r i) →
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
        Metric.ball (X j).base 1 ⊆ ⋃ i, Metric.ball (f j (y i)) (r i + η))
    (F S : Finset Y.carrier) (B : Y.carrier → ℝ)
    (hB : ∀ y ∈ F, 0 < B y ∧ B y ≤ 1)
    (hcover : Metric.closedBall Y.base R \ (S : Set Y.carrier) ⊆
      ⋃ y ∈ F, Metric.ball y (B y / 4) \ {y})
    (q : ∀ j, S → (X j).carrier)
    (hq : ∀ i, Tendsto (fun j => dist (f j i.val) (q j i)) atTop (𝓝 0))
    (σ : S → ℝ) (hσ : ∀ i, 0 < σ i) :
    ∃ A : Finset (Y.carrier × ℝ),
      (∀ a ∈ A, a.1 ∈ F ∧ 0 < a.2 ∧ a.2 ≤ 1 ∧ 3 * a.2 < 2 * B a.1) ∧
      (Metric.closedBall Y.base R ⊆
        (⋃ a ∈ A, {x | (113 / 96 : ℝ) * a.2 ≤ dist a.1 x ∧
          dist a.1 x ≤ (19 / 16 : ℝ) * a.2}) ∪ ⋃ i : S, Metric.ball i.val (σ i)) ∧
      ∀ᶠ j in atTop, Metric.ball (X j).base 1 ⊆
        (⋃ a ∈ A, {x | (113 / 96 : ℝ) * a.2 ≤ dist (f j a.1) x ∧
          dist (f j a.1) x ≤ (19 / 16 : ℝ) * a.2}) ∪
          ⋃ i : S, Metric.ball (q j i) (σ i) := by
  classical
  let K := Metric.closedBall Y.base R
  obtain ⟨E, e, he, hEc⟩ := exists_finite_annular_spire_ball_refinement
    hK F S B (fun y hy => (hB y hy).1) hcover σ hσ
  let J := E
  have hej (z : J) : 0 < e z.val := (he z.val z.property).1
  have htagEx (z : J) : ∃ t : S ⊕ (Y.carrier × ℝ),
      match t with
      | .inl i => dist i.val z.val.val + 4 * e z.val < σ i
      | .inr a => a.1 ∈ F ∧ 0 < a.2 ∧ a.2 ≤ B a.1 / 3 ∧
          (113 / 96 : ℝ) * a.2 + 4 * e z.val < dist a.1 z.val.val ∧
          dist a.1 z.val.val + 4 * e z.val < (19 / 16 : ℝ) * a.2 := by
    rcases (he z.val z.property).2 with ⟨i, hi⟩ | ⟨y, hy, r, hr, hrB, hlo, hhi⟩
    · exact ⟨.inl i, hi⟩
    · exact ⟨.inr (y, r), hy, hr, hrB, hlo, hhi⟩
  choose tag htag using htagEx
  let A : Finset (Y.carrier × ℝ) := (Finset.univ.image tag).toRight
  have hAmem (z : J) (a : Y.carrier × ℝ) (hz : tag z = .inr a) : a ∈ A := by
    apply Finset.mem_toRight.mpr
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz⟩
  have hAbounds : ∀ a ∈ A,
      a.1 ∈ F ∧ 0 < a.2 ∧ a.2 ≤ 1 ∧ 3 * a.2 < 2 * B a.1 := by
    intro a ha
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp (Finset.mem_toRight.mp ha)
    have hzdata := htag z
    rw [hz] at hzdata
    have hBa := hB a.1 hzdata.1
    exact ⟨hzdata.1, hzdata.2.1, by linarith [hzdata.2.2.1],
      by linarith [hzdata.2.2.1]⟩
  have htarget : Metric.closedBall Y.base R ⊆
      (⋃ a ∈ A, {x | (113 / 96 : ℝ) * a.2 ≤ dist a.1 x ∧
        dist a.1 x ≤ (19 / 16 : ℝ) * a.2}) ∪ ⋃ i : S, Metric.ball i.val (σ i) := by
    intro x hx
    obtain ⟨z, hzE, hxz⟩ := mem_iUnion₂.mp (hEc hx)
    let zJ : J := ⟨z, hzE⟩
    have hez := hej zJ
    have hdist : dist z.val x < e z := Metric.mem_ball'.mp hxz
    have hzdata := htag zJ
    cases hz : tag zJ with
    | inl i =>
      rw [hz] at hzdata
      apply Or.inr
      refine mem_iUnion.mpr ⟨i, Metric.mem_ball'.mpr ?_⟩
      have ht := dist_triangle i.val z.val x
      change dist i.val z.val + 4 * e z < σ i at hzdata
      linarith
    | inr a =>
      rw [hz] at hzdata
      apply Or.inl
      refine mem_iUnion₂.mpr ⟨a, hAmem zJ a hz, ?_, ?_⟩
      · have ht := dist_triangle a.1 x z.val
        rw [dist_comm x z.val] at ht
        have hlo := hzdata.2.2.2.1
        change (113 / 96 : ℝ) * a.2 + 4 * e z < dist a.1 z.val at hlo
        linarith
      · have ht := dist_triangle a.1 z.val x
        have hhi := hzdata.2.2.2.2
        change dist a.1 z.val + 4 * e z < (19 / 16 : ℝ) * a.2 at hhi
        linarith
  let T : Finset ℝ := insert 1 (E.image e)
  have hT : T.Nonempty := ⟨1, by simp [T]⟩
  let η := T.min' hT
  have hη : 0 < η := by
    have hm : η ∈ T := Finset.min'_mem T hT
    rcases Finset.mem_insert.mp hm with h1 | hi
    · simpa only [h1] using (show (0 : ℝ) < 1 by norm_num)
    · obtain ⟨z, hzE, hz⟩ := Finset.mem_image.mp hi
      simpa only [hz] using (he z hzE).1
  have hηe (z : J) : η ≤ e z.val := Finset.min'_le T _ (by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩)
  have hfiniteCover : Metric.closedBall Y.base R ⊆
      ⋃ z : J, Metric.ball z.val.val (e z.val) := by
    intro x hx
    obtain ⟨z, hzE, hz⟩ := mem_iUnion₂.mp (hEc hx)
    exact mem_iUnion.mpr ⟨⟨z, hzE⟩, hz⟩
  have hsourceCover := htransfer (fun z : J => z.val.val) (fun z => e z.val)
    hfiniteCover η hη
  let cs : ∀ j, J → (X j).carrier := fun j z =>
    match tag z with | .inl i => q j i | .inr a => f j a.1
  let ct : J → Y.carrier := fun z =>
    match tag z with | .inl i => i.val | .inr a => a.1
  have hcd (z : J) :
      Tendsto (fun j => dist (cs j z) (f j z.val.val)) atTop
        (𝓝 (dist (ct z) z.val.val)) := by
    cases hz : tag z with
    | inl i =>
      simp only [cs, ct, hz]
      apply (hpair i.val z.val.val).congr_dist
      exact squeeze_zero (fun _ => dist_nonneg)
        (fun j => dist_dist_dist_le_left (f j i.val) (q j i) (f j z.val.val)) (hq i)
    | inr a =>
      simp only [cs, ct, hz]
      exact hpair a.1 z.val.val
  have hclose : ∀ᶠ j in atTop, ∀ z : J,
      |dist (cs j z) (f j z.val.val) - dist (ct z) z.val.val| < e z.val := by
    apply eventually_all.mpr
    intro z
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hcd z) (e z.val) (hej z))
  refine ⟨A, hAbounds, htarget, ?_⟩
  filter_upwards [hsourceCover, hclose] with j hj hcj
  intro x hx
  obtain ⟨z, hz⟩ := mem_iUnion.mp (hj hx)
  have hzx : dist (f j z.val.val) x < e z.val + η := Metric.mem_ball'.mp hz
  have hez := hej z
  have hηz := hηe z
  obtain ⟨hcLo, hcHi⟩ := abs_lt.mp (hcj z)
  have hUp := dist_triangle (cs j z) (f j z.val.val) x
  have hLo := dist_triangle (cs j z) x (f j z.val.val)
  rw [dist_comm x (f j z.val.val)] at hLo
  have hzdata := htag z
  cases ht : tag z with
  | inl i =>
    rw [ht] at hzdata
    apply Or.inr
    refine mem_iUnion.mpr ⟨i, Metric.mem_ball'.mpr ?_⟩
    simp only [cs, ct, ht] at hcLo hcHi hUp hLo
    linarith
  | inr a =>
    rw [ht] at hzdata
    apply Or.inl
    refine mem_iUnion₂.mpr ⟨a, hAmem z a ht, ?_, ?_⟩
    · simp only [cs, ct, ht] at hcLo hcHi hUp hLo
      linarith [hzdata.2.2.2.1]
    · simp only [cs, ct, ht] at hcLo hcHi hUp hLo
      linarith [hzdata.2.2.2.2]

end Poincare.CurvatureIntegral

open Set Filter Topology
open Poincare.GromovHausdorff Poincare.Alexandrov Poincare.CurvatureIntegral
open scoped Manifold ContDiff Bundle
namespace PoincareConjecture.RiemannianMetric

theorem exists_quarter_spire_annular_source_cover_of_pointed_limit
    {n : ℕ} {M : ℕ → Type} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j)
    {Y : BasedMetricSpaceBundle.{0}} [ProperSpace Y.carrier]
    (hconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) Y)
    (hYgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    {c0 cminus c cplus cap : ℝ}
    (hc0 : c0 < cminus) (hminus0 : 0 ≤ cminus) (hminus : cminus < c)
    (hplus : c < cplus) (hplus1 : cplus < 1) (hcap : 0 < cap) (hcap2 : cap ≤ 2)
    {R : ℝ} (hR : 1 < R) :
    ∃ (B : Y.carrier → ℝ) (F S : Finset Y.carrier) (b ρ : ℝ)
      (φ : ℕ → ℕ) (f : ∀ j, Y.carrier → M (φ j))
      (q : ∀ j, S → M (φ j)),
      (∀ x, 0 < B x ∧ 2 * B x ≤ cap) ∧
      (∀ x y : Y.carrier, 0 < dist x y → dist x y < 2 * B x →
        HasLocalDistanceAscent cminus x y) ∧
      (∀ x : Y.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
        (∀ y : Y.carrier, 0 < dist x y → dist x y < 2 * a →
          HasLocalDistanceAscent cminus x y) → a ≤ B x) ∧
      (S : Set Y.carrier) =
        {x | x ∈ Metric.closedBall Y.base R ∧ ∀ y : Y.carrier, y ≠ x → B y / 4 ≤ dist y x} ∧
      Metric.closedBall Y.base R \ (S : Set Y.carrier) ⊆ ⋃ y ∈ F, Metric.ball y (B y / 4) \ {y} ∧
      0 < b ∧ b ≤ cap ∧ 0 < ρ ∧ ρ < b / 8 ∧
      (∀ i : S, ∀ y : Y.carrier, 0 < dist i.val y → dist i.val y ≤ b →
        HasLocalDistanceAscent cplus i.val y) ∧
      StrictMono φ ∧
      (∀ y z : Y.carrier,
        Tendsto (fun j => ((g (φ j)).edist (f j y) (f j z)).toReal)
          atTop (𝓝 (dist y z))) ∧
      (∀ y : Y.carrier,
        Tendsto (fun j => ((g (φ j)).edist (p (φ j)) (f j y)).toReal)
          atTop (𝓝 (dist Y.base y))) ∧
      (∀ y : Y.carrier,
        PointedGHConvergesUnbounded
          (fun j => (g (φ j)).toBasedMetricSpace (f j y)) (Y.rebase y)) ∧
      (∀ j, ∀ i : S, letI := (g (φ j)).toMetricSpace
        dist (f j i.val) (q j i) ≤ ρ ∧
        badAscentRadius c b (q j i) ≤ badAscentRadius c b (f j i.val) ∧
        ∀ z : M (φ j), dist (f j i.val) z ≤ ρ →
          badAscentRadius c b (q j i) ≤ 2 * badAscentRadius c b z) ∧
      (∀ i : S,
        Tendsto (fun j => letI := (g (φ j)).toMetricSpace
          badAscentRadius c b (f j i.val)) atTop (𝓝 0) ∧
        Tendsto (fun j => letI := (g (φ j)).toMetricSpace
          badAscentRadius c b (q j i)) atTop (𝓝 0) ∧
        Tendsto (fun j => ((g (φ j)).edist (f j i.val) (q j i)).toReal)
          atTop (𝓝 0)) ∧
      ∀ σ : S → ℝ, (∀ i, 0 < σ i) →
        ∃ A : Finset (Y.carrier × ℝ),
          (∀ a ∈ A, a.1 ∈ F ∧ 0 < a.2 ∧ a.2 ≤ 1 ∧ 3 * a.2 < 2 * B a.1) ∧
          (Metric.closedBall Y.base R ⊆
            (⋃ a ∈ A, {x | (113 / 96 : ℝ) * a.2 ≤ dist a.1 x ∧
              dist a.1 x ≤ (19 / 16 : ℝ) * a.2}) ∪
                ⋃ i : S, Metric.ball i.val (σ i)) ∧
          ∀ᶠ j in atTop, letI := (g (φ j)).toMetricSpace
            (Metric.ball (p (φ j)) 1 ⊆
              (⋃ a ∈ A, {x | (113 / 96 : ℝ) * a.2 ≤ dist (f j a.1) x ∧
                dist (f j a.1) x ≤ (19 / 16 : ℝ) * a.2}) ∪
                  ⋃ i : S, Metric.ball (q j i) (σ i)) ∧
            ∀ a ∈ A, ∀ x : M (φ j),
              a.2 / 2 ≤ dist (f j a.1) x →
              dist (f j a.1) x ≤ 3 * a.2 →
              HasLocalDistanceAscent c0 (f j a.1) x := by
  classical
  let (j : ℕ) : MetricSpace (M j) := (g j).toMetricSpace
  let (j : ℕ) : ProperSpace ((g j).toBasedMetricSpace (p j)).carrier :=
    (g j).properSpace_toMetricSpace (hcomplete j)
  let (y : Y.carrier) : ProperSpace (Y.rebase y).carrier :=
    (inferInstance : ProperSpace Y.carrier)
  have hc : 0 ≤ c := hminus0.trans hminus.le
  have hplus0 : 0 ≤ cplus := hc.trans hplus.le
  have hc1 : c < 1 := hplus.trans hplus1
  have hminus1 : cminus < 1 := hminus.trans hc1
  have hY := curvatureGEnegOne_of_sectional_pointed_limit g p D hcomplete hsec hconv
  have hpacking : ∀ α : ℝ, 0 < α → ∃ N : ℕ,
      ComparisonAnglePackingBound Y.carrier α N := by
    intro α hα
    obtain ⟨N, hN⟩ := exists_comparisonAngle_packing_bound_of_sectional_pointed_limit n hα
    exact ⟨N, hN g p D hcomplete hsec hconv⟩
  have hK : IsCompact (Metric.closedBall Y.base R) := isCompact_closedBall _ _
  obtain ⟨B, hB, hBasc, hBmax⟩ :=
    exists_maximal_regular_radius_function hY hYgeo hpacking hminus0 hminus1 hcap
  obtain ⟨F, S, hS, hcover⟩ := exists_finite_punctured_ball_cover
    hK (fun y => B y / 4) (fun y => div_pos (hB y).1 (by norm_num))
  obtain ⟨Bplus, hBplus, hBplusAsc, _⟩ :=
    exists_maximal_regular_radius_function hY hYgeo hpacking hplus0 hplus1 hcap
  let T : Finset ℝ := insert cap (S.image Bplus)
  have hT : T.Nonempty := ⟨cap, by simp [T]⟩
  let b : ℝ := T.min' hT
  have hb : 0 < b := by
    have hbmem : b ∈ T := Finset.min'_mem T hT
    rcases Finset.mem_insert.mp hbmem with heq | him
    · simpa only [heq] using hcap
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp him
      simpa only [hi] using (hBplus i).1
  have hbcap : b ≤ cap := Finset.min'_le T cap (by simp [T])
  have hbi (i : S) : b ≤ Bplus i.val :=
    Finset.min'_le T (Bplus i.val) (by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩)
  let ρ : ℝ := b / 16
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρb : ρ < b / 8 := by dsimp [ρ]; linarith
  have hstrong (i : S) (y : Y.carrier)
      (hy : 0 < dist i.val y) (hyb : dist i.val y ≤ b) :
      HasLocalDistanceAscent cplus i.val y := by
    apply hBplusAsc i.val y hy
    have hi := hbi i
    have hipos := (hBplus i.val).1
    linarith
  have hgeo (j : ℕ) (x y : M j) :
      ∃ γ : ℝ → M j, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y := by
    obtain ⟨_, _, γ, _, h0, h1, hmin⟩ :=
      (g j).exists_minimizing_geodesic_of_metricComplete (hcomplete j) x y
    refine ⟨γ, h0, h1, ?_⟩
    intro s hs t ht
    change ((g j).edist (γ s) (γ t)).toReal = |s - t| * ((g j).edist x y).toReal
    rw [hmin s hs t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  obtain ⟨φ, hφ, f, hfpair, hfrad, hfconv, hfcover⟩ :=
    exists_subseq_rebased_pointedGHConvergesUnbounded_with_ball_covers hgeo hYgeo hconv
  have hspire (i : S) (y : Y.carrier) (hy : y ≠ i.val) :
      (1 / 4 : ℝ) * B y ≤ dist y i.val := by
    have hi : i.val ∈ (S : Set Y.carrier) := i.property
    rw [hS] at hi
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hi.2 y hy
  have href (i : S) :
      Tendsto (fun j => badAscentRadius c b (f j i.val)) atTop (𝓝 0) :=
    (tendsto_radius_and_dist_zero_of_selected_centers_at_scaled_spire
      (fun j => g (φ j)) (fun j => D (φ j)) (fun j => hcomplete (φ j))
      (fun j => hsec (φ j)) (fun j => f j i.val) (fun j => f j i.val)
      (hfconv i.val) (by norm_num : (0 : ℝ) < 1 / 4) hc hminus hplus hρ
      (by linarith : ρ < (1 / 4 : ℝ) * b / 2) hbcap (hstrong i) B hBmax (hspire i)
      (fun j => by change dist (f j i.val) (f j i.val) ≤ ρ; simpa using hρ.le)
      (fun _ => le_rfl)).1
  have hselect (i : S) := exists_near_min_badAscentRadius_centers_of_tendsto_zero
    (fun j => g (φ j)) (fun j => hcomplete (φ j))
    hc1 hb hρ (fun j => f j i.val) (href i)
  choose q hq hqzero using hselect
  have hqdist (i : S) :
      Tendsto (fun j => ((g (φ j)).edist (f j i.val) (q i j)).toReal)
        atTop (𝓝 0) :=
    (tendsto_radius_and_dist_zero_of_selected_centers_at_scaled_spire
      (fun j => g (φ j)) (fun j => D (φ j)) (fun j => hcomplete (φ j))
      (fun j => hsec (φ j)) (fun j => f j i.val) (q i)
      (hfconv i.val) (by norm_num : (0 : ℝ) < 1 / 4) hc hminus hplus hρ
      (by linarith : ρ < (1 / 4 : ℝ) * b / 2) hbcap (hstrong i) B hBmax (hspire i)
      (fun j => (hq i j).1) (fun j => (hq i j).2.1)).2
  refine ⟨B, F, S, b, ρ, φ, f, fun j i => q i j,
    hB, hBasc, hBmax, hS, hcover, hb, hbcap, hρ, hρb, hstrong,
    hφ, hfpair, hfrad, hfconv, (fun j i => hq i j),
    (fun i => ⟨href i, hqzero i, hqdist i⟩), ?_⟩
  intro σ hσ
  have htrans : ∀ {ι : Type} [Finite ι] (y : ι → Y.carrier) (r : ι → ℝ),
      Metric.closedBall Y.base R ⊆ ⋃ i, Metric.ball (y i) (r i) →
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
        Metric.ball (p (φ j)) 1 ⊆ ⋃ i, Metric.ball (f j (y i)) (r i + η) := by
    intro ι _ y r hcov η hη
    exact hfcover y r hR hcov (fun j i => f j (y i))
      (fun i => by simpa only [dist_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
      η hη
  obtain ⟨A, hA, htarget, hsource⟩ :=
    Poincare.CurvatureIntegral.exists_finite_annuli_and_spire_cover_of_ball_transfer
      (X := fun j => (g (φ j)).toBasedMetricSpace (p (φ j)))
      f hfpair hK htrans F S B
      (fun y _ => ⟨(hB y).1, by linarith [(hB y).2]⟩)
      hcover (fun j i => q i j) hqdist σ hσ
  have hasc (a : Y.carrier × ℝ) (ha : a ∈ A) :
      ∀ᶠ j in atTop, ∀ x : M (φ j),
        a.2 / 2 ≤ dist (f j a.1) x → dist (f j a.1) x ≤ 3 * a.2 →
          HasLocalDistanceAscent c0 (f j a.1) x := by
    have hr : 0 < a.2 / 2 := half_pos (hA a ha).2.1
    exact eventually_annular_distance_ascent_of_pointedGHConvergesUnbounded
      (fun j => g (φ j)) (fun j => D (φ j)) (fun j => hcomplete (φ j))
      (K := 1) (by norm_num) (fun j => hsec (φ j))
      (fun j => f j a.1) (hfconv a.1) hr hc0 (fun y hylo hyhi =>
        hBasc a.1 y (hr.trans_le hylo) (hyhi.trans_lt (hA a ha).2.2.2))
  refine ⟨A, hA, htarget, ?_⟩
  exact hsource.and ((eventually_all_finite A.finite_toSet).mpr hasc)

end PoincareConjecture.RiemannianMetric
