import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.LevelSets
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem exists_chart_squaredRadius_function (x : M) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hR : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    ∃ g : M → ℝ, ContMDiff (𝓡 2) (𝓘(ℝ, ℝ)) ∞ g ∧
      (∀ y ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r,
        g y = ‖(chartAt (EuclideanSpace ℝ (Fin 2)) x) y -
          (chartAt (EuclideanSpace ℝ (Fin 2)) x) x‖ ^ 2) ∧
      (∀ y ∉ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r,
        r ^ 2 ≤ g y) := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let f : SmoothBumpFunction (𝓡 2) x :=
    { rIn := r
      rOut := R
      rIn_pos := hr
      rIn_lt_rOut := hrR
      closedBall_subset := by simpa using hR }
  let q : M → ℝ := fun y => ‖e y - e x‖ ^ 2
  have hq : ContMDiffOn (𝓡 2) (𝓘(ℝ, ℝ)) ∞ q e.source := by
    exact ((contDiff_norm_sq ℝ).contMDiff.comp_contMDiffOn
      ((contMDiffOn_chart (I := 𝓡 2)).sub contMDiffOn_const))
  let g : M → ℝ := fun y => R ^ 2 + f y * (q y - R ^ 2)
  refine ⟨g, ?_, ?_, ?_⟩
  · exact contMDiff_const.add (f.contMDiff_smul (hq.sub contMDiffOn_const))
  · rintro y ⟨z, hz, rfl⟩
    have hzR : z ∈ e.target := hR (closedBall_subset_closedBall hrR.le hz)
    have hf : f (e.symm z) = 1 := by
      apply f.one_of_dist_le (e.map_target hzR)
      simpa [e, extChartAt, OpenPartialHomeomorph.extend, e.right_inv hzR] using hz
    change R ^ 2 + f (e.symm z) * (q (e.symm z) - R ^ 2) = q (e.symm z)
    rw [hf]
    ring
  · intro y hy
    have hRr : r ^ 2 ≤ R ^ 2 := sq_le_sq₀ hr.le (hr.trans hrR).le |>.mpr hrR.le
    by_cases hf : f y = 0
    · simpa [g, hf] using hRr
    · have hys : y ∈ e.source := f.support_subset_source hf
      have hnorm : r ≤ ‖e y - e x‖ := by
        by_contra hn
        apply hy
        refine ⟨e y, ?_, e.left_inv hys⟩
        exact mem_ball.mpr (by simpa only [dist_eq_norm] using lt_of_not_ge hn)
      have hqr : r ^ 2 ≤ q y :=
        (sq_le_sq₀ hr.le (norm_nonneg _)).mpr hnorm
      have hnonneg := f.nonneg (x := y)
      have hle := f.le_one (x := y)
      dsimp [g]
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hqr),
        mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hRr)]

theorem exists_chart_circle_level_function (x : M) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hR : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    ∃ g : M → ℝ, ContMDiff (𝓡 2) (𝓘(ℝ, ℝ)) ∞ g ∧
      ∀ ρ ∈ Ioo (0 : ℝ) r, g ⁻¹' {ρ ^ 2} =
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) ρ := by
  obtain ⟨g, hg, heq, hge⟩ := exists_chart_squaredRadius_function x hr hrR hR
  refine ⟨g, hg, ?_⟩
  intro ρ hρ
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hρr : ρ ^ 2 < r ^ 2 := (sq_lt_sq₀ hρ.1.le hr.le).mpr hρ.2
  ext y
  constructor
  · intro hy
    have hgy : g y = ρ ^ 2 := hy
    have hyball : y ∈ e.symm '' ball (e x) r := by
      by_contra hyball
      have h := hge y hyball
      rw [hgy] at h
      exact (not_le_of_gt hρr) h
    obtain ⟨z, hz, rfl⟩ := hyball
    have hztarget : z ∈ e.target := hR
      (closedBall_subset_closedBall hrR.le (ball_subset_closedBall hz))
    refine ⟨z, ?_, rfl⟩
    have hval := heq (e.symm z) ⟨z, ball_subset_closedBall hz, rfl⟩
    change g (e.symm z) = ‖e (e.symm z) - e x‖ ^ 2 at hval
    rw [e.right_inv hztarget] at hval
    rw [mem_sphere, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hρ.1.le).mp (hval.symm.trans hgy)
  · rintro ⟨z, hz, rfl⟩
    have hzr : z ∈ closedBall (e x) r :=
      closedBall_subset_closedBall hρ.2.le (sphere_subset_closedBall hz)
    have hztarget : z ∈ e.target := hR (closedBall_subset_closedBall hrR.le hzr)
    have hval := heq (e.symm z) ⟨z, hzr, rfl⟩
    change g (e.symm z) = ‖e (e.symm z) - e x‖ ^ 2 at hval
    change g (e.symm z) = ρ ^ 2
    rw [hval, e.right_inv hztarget, ← dist_eq_norm, mem_sphere.mp hz]

theorem exists_chart_circle_finite_edge_intersections {I : Type*} [Finite I]
    (x : M) (edge : I → SmoothEdge M) {a b r R : ℝ}
    (ha : 0 < a) (hab : a < b) (hbr : b < r) (hrR : r < R)
    (hR : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    ∃ ρ ∈ Ioo a b, ∀ i,
      ((edge i).map '' Icc (0 : ℝ) 1 ∩
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) ρ).Finite ∧
      (edge i).map 0 ∉ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) ρ ∧
      (edge i).map 1 ∉ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) ρ := by
  obtain ⟨g, hg, hlevels⟩ := exists_chart_circle_level_function x
    (ha.trans (hab.trans hbr)) hrR hR
  obtain ⟨c, hc, _, hreg⟩ := exists_finite_smoothEdge_level_intersections edge g hg ∅
    ((sq_lt_sq₀ ha.le (ha.trans hab).le).mpr hab)
  have hcpos : 0 ≤ c := (sq_nonneg a).trans hc.1.le
  have hsq : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hcpos
  have hρa : a < Real.sqrt c :=
    (sq_lt_sq₀ ha.le (Real.sqrt_nonneg _)).mp (hsq.symm ▸ hc.1)
  have hρb : Real.sqrt c < b :=
    (sq_lt_sq₀ (Real.sqrt_nonneg _) (ha.trans hab).le).mp (hsq.symm ▸ hc.2)
  have hlevel := hlevels (Real.sqrt c) ⟨ha.trans hρa, hρb.trans hbr⟩
  rw [hsq] at hlevel
  refine ⟨Real.sqrt c, ⟨hρa, hρb⟩, fun i => ?_⟩
  rw [← hlevel]
  exact ⟨(hreg i).2.2.1, (hreg i).1, (hreg i).2.1⟩

end PoincareConjecture.Topology.Surface
