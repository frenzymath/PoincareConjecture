


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartLevel












set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]





theorem exists_chart_circle_transverse_edge_intersections {I : Type*} [Finite I]
    (x : M) (edge : I → SmoothEdge M) (S : Finset M) {a b r R : ℝ}
    (ha : 0 < a) (hab : a < b) (hbr : b < r) (hrR : r < R)
    (hR : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    ∃ ρ ∈ Ioo a b,
      (∀ y ∈ S, y ∉ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) ρ) ∧
      ∀ i,
        ((edge i).map '' Icc (0 : ℝ) 1 ∩
          (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
            sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) ρ).Finite ∧
        (edge i).map 0 ∉ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) ρ ∧
        (edge i).map 1 ∉ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) ρ ∧
        ∀ t ∈ Ioo (0 : ℝ) 1,
          (edge i).map t ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
            sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) ρ →
          deriv (fun u => ‖chartAt (EuclideanSpace ℝ (Fin 2)) x ((edge i).map u) -
            chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2) t ≠ 0 := by
  classical
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hr : 0 < r := ha.trans (hab.trans hbr)
  have hrsub : closedBall (e x) r ⊆ e.target :=
    (closedBall_subset_closedBall hrR.le).trans hR
  obtain ⟨g, hg, heq, hge⟩ := exists_chart_squaredRadius_function x hr hrR hR
  obtain ⟨c, hc, havoid, hreg⟩ := exists_finite_smoothEdge_level_intersections edge g hg
    (S.image g) ((sq_lt_sq₀ ha.le (ha.trans hab).le).mpr hab)
  have hcpos : 0 ≤ c := (sq_nonneg a).trans hc.1.le
  have hsq : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hcpos
  have hρa : a < Real.sqrt c :=
    (sq_lt_sq₀ ha.le (Real.sqrt_nonneg _)).mp (hsq.symm ▸ hc.1)
  have hρb : Real.sqrt c < b :=
    (sq_lt_sq₀ (Real.sqrt_nonneg _) (ha.trans hab).le).mp (hsq.symm ▸ hc.2)
  have hρr : Real.sqrt c < r := hρb.trans hbr
  have hcr : c < r ^ 2 := by
    rw [← hsq]
    exact (sq_lt_sq₀ (Real.sqrt_nonneg _) hr.le).mpr hρr
  have hlevel_ball : g ⁻¹' {c} ⊆ e.symm '' ball (e x) r := by
    intro y hy
    by_contra hyball
    have h := hge y hyball
    change g y = c at hy
    rw [hy] at h
    exact (not_le_of_gt hcr) h
  have hlevel : g ⁻¹' {c} = e.symm '' sphere (e x) (Real.sqrt c) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := hlevel_ball hy
      have hztarget := hrsub (ball_subset_closedBall hz)
      refine ⟨z, ?_, rfl⟩
      have hval := heq (e.symm z) ⟨z, ball_subset_closedBall hz, rfl⟩
      change g (e.symm z) = ‖e (e.symm z) - e x‖ ^ 2 at hval
      rw [e.right_inv hztarget] at hval
      rw [mem_sphere, dist_eq_norm]
      have hgy : g (e.symm z) = c := hy
      exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
        (hval.symm.trans (hgy.trans hsq.symm))
    · rintro ⟨z, hz, rfl⟩
      have hzr : z ∈ closedBall (e x) r :=
        closedBall_subset_closedBall hρr.le (sphere_subset_closedBall hz)
      have hval := heq (e.symm z) ⟨z, hzr, rfl⟩
      change g (e.symm z) = ‖e (e.symm z) - e x‖ ^ 2 at hval
      change g (e.symm z) = c
      rw [hval, e.right_inv (hrsub hzr), ← dist_eq_norm, mem_sphere.mp hz, hsq]
  refine ⟨Real.sqrt c, ⟨hρa, hρb⟩, ?_, fun i => ?_⟩
  · intro y hy hycircle
    have hgy : g y = c := by
      change y ∈ g ⁻¹' {c}
      rw [hlevel]
      exact hycircle
    exact havoid (Finset.mem_image.mpr ⟨y, hy, hgy⟩)
  · change ((_ '' Icc (0 : ℝ) 1) ∩ e.symm '' sphere (e x) (Real.sqrt c)).Finite ∧ _
    rw [← hlevel]
    refine ⟨(hreg i).2.2.1, (hreg i).1, (hreg i).2.1, ?_⟩
    intro t ht hgt
    have hball := hlevel_ball hgt
    have hcont : ContinuousAt (edge i).map t :=
      ((edge i).smooth.continuousOn t ⟨ht.1.le, ht.2.le⟩).continuousAt
        (Icc_mem_nhds ht.1 ht.2)
    have heventually : (fun u => g ((edge i).map u)) =ᶠ[𝓝 t]
        (fun u => ‖e ((edge i).map u) - e x‖ ^ 2) := by
      filter_upwards [hcont ((isOpen_chart_ball x hrsub).mem_nhds hball)] with u hu
      exact heq _ (image_mono ball_subset_closedBall hu)
    rw [← heventually.deriv_eq]
    exact (hreg i).2.2.2 t ht hgt

end PoincareConjecture.Topology.Surface
