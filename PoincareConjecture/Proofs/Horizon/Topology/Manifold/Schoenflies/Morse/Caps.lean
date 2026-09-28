import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sublevel.Minimum













noncomputable section
set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)


theorem morse_signs_eq_one_of_isLocalMin
    {M : Type*} [TopologicalSpace M] {h : M -> Real}
    (e : OpenPartialHomeomorph E2 M) (he0 : 0 ∈ e.source)
    (σ : Fin 2 -> Real) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hform : ∀ x ∈ e.source, h (e x) = h (e 0) + ∑ i : Fin 2, σ i * x i ^ 2)
    (hmin : IsLocalMin h (e 0)) : ∀ i, σ i = 1 := by
  have hloc : IsLocalMin (h ∘ e) 0 := hmin.comp_continuous
    (e.continuousOn.continuousAt (e.open_source.mem_nhds he0))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (e.open_source.mem_nhds he0) hloc)
  intro i
  rcases hσ i with hi | hi
  · have hx : EuclideanSpace.single i (r / 2) ∈ ball (0 : E2) r := by
      simp only [mem_ball_zero_iff, PiLp.norm_single, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      linarith
    obtain ⟨hxs, hxle⟩ := hball hx
    have hh := hform (EuclideanSpace.single i (r / 2)) hxs
    simp only [PiLp.single_apply, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hi] at hh
    change h (e 0) ≤ h (e (EuclideanSpace.single i (r / 2))) at hxle
    nlinarith [sq_pos_of_pos (half_pos hr)]
  · exact hi



theorem exists_minimum_cap_radius
    {M : Type*} [TopologicalSpace M] {h : M -> Real}
    (e : OpenPartialHomeomorph E2 M) (he0 : 0 ∈ e.source)
    (σ : Fin 2 -> Real) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hform : ∀ x ∈ e.source, h (e x) = h (e 0) + ∑ i : Fin 2, σ i * x i ^ 2)
    (hmin : IsLocalMin h (e 0)) :
    ∃ R : Real, 0 < R ∧ closedBall (0 : E2) R ⊆ e.source ∧
      ∀ r ∈ Ioc (0 : Real) R,
        e '' closedBall 0 r = e.target ∩ {p | h p ≤ h (e 0) + r ^ 2} ∧
        e '' ball 0 r = e.target ∩ {p | h p < h (e 0) + r ^ 2} ∧
        e '' sphere 0 r = e.target ∩ {p | h p = h (e 0) + r ^ 2} := by
  have hsign := morse_signs_eq_one_of_isLocalMin e he0 σ hσ hform hmin
  have hnorm (x : E2) (hx : x ∈ e.source) : h (e x) = h (e 0) + ‖x‖ ^ 2 := by
    simpa only [hsign, one_mul, ← EuclideanSpace.real_norm_sq_eq] using hform x hx
  obtain ⟨R, hR, hRs⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  refine ⟨R / 2, half_pos hR, ?_, ?_⟩
  · exact (closedBall_subset_ball (by linarith)).trans hRs
  · intro r hr
    have hrs : closedBall (0 : E2) r ⊆ e.source :=
      (closedBall_subset_ball (by linarith [hr.2])).trans hRs
    have hle (x : E2) : ‖x‖ ^ 2 ≤ r ^ 2 ↔ ‖x‖ ≤ r :=
      sq_le_sq₀ (norm_nonneg _) hr.1.le
    have hlt (x : E2) : ‖x‖ ^ 2 < r ^ 2 ↔ ‖x‖ < r :=
      sq_lt_sq₀ (norm_nonneg _) hr.1.le
    have heq (x : E2) : ‖x‖ ^ 2 = r ^ 2 ↔ ‖x‖ = r :=
      sq_eq_sq₀ (norm_nonneg _) hr.1.le
    refine ⟨?_, ?_, ?_⟩
    · ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨e.map_source (hrs hx), ?_⟩
        simp only [mem_ofPred_eq, hnorm x (hrs hx), add_le_add_iff_left, hle]
        simpa only [mem_closedBall, dist_zero_right] using hx
      · rintro ⟨hp, hh⟩
        refine ⟨e.symm p, ?_, e.right_inv hp⟩
        have hx := e.map_target hp
        change h p ≤ h (e 0) + r ^ 2 at hh
        rw [← e.right_inv hp, hnorm _ hx] at hh
        simpa only [mem_closedBall, dist_zero_right,
          add_le_add_iff_left, hle] using hh
    · ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxs := hrs (ball_subset_closedBall hx)
        refine ⟨e.map_source hxs, ?_⟩
        simp only [mem_ofPred_eq, hnorm x hxs, add_lt_add_iff_left, hlt]
        exact mem_ball_zero_iff.mp hx
      · rintro ⟨hp, hh⟩
        refine ⟨e.symm p, ?_, e.right_inv hp⟩
        have hx := e.map_target hp
        change h p < h (e 0) + r ^ 2 at hh
        rw [← e.right_inv hp, hnorm _ hx] at hh
        simpa only [mem_ball_zero_iff, add_lt_add_iff_left, hlt] using hh
    · ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxs := hrs (sphere_subset_closedBall hx)
        refine ⟨e.map_source hxs, ?_⟩
        simp only [mem_ofPred_eq, hnorm x hxs, add_right_inj, heq]
        simpa only [mem_sphere, dist_zero_right] using hx
      · rintro ⟨hp, hh⟩
        refine ⟨e.symm p, ?_, e.right_inv hp⟩
        have hx := e.map_target hp
        change h p = h (e 0) + r ^ 2 at hh
        rw [← e.right_inv hp, hnorm _ hx] at hh
        simpa only [mem_sphere, dist_zero_right, add_right_inj, heq] using hh


theorem exists_maximum_cap_radius
    {M : Type*} [TopologicalSpace M] {h : M -> Real}
    (e : OpenPartialHomeomorph E2 M) (he0 : 0 ∈ e.source)
    (σ : Fin 2 -> Real) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hform : ∀ x ∈ e.source, h (e x) = h (e 0) + ∑ i : Fin 2, σ i * x i ^ 2)
    (hmax : IsLocalMax h (e 0)) :
    ∃ R : Real, 0 < R ∧ closedBall (0 : E2) R ⊆ e.source ∧
      ∀ r ∈ Ioc (0 : Real) R,
        e '' closedBall 0 r = e.target ∩ {p | h (e 0) - r ^ 2 ≤ h p} ∧
        e '' ball 0 r = e.target ∩ {p | h (e 0) - r ^ 2 < h p} ∧
        e '' sphere 0 r = e.target ∩ {p | h p = h (e 0) - r ^ 2} := by
  have hsign (i : Fin 2) : -σ i = -1 ∨ -σ i = 1 := by
    rcases hσ i with hi | hi <;> simp [hi]
  have hneg (x : E2) (hx : x ∈ e.source) :
      -h (e x) = -h (e 0) + ∑ i : Fin 2, -σ i * x i ^ 2 := by
    rw [hform x hx]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add_rev]
    ring
  obtain ⟨R, hR, hRs, hcap⟩ :=
    exists_minimum_cap_radius e he0 (fun i => -σ i) hsign hneg hmax.neg
  refine ⟨R, hR, hRs, fun r hr => ?_⟩
  obtain ⟨hc, ho, hs⟩ := hcap r hr
  refine ⟨hc.trans ?_, ho.trans ?_, hs.trans ?_⟩ <;> congr 1 <;> ext p <;>
    simp only [mem_ofPred_eq] <;> constructor <;> intro hp <;> linarith



theorem exists_minimum_cap_of_morse_coordinates
    {M : Type*} [TopologicalSpace M] [ChartedSpace E2 M]
    [IsManifold (𝓡 2) ∞ M] {h : M -> Real}
    (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hcoords : ∀ p, mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 ->
      ∃ (e : OpenPartialHomeomorph E2 M) (σ : Fin 2 -> Real),
        (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        ∀ x ∈ e.source, h (e x) = h p + ∑ i : Fin 2, σ i * x i ^ 2)
    {p : M} (hp : IsLocalMin h p) :
    ∃ (e : OpenPartialHomeomorph E2 M) (R : Real),
      0 < R ∧ closedBall 0 R ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∀ r ∈ Ioc (0 : Real) R,
        e '' closedBall 0 r = e.target ∩ {q | h q ≤ h p + r ^ 2} ∧
        e '' ball 0 r = e.target ∩ {q | h q < h p + r ^ 2} ∧
        e '' sphere 0 r = e.target ∩ {q | h q = h p + r ^ 2} := by
  obtain ⟨e, σ, hσ, he0, hep, he, hei, hform⟩ := hcoords p
    (Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh hp)
  obtain ⟨R, hR, hRs, hcap⟩ := exists_minimum_cap_radius e he0 σ hσ
    (by simpa only [hep] using hform) (by simpa only [hep] using hp)
  exact ⟨e, R, hR, hRs, hep, he, hei, by simpa only [hep] using hcap⟩

end Poincare.Manifold.Schoenflies
