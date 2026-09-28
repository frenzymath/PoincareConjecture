import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OneDimensional.Period
import PoincareConjecture.Proofs.M62.Mathlib.FlatCircleCharts
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.OneDimensional

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]



theorem nonempty_diffeomorph_of_periodic_line
    {T : ℝ} [ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle T)]
    [IsManifold (𝓡 1) ∞ (AddCircle T)]
    (hq : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞
      (fun t : ℝ => (t : AddCircle T)))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ)
    (hderiv : ∀ t, Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t))
    (hsurj : Function.Surjective γ) (hper : Function.Periodic γ T)
    (hfib : ∀ a b : ℝ, γ a = γ b ↔ a - b ∈ AddSubgroup.zmultiples T) :
    Nonempty (Diffeomorph (𝓡 1) (𝓡 1) (AddCircle T) M ∞) := by
  let F : AddCircle T → M := hper.lift
  have hFq (t : ℝ) : F (t : AddCircle T) = γ t := hper.lift_coe t
  have hFsmooth : ContMDiff (𝓡 1) (𝓡 1) ∞ F := by
    intro y
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hlinv := (hq t).localInverse_left_inv (hq t).localInverse_mem_target
    have hcomp : ContMDiffAt (𝓡 1) (𝓡 1) ∞
        (fun y => γ ((hq t).localInverse y)) (t : AddCircle T) := by
      apply ContMDiffAt.comp _ _ (hq t).localInverse_contMDiffAt
      rw [hlinv]
      exact hγ t
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [(hq t).localInverse_eventuallyEq_right] with y hy
    change (((hq t).localInverse y : ℝ) : AddCircle T) = y at hy
    rw [← hFq, hy]
  have hFbij : Function.Bijective F := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
      exact QuotientAddGroup.eq_iff_sub_mem.mpr ((hfib a b).mp hxy)
    · intro y
      obtain ⟨t, ht⟩ := hsurj y
      exact ⟨(t : AddCircle T), (hFq t).trans ht⟩
  have hFderiv : ∀ y, Function.Bijective (mfderiv (𝓡 1) (𝓡 1) F y) := by
    intro y
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hchain := mfderiv_comp t
      ((hFsmooth (t : AddCircle T)).mdifferentiableAt (by simp))
      ((hq t).mdifferentiableAt (by simp))
    have hcompose : F ∘ (fun t : ℝ => (t : AddCircle T)) = γ := funext hFq
    rw [hcompose] at hchain
    have hqbij : Function.Bijective
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => (t : AddCircle T)) t) :=
      ((hq t).mfderivToContinuousLinearEquiv (by simp)).bijective
    apply (Function.Bijective.of_comp_iff _ hqbij).mp
    change Function.Bijective
      ((mfderiv (𝓡 1) (𝓡 1) F (t : AddCircle T)).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => (t : AddCircle T)) t))
    rw [← hchain]
    exact hderiv t
  exact ⟨(Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv
    hFsmooth hFderiv).diffeomorphOfBijective hFbij⟩





theorem exists_addCircle_diffeomorph_of_compact_connected
    [T3Space M] [CompactSpace M] [ConnectedSpace M]
    (g : PoincareConjecture.RiemannianMetric 1 M) :
    ∃ T : ℝ, 0 < T ∧
      ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle T), letI := C
        IsManifold (𝓡 1) ∞ (AddCircle T) ∧
        IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞
          (fun t : ℝ => (t : AddCircle T)) ∧
        Nonempty (Diffeomorph (𝓡 1) (𝓡 1) (AddCircle T) M ∞) := by
  classical
  have hc : PoincareConjecture.MetricComplete g := by
    unfold PoincareConjecture.MetricComplete
    infer_instance
  let p : M := Classical.arbitrary M
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 1))
  obtain ⟨γ, hγ, hγ0, hγd⟩ := g.exists_global_line_geodesic hc p v
  obtain ⟨T, hT, hper, hfib, _⟩ :=
    g.exists_fundamental_period_line_geodesic hc hγ hγ0 hv hγd
  let A : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    ((EuclideanSpace.equiv (Fin 1) ℝ).trans
      (LinearEquiv.funUnique (Fin 1) ℝ ℝ).toContinuousLinearEquiv).symm
  obtain ⟨C, hM, hq, _⟩ := AddCircle.exists_flatChartedSpace A hT
  let := C
  let := hM
  refine ⟨T, hT, C, hM, hq, ?_⟩
  exact nonempty_diffeomorph_of_periodic_line hq
    (PoincareConjecture.RiemannianMetric.contMDiff_global_line_geodesic hγ)
    (g.line_geodesic_mfderiv_bijective hγ hγ0 hv hγd)
    (g.surjective_global_line_geodesic hc hγ hγ0 hv hγd) hper hfib

end Poincare.Geometry.Manifold.OneDimensional
