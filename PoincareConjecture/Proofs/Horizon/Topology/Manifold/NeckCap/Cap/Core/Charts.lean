import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.HalfSpaceChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem exists_boundary_halfspace_chart (a : M) (ha : a ∈ C.boundary_sphere) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      a ∈ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      e.IsImage C.closed_core {y | 0 ≤ y 0} := by
  obtain ⟨U, f, hU, haU, _, hdef, _, hf, d, _, hd⟩ :=
    C.boundary_local_defining_function a ha
  obtain ⟨F, hF, hFeq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hf haU
  have hdF : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) F a d ≠ 0 := by
    rw [hFeq.mfderiv_eq]
    intro h
    apply hd
    change NormedSpace.fromTangentSpace (f a) (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f a d) = 0
    erw [h]
  have hreg : Function.Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (-F) a) := by
    rw [mfderiv_neg]
    change Function.Surjective
      (fun v : TangentSpace (𝓡 3) a => -(mfderiv (𝓡 3) 𝓘(ℝ, ℝ) F a v : ℝ))
    intro y
    change ℝ at y
    let r : ℝ := mfderiv (𝓡 3) 𝓘(ℝ, ℝ) F a d
    refine ⟨(-y / r) • d, ?_⟩
    simp only [map_smul, smul_eq_mul]
    change -((-y / r) * r) = y
    have hr : r ≠ 0 := hdF
    field_simp
  obtain ⟨e, hae, he, hei, hefirst, _⟩ :=
    Poincare.Manifold.exists_normalized_regular_point_chart
      (n := 2) (by simp) hF.neg a 0 hreg
  obtain ⟨V, hVU, hV, haV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds haU) hFeq)
  refine ⟨e.restrOpen V hV, ⟨hae, haV⟩,
    he.mono (fun x hx => hx.1), hei.mono (fun y hy => hy.1), ?_⟩
  intro x hx
  change 0 ≤ e x 0 ↔ x ∈ C.closed_core
  rw [hefirst x hx.1]
  have hxV := hVU hx.2
  have hFx : F x = f x := hxV.2
  simpa only [Pi.neg_apply, sub_zero, neg_nonneg, hFx] using (hdef x hxV.1).symm

theorem exists_closed_core_halfspace_chart (a : C.closed_core) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      a.val ∈ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      e.IsImage C.closed_core {y | 0 ≤ y 0} := by
  by_cases ha : a.val ∈ C.core
  · obtain ⟨e, hae, he, hei, himg⟩ :=
      Poincare.Manifold.exists_interior_superlevel_halfspace_chart
        (E := EuclideanSpace ℝ (Fin 3)) (n := 2) (by simp)
        (f := fun _ : M => (1 : ℝ)) continuous_const 0 a.val
        (by norm_num)
    refine ⟨e.restrOpen C.core C.isOpen_core, ⟨hae, ha⟩,
      he.mono (fun x hx => hx.1), hei.mono (fun y hy => hy.1), ?_⟩
    intro x hx
    exact iff_of_true ((himg hx.1).mpr (by norm_num))
      (C.core_subset_closed_core hx.2)
  · exact C.exists_boundary_halfspace_chart a.val
      (C.boundary_eq_closed_core_diff_core.symm ▸ ⟨a.property, ha⟩)

end PoincareConjecture.CapCertificate
