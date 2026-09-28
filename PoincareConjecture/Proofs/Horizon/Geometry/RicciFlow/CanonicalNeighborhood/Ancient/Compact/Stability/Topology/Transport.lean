import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CompactCapTransport

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  (e : OpenPartialHomeomorph M N)

theorem isImage_of_subset {S : Set M} (hS : S ⊆ e.source) : e.IsImage S (e '' S) := by
  apply OpenPartialHomeomorph.IsImage.of_image_eq
  rw [inter_eq_right.mpr hS,
    inter_eq_right.mpr ((image_mono hS).trans e.image_source_subset)]

theorem image_interior {S : Set M} (hS : S ⊆ e.source) :
    e '' interior S = interior (e '' S) := by
  have h := (isImage_of_subset e hS).interior.image_eq
  rwa [inter_eq_right.mpr (interior_subset.trans hS),
    inter_eq_right.mpr (interior_subset.trans
      ((image_mono hS).trans e.image_source_subset))] at h

theorem image_closure [T2Space N] {S : Set M} (hS : IsCompact (closure S))
    (hsource : closure S ⊆ e.source) :
    e '' closure S = closure (e '' S) := by
  have hclosed := (hS.image_of_continuousOn (e.continuousOn.mono hsource)).isClosed
  have hsubset : closure (e '' S) ⊆ e '' closure S :=
    closure_minimal (image_mono subset_closure) hclosed
  have h := (isImage_of_subset e (subset_closure.trans hsource)).closure.image_eq
  rwa [inter_eq_right.mpr hsource,
    inter_eq_right.mpr (hsubset.trans
      ((image_mono hsource).trans e.image_source_subset))] at h

theorem image_frontier [T2Space N] {S : Set M} (hS : IsCompact (closure S))
    (hsource : closure S ⊆ e.source) :
    e '' frontier S = frontier (e '' S) := by
  have htarget : closure (e '' S) ⊆ e.target := by
    rw [← image_closure e hS hsource]
    exact (image_mono hsource).trans e.image_source_subset
  have h := (isImage_of_subset e (subset_closure.trans hsource)).frontier.image_eq
  rwa [inter_eq_right.mpr (frontier_subset_closure.trans hsource),
    inter_eq_right.mpr (frontier_subset_closure.trans htarget)] at h

end PoincareConjecture.CompactCapTransport

namespace PoincareConjecture.CapCertificate

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (A : CapCertificate g)
  (e : OpenPartialHomeomorph M N) (hA : A.carrier ⊆ e.source)

include hA

theorem image_carrier_open : IsOpen (e '' A.carrier) :=
  e.isOpen_image_of_subset_source A.carrier_open hA

theorem image_closed_core_compact : IsCompact (e '' A.closed_core) :=
  A.closed_core_compact.image_of_continuousOn
    (e.continuousOn.mono (A.closed_core_subset_carrier.trans hA))

theorem image_core_eq_interior :
    e '' A.core = interior (e '' A.closed_core) := by
  rw [A.core_eq_interior_closed_core]
  exact CompactCapTransport.image_interior e (A.closed_core_subset_carrier.trans hA)

theorem image_closed_core_eq_complement_end :
    e '' A.closed_core = e '' A.carrier \ e '' A.end_neck.carrier := by
  rw [A.closed_core_eq_complement_end]
  exact (e.injOn.mono hA).image_sdiff_subset A.end_neck_subset

theorem image_boundary_eq_end_frontier :
    e '' A.boundary_sphere = e '' A.carrier ∩ frontier (e '' A.end_neck.carrier) := by
  have hend := CompactCapTransport.isImage_of_subset e (A.end_neck_subset.trans hA)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := A.boundary_eq_end_frontier ▸ hx
    exact ⟨mem_image_of_mem e hx'.1,
      (hend.frontier.apply_mem_iff (hA hx'.1)).mpr hx'.2⟩
  · rintro ⟨⟨x, hx, rfl⟩, hfront⟩
    refine ⟨x, ?_, rfl⟩
    rw [A.boundary_eq_end_frontier]
    exact ⟨hx, (hend.frontier.apply_mem_iff (hA hx)).mp hfront⟩

theorem image_boundary_subset_negative_end_closure :
    e '' A.boundary_sphere ⊆
      closure (e '' A.end_neck.region (-A.epsilon⁻¹) (-A.epsilon⁻¹ / 2)) := by
  rintro _ ⟨x, hx, rfl⟩
  have hregion := CompactCapTransport.isImage_of_subset e
    (show A.end_neck.region (-A.epsilon⁻¹) (-A.epsilon⁻¹ / 2) ⊆ e.source from
      fun _ hz ↦ hA (A.end_neck_subset hz.1))
  exact (hregion.closure.apply_mem_iff (hA (A.boundary_subset hx))).mpr
    (A.boundary_subset_negative_end_closure hx)

variable [T2Space N]

theorem image_core_frontier_eq_boundary :
    frontier (e '' A.closed_core) = e '' A.boundary_sphere := by
  have : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ ‹T3Space M›)
  rw [← CompactCapTransport.image_frontier e
    (by simpa only [A.isClosed_closed_core.closure_eq] using A.closed_core_compact)
    (by simpa only [A.isClosed_closed_core.closure_eq] using
      A.closed_core_subset_carrier.trans hA), A.core_frontier_eq_boundary]

variable [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

noncomputable def imageModelEquivalence
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    CapModelEquivalence A.model_kind A.puncture (e '' A.carrier) := by
  let F := A.model_equivalence
  let : TopologicalSpace F.model := F.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) F.model := F.model_charted
  let : IsManifold (𝓡 3) ∞ F.model := F.model_manifold
  refine
    { model := F.model
      model_topology := F.model_topology
      model_charted := F.model_charted
      model_manifold := F.model_manifold
      standard_model := F.standard_model
      standard_smooth := F.standard_smooth
      forward := F.forward ∘ e.symm
      inverse := e ∘ F.inverse
      inverse_mem := fun y ↦ mem_image_of_mem e (F.inverse_mem y)
      left_inverse := ?_
      right_inverse := ?_
      forward_smooth := ?_
      inverse_smooth := ?_ }
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, e.left_inv (hA hx), F.left_inverse x hx]
  · intro y
    simp only [Function.comp_apply, e.left_inv (hA (F.inverse_mem y)), F.right_inverse]
  · apply F.forward_smooth.comp (hei.mono ((image_mono hA).trans e.image_source_subset))
    rintro _ ⟨x, hx, rfl⟩
    simpa only [mem_preimage, e.left_inv (hA hx)] using hx
  · exact he.comp F.inverse_smooth (fun y _ ↦ hA (F.inverse_mem y))

omit [T2Space N] [IsManifold (𝓡 3) ∞ N] in

theorem horizon_image_boundary_local_defining_function
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    ∀ y ∈ e '' A.boundary_sphere, ∃ V : Set N, ∃ f : N → ℝ,
      IsOpen V ∧ y ∈ V ∧ V ⊆ e '' A.carrier ∧
        (∀ z ∈ V, z ∈ e '' A.closed_core ↔ f z ≤ 0) ∧ f y = 0 ∧
        ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f V ∧
        ∃ d : TangentSpace (𝓡 3) y, d ≠ 0 ∧ mvfderiv (𝓡 3) f y d ≠ 0 := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨V, f, hV, hxV, hVA, hlevel, hfzero, hf, d, hd, hdf⟩ :=
    A.boundary_local_defining_function x hx
  have hVs : V ⊆ e.source := hVA.trans hA
  have hxs : x ∈ e.source := hVs hxV
  have hemd : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨fun _ hz ↦ (he _ hz).mdifferentiableWithinAt (by simp),
      fun _ hz ↦ (hei _ hz).mdifferentiableWithinAt (by simp)⟩
  refine ⟨e '' V, f ∘ e.symm, e.isOpen_image_of_subset_source hV hVs,
    mem_image_of_mem e hxV, image_mono hVA, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [(CompactCapTransport.isImage_of_subset e
      (A.closed_core_subset_carrier.trans hA)).apply_mem_iff (hVs hz)]
    simpa only [Function.comp_apply, e.left_inv (hVs hz)] using hlevel z hz
  · simpa only [Function.comp_apply, e.left_inv hxs] using hfzero
  · apply hf.comp (hei.mono ((image_mono hVs).trans e.image_source_subset))
    rintro _ ⟨z, hz, rfl⟩
    simpa only [mem_preimage, e.left_inv (hVs hz)] using hz
  · refine ⟨mfderiv (𝓡 3) (𝓡 3) e x d, ?_, ?_⟩
    · intro hzero
      apply hd
      have hback := congrArg (fun L ↦ L d) (hemd.symm_comp_deriv hxs)
      change mfderiv (𝓡 3) (𝓡 3) e.symm (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x d) = d at hback
      simpa only [hzero, map_zero, e.left_inv hxs] using hback.symm
    · have hfx : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (e.symm (e x)) := by
        rw [e.left_inv hxs]
        exact ((hf x hxV).contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
      have hback := congrArg (fun L ↦ L d) (hemd.symm_comp_deriv hxs)
      change mfderiv (𝓡 3) (𝓡 3) e.symm (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x d) = d at hback
      rw [mvfderiv_comp_apply (e x) hfx
        (hemd.mdifferentiableAt_symm (e.map_source hxs)), hback, e.left_inv hxs]
      exact hdf

end PoincareConjecture.CapCertificate
