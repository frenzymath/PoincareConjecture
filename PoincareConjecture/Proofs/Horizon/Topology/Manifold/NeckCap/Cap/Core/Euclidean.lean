import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.EmbeddingSupplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.Charts
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.CoreConnected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ModelCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.FromEmbedding












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)
  (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
  (hs : e.source = C.carrier) (ht : e.target = univ)

include hs ht

omit [T2Space M] in
private theorem isImage_of_subset_carrier (S : Set M) (hS : S ⊆ C.carrier) :
    e.IsImage S (e '' S) := by
  apply OpenPartialHomeomorph.IsImage.of_image_eq
  rw [hs, inter_eq_right.mpr hS, ht, univ_inter]


theorem closure_image_core : closure (e '' C.core) = e '' C.closed_core := by
  have h := (C.isImage_of_subset_carrier e hs ht C.core C.core_subset_carrier).closure.image_eq
  rw [C.closure_core_eq_closed_core, hs,
    inter_eq_right.mpr C.closed_core_subset_carrier, ht, univ_inter] at h
  exact h.symm

omit [T2Space M] in

theorem interior_image_closed_core : interior (e '' C.closed_core) = e '' C.core := by
  have h := (C.isImage_of_subset_carrier e hs ht
    C.closed_core C.closed_core_subset_carrier).interior.image_eq
  rw [← C.core_eq_interior_closed_core, hs,
    inter_eq_right.mpr C.core_subset_carrier, ht, univ_inter] at h
  exact h.symm


theorem frontier_image_core : frontier (e '' C.core) = e '' C.boundary_sphere := by
  have h := (C.isImage_of_subset_carrier e hs ht C.core C.core_subset_carrier).frontier.image_eq
  rw [C.frontier_core_eq_boundary, hs,
    inter_eq_right.mpr C.boundary_subset, ht, univ_inter] at h
  exact h.symm



theorem nonempty_smoothDomain_image_core
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    Nonempty (Poincare.Manifold.SmoothDomain 3 (e '' C.core)) := by
  have hsub : C.closed_core ⊆ e.source := hs.symm ▸ C.closed_core_subset_carrier
  have himg := C.isImage_of_subset_carrier e hs ht C.closed_core C.closed_core_subset_carrier
  have hcharts : ∀ a : e '' C.closed_core,
      ∃ f : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace ℝ (Fin 3)),
        a.val ∈ f.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target ∧
        f.IsImage (e '' C.closed_core) {y | 0 ≤ y 0} := by
    intro a
    have hat : a.val ∈ e.target := ht.symm ▸ mem_univ _
    have ha : e.symm a.val ∈ C.closed_core := (himg.symm_apply_mem_iff hat).mpr a.property
    obtain ⟨f, haf, hf, hfi, hfimg⟩ := C.exists_closed_core_halfspace_chart ⟨e.symm a.val, ha⟩
    refine ⟨e.symm.trans f, ⟨hat, haf⟩, ?_, ?_, ?_⟩
    · exact hf.comp (hei.mono (fun x hx => hx.1)) (fun x hx => hx.2)
    · exact he.comp (hfi.mono (fun y hy => hy.1)) (fun y hy => hy.2)
    · intro x hx
      exact (hfimg hx.2).trans (himg.symm hx.1)
  choose amb hamb using hcharts
  obtain ⟨CS, rel, hsource, _, hman, hemb⟩ :=
    Poincare.Manifold.exists_smooth_embedding_of_halfspace_charts
      (n := 2) (by simp) (e '' C.closed_core) amb hamb
  let := CS
  let := hman
  have hcompact : IsCompact (e '' C.closed_core) :=
    C.closed_core_compact.image_of_continuousOn (e.continuousOn.mono hsub)
  have hconn : IsConnected (e '' C.closed_core) :=
    C.isConnected_closed_core.image _ (e.continuousOn.mono hsub)
  simpa only [C.interior_image_closed_core e hs ht] using
    Poincare.Manifold.nonempty_smoothDomain_interior (n := 2) hcompact hconn hemb

omit hs ht



theorem exists_euclidean_core_coordinates (hkind : C.model_kind = .euclidean) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      e.source = C.carrier ∧ e.target = univ ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      Nonempty (Poincare.Manifold.SmoothDomain 3 (e '' C.core)) ∧
      closure (e '' C.core) = e '' C.closed_core ∧
      frontier (e '' C.core) = e '' C.boundary_sphere := by
  obtain ⟨e, hs, ht, he, hei⟩ := C.exists_euclidean_coordinates hkind
  exact ⟨e, hs, ht, he, hei, C.nonempty_smoothDomain_image_core e hs ht he hei,
    C.closure_image_core e hs ht, C.frontier_image_core e hs ht⟩

end PoincareConjecture.CapCertificate
