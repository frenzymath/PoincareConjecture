import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.MixedSlice
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.SliceAlignment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.AlignedCores
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.LowerCore

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_mixed_overlap_containment_or_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
          (D.boundary_sphere ∩ C.carrier).Nonempty →
          (¬ D.boundary_sphere ⊆ C.carrier) →
          C.carrier ⊆ D.carrier ∨
            (C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
              IsCompact (C.carrier ∪ D.carrier)) := by
  obtain ⟨ε₁, hε₁, hsmall, hslice⟩ := exists_mixed_boundary_shifted_slice_threshold.{u}
  obtain ⟨ε₂, hε₂, _, halign⟩ := exists_slice_alignment_threshold.{u}
  obtain ⟨ε₃, hε₃, _, hcontact⟩ := exists_mixed_boundary_positive_end_contact.{u}
  obtain ⟨ε₄, hε₄, _, hquarter⟩ :=
    EpsilonNeck.exists_closure_positive_quarter_subset_of_central_sphere_contact.{u}
  refine ⟨min ε₁ (min ε₂ (min ε₃ ε₄)),
    lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)),
    ((min_le_left _ _).trans hsmall).trans (by norm_num), ?_⟩
  intro M _ _ _ _ _ _ _ g C D hC hDC hmeet hmiss
  have hC₁ := hC.trans (min_le_left _ _)
  have hC₂ := hC.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hC₃ := hC.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hC₄ := hC.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨a, _, ha, hhigh⟩ := hslice C D hC₁ hDC hmeet hmiss
  obtain ⟨e, f, heC, hfD, heB, hfB, hretain⟩ := halign C D hC₂ hDC ha
    (fun q => (hhigh (mem_range_self q)).1)
  rcases C.closed_core_eq_or_compact_component_of_aligned_boundaries D e f
      heC hfD (heB.trans hfB.symm) with hequal | hclosed
  · left
    have hlower := C.lower_carrier_subset_transported_core e hretain (heB ▸ hhigh)
    obtain ⟨x, _, _, hxquarter, hxD⟩ := hcontact C D hC₃ hmeet hmiss
    have hupper := hquarter C.end_neck D.boundary_neck
      (C.end_neck_epsilon.trans_le hC₄)
      (D.boundary_neck_epsilon.trans (hDC.trans C.end_neck_epsilon.symm))
      ⟨x, by simpa only [C.end_neck_epsilon] using hxquarter, hxD⟩
    intro y hy
    by_cases hyupper : y ∈ C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹
    · apply D.boundary_neck_subset
      apply hupper
      simpa only [C.end_neck_epsilon] using subset_closure hyupper
    · have hycore := image_mono C.core_subset_closed_core (hlower ⟨hy, hyupper⟩)
      rw [hequal] at hycore
      rw [← hfD]
      exact image_mono D.closed_core_subset_carrier hycore
  · exact Or.inr hclosed

end PoincareConjecture.CapCertificate
