import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Fubini
import Mathlib.Topology.Compactness.Lindelof








set_option autoImplicit false

open Set MeasureTheory Poincare.Coarea Poincare.EuclideanSpace
open scoped ENNReal

namespace PoincareConjecture.RiemannianMetric


theorem lintegral_euclideanCons_image_tail {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} {t : Set ℝ}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hρ : AEMeasurable ρ (volume.restrict s)) :
    (∫⁻ x in euclideanConsEquiv n '' (t ×ˢ s), ρ (euclideanTail x)) =
      (∫⁻ y in s, ρ y) * volume t := by
  rw [← (volumePreserving_euclideanConsEquiv n).setLIntegral_comp_emb
    (euclideanConsEquiv n).measurableEmbedding]
  simp only [euclideanConsEquiv_apply, euclideanTail_cons]
  change (∫⁻ z in t ×ˢ s, ρ z.2 ∂volume.prod volume) = _
  rw [← Measure.prod_restrict, lintegral_prod _ hρ.comp_snd]
  simp only [lintegral_const, Measure.restrict_apply_univ]



theorem measure_eq_prod_of_local_rectangles
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (μ : Measure (X × Y)) (ν : Measure X) (ξ : Measure Y)
    [SigmaFinite ν] [SigmaFinite ξ]
    (U : X → Set X) (hU : ∀ x, IsOpen (U x)) (hcover : ∀ x, x ∈ U x)
    (hlocal : ∀ x s t, MeasurableSet s → MeasurableSet t → s ⊆ U x →
      μ (s ×ˢ t) = ν s * ξ t) : μ = ν.prod ξ := by
  obtain ⟨C, hC, hCU⟩ := isLindelof_univ.elim_countable_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hcover x⟩)
  apply Measure.ext_of_biUnion_eq_univ hC
    (s := fun x => U x ×ˢ (univ : Set Y))
  · apply eq_univ_of_forall
    intro z
    obtain ⟨x, hxC, hx⟩ := mem_iUnion₂.mp (hCU (mem_univ z.1))
    exact mem_iUnion₂.mpr ⟨x, hxC, hx, mem_univ z.2⟩
  · intro x _
    rw [← Measure.restrict_prod_eq_prod_univ]
    symm
    apply Measure.prod_eq
    intro s t hs ht
    rw [Measure.restrict_apply (hs.prod ht),
      show (s ×ˢ t) ∩ (U x ×ˢ univ) = (s ∩ U x) ×ˢ t by
        ext z; simp [and_assoc, and_comm, and_left_comm],
      hlocal x (s ∩ U x) t (hs.inter (hU x).measurableSet) ht inter_subset_right,
      Measure.restrict_apply hs]

end PoincareConjecture.RiemannianMetric
