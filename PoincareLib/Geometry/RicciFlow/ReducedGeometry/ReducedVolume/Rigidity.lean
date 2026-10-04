import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Theory

/-!
# The strict reduced-volume bound

The Euclidean equality case in M10 is static on a nondegenerate time interval.
The Ricci-flow equation therefore forces zero Ricci curvature in its interior.
This excludes equality when scalar curvature is positive, as used in
Morgan--Tian Corollary 9.14, pp. 185-186, and Theorem 7.26 and
Proposition 7.27, pp. 165-167.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The Ricci-flow equation forces zero scalar curvature in the interior of
an interval on which a single Euclidean identification fixes the metric. -/
theorem IsStaticEuclideanFlowOn.scalarCurvature_eq_zero
    {J : Set ℝ} {F : RicciFlow n M J} {a b t : ℝ}
    (h : IsStaticEuclideanFlowOn F (Icc a b)) (hJ : Ioo a b ⊆ J)
    (ht : t ∈ Ioo a b) (x : M) : (F.connection t).scalarCurvature x = 0 := by
  obtain ⟨e, he⟩ := h
  have hRic (v w : TangentSpace (𝓡 n) x) : (F.connection t).ricci x v w = 0 := by
    have hz : HasDerivWithinAt (fun s ↦ (F.metric s).inner x v w) 0 (Ioo a b) t := by
      apply (hasDerivWithinAt_const t (Ioo a b)
        (inner ℝ (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w))).congr
      · intro s hs
        exact he s ⟨hs.1.le, hs.2.le⟩ x v w
      · exact he t ⟨ht.1.le, ht.2.le⟩ x v w
    have hd : UniqueDiffWithinAt ℝ (Ioo a b) t := isOpen_Ioo.uniqueDiffWithinAt ht
    have hderiv := ((F.equation t (hJ ht) x v w).mono hJ).derivWithin hd
    rw [hz.derivWithin hd] at hderiv
    linarith
  simp only [LeviCivitaData.scalarCurvature, hRic, Finset.sum_const_zero]

/-- Positive scalar curvature at one interior point excludes the Euclidean
reduced-volume equality case supplied by M10. -/
theorem reducedVolume_lt_euclidean_of_scalar_pos
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {F : RicciFlow n M (Iic 0)} {R τ : ℝ}
    (Q : ReducedVolumeTheory F 0 R) (hτ : 0 < τ) (hR : τ < R)
    (p x : M) (hscalar : 0 < (F.connection (-τ / 2)).scalarCurvature x) :
    reducedVolume F 0 p τ < euclideanReducedVolume n := by
  apply lt_of_le_of_ne (Q.volume_bounds p τ hτ hR).2
  intro heq
  have hflat := Q.euclidean_rigidity p τ hτ hR heq
  have hz := hflat.scalarCurvature_eq_zero
    (by intro s hs; exact hs.2.le) (t := -τ / 2)
    (by constructor <;> linarith) x
  linarith

end PoincareMT
