import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.SpatialBounds
import PoincareConjecture.Proofs.M34.Mathlib.ClosedIntervalDerivativeBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Evolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.MetricFlowApproximation

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)] (A : MetricFlowApproximation ginit Mfamily)

theorem contDiffOn_interior_coefficients (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2)
      (Ioo 0 A.time ×ˢ A.source k) :=
  (A.contDiffOn_coefficients k).mono (prod_mono Ioo_subset_Icc_self (Subset.refl _))

theorem spatialJet_mem_domain (k : ℕ) (t : ℝ) {x : StandardCapSpace}
    (hx : x ∈ A.source k) :
    spatialJet 2 (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2) (t, x) ∈
      jetRicciFlowDomain 3 := by
  change ((twoJetProjection 3 (spatialJet 2
    (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2) (t, x))).1).IsInvertible
  rw [twoJetProjection_spatialJet]
  exact ((A.flow k).metric t).isInvertible_pullbackCoefficients
    (A.chart_invertible k _ hx).injective

theorem deriv_coefficients_eq_operator (k : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 A.time)
    {x : StandardCapSpace} (hx : x ∈ A.source k) :
    deriv (fun s => A.coefficients k s x) t =
      jetRicciFlowOperator 3
        (spatialJet 2 (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2) (t, x)) := by
  rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
  exact deriv_pullbackCoefficients_eq_ricciFlowOperator (A.interiorFlow k)
    isOpen_Ioo (A.source_isOpen k) (A.chart_smooth k)
    (fun _ hy => A.chart_invertible k _ hy) ht hx

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_compact_spatialJet_box (P : RicciFlowCurvatureTheory.{0})
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ L : Set (Jet StandardCapSpace (MetricCoefficient 3) (2 + m)),
      IsCompact L ∧ L ⊆ (baseProjection 2 m) ⁻¹' jetRicciFlowDomain 3 ∧
      ∀ k t, t ∈ Icc 0 A.time → ∀ x ∈ K, x ∈ A.source k →
        spatialJet (2 + m)
          (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2) (t, x) ∈ L := by
  obtain ⟨a, _b, ha, _hb, hcoeff⟩ := A.exists_compact_ellipticity P hK
  obtain ⟨B, hB, hbound⟩ := A.exists_compact_spatialJet_bounds P hK (2 + m)
  obtain ⟨L, hL, hLU, hbox⟩ := exists_compact_elliptic_jet_box 3 m ha B
  refine ⟨L, hL, hLU, ?_⟩
  intro k t ht x hx hsource
  apply hbox
  · apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hB)).mpr
    intro j
    exact hbound j (by omega) k t ht x hx hsource
  · exact fun v => (hcoeff k t ht x hx hsource v).1

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_compact_timeDeriv_spatialJet_bound (P : RicciFlowCurvatureTheory.{0})
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k t, t ∈ Ioo 0 A.time →
      ∀ x ∈ K, x ∈ A.source k →
        ‖deriv (fun s => iteratedFDeriv ℝ m (A.coefficients k s) x) t‖ ≤ C := by
  obtain ⟨L, hL, hLU, hrange⟩ := A.exists_compact_spatialJet_box P hK m
  let Q := operator 2 (jetRicciFlowOperator 3) m
  have hQ := contDiffOn_operator (isOpen_jetRicciFlowDomain 3)
    (contDiffOn_jetRicciFlowOperator 3) m
  obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn (f := Q)
    (hQ.continuousOn.mono hLU)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro k t ht x hx hsource
  have heq := deriv_spatialJet_eq_operator (isOpen_jetRicciFlowDomain 3)
    (contDiffOn_jetRicciFlowOperator 3) (A.contDiffOn_interior_coefficients k)
    isOpen_Ioo (A.source_isOpen k)
    (fun z hz => A.spatialJet_mem_domain k z.1 hz.2)
    (fun z hz => A.deriv_coefficients_eq_operator k hz.1 hz.2) m (z := (t, x)) ⟨ht, hsource⟩
  rw [heq]
  exact (hC _ (hrange k t (Ioo_subset_Icc_self ht) x hx hsource)).trans (le_max_left _ _)

theorem exists_compact_spatialJet_initial_modulus (P : RicciFlowCurvatureTheory.{0})
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k t, t ∈ Icc 0 A.time →
      ∀ x ∈ K, x ∈ A.source k →
        ‖iteratedFDeriv ℝ m (A.coefficients k t) x -
          iteratedFDeriv ℝ m ginit.euclideanCoefficients x‖ ≤ C * t := by
  obtain ⟨C, hC, hbound⟩ := A.exists_compact_timeDeriv_spatialJet_bound P hK m
  refine ⟨C, hC, ?_⟩
  intro k t ht x hx hsource
  rw [← A.spatialJet_zero k m hsource]
  have h : ‖iteratedFDeriv ℝ m (A.coefficients k t) x -
      iteratedFDeriv ℝ m (A.coefficients k 0) x‖ ≤ C * |t - 0| := by
    apply norm_sub_le_of_interior_deriv_bound_Icc
      (f := fun s => iteratedFDeriv ℝ m (A.coefficients k s) x) A.time_pos hC
    · exact A.continuousOn_spatialJet_time k m hsource
    · intro s hs
      exact A.differentiableAt_spatialJet_time k m hsource hs
    · exact fun s hs => hbound k s hs x hx hsource
    · exact ⟨le_rfl, A.time_pos.le⟩
    · exact ht
  simpa only [sub_zero, abs_of_nonneg ht.1] using h

end PoincareConjecture.M34.MetricFlowApproximation
