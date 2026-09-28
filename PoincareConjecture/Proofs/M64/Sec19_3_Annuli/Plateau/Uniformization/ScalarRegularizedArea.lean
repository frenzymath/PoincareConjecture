import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.AnnulusRegularizedMetric
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarSmoothDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)





theorem scalarAnnulus_ae_eq_closed :
    scalarAnnulus =ᵐ[volume] {p : Plane | 0 ≤ scalarAnnulusDefining p} := by
  have hnull (r : ℝ) : ∀ᵐ p : Plane ∂volume, p ∉ Metric.sphere (0 : Plane) r := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using Measure.addHaar_sphere volume (0 : Plane) r
  filter_upwards [hnull 1, hnull 2] with p hp1 hp2
  apply propext
  change (1 < ‖p‖ ∧ ‖p‖ < 2) ↔ 0 ≤ scalarAnnulusDefining p
  rw [scalarAnnulusDefining_nonneg]
  have h1 : ‖p‖ ≠ 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp1
  have h2 : ‖p‖ ≠ 2 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp2
  exact ⟨fun hp => ⟨hp.1.le, hp.2.le⟩,
    fun hp => ⟨lt_of_le_of_ne hp.1 h1.symm, lt_of_le_of_ne hp.2 h2⟩⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem m64RegularizedPullbackMetric_exists_annular_area_lt
    (g : RiemannianMetric n M) (f : Plane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (eta : ℝ) (heta : 0 < eta) :
    ∃ (delta : ℝ) (hdelta : 0 < delta),
      (∫ p in scalarAnnulus,
        m60AreaDensity (m64RegularizedPullbackMetric g f hf delta hdelta) id p) <
        (∫ p in scalarAnnulus, m60AreaDensity g f p) + eta := by
  simp_rw [setIntegral_congr_set scalarAnnulus_ae_eq_closed]
  exact m64RegularizedPullbackMetric_exists_area_lt g f hf
    scalarClosedAnnulus_isCompact eta heta

end PoincareConjecture.M64Uniformization
