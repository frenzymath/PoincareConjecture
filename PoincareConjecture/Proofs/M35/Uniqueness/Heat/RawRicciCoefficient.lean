import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCoordinateTrace
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawPrincipalExtension
import PoincareConjecture.Proofs.M35.Uniqueness.VectorHeatEnergy
import PoincareConjecture.Proofs.M13.CurvatureContractions
import PoincareConjecture.Proofs.M04.RicciRegularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem raw_ricciSharp_inverse_gram {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (x z : V) :
    RicciFlow.ricciSharp D x z = ∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
      (D.ricci x z (EuclideanSpace.single i 1) • EuclideanSpace.single j 1) := by
  let B : V →ₗ[ℝ] V →ₗ[ℝ] V :=
    (M13.ricciLinear D x z).smulRight (LinearMap.id : V →ₗ[ℝ] V)
  exact vector_bilinear_trace_inverse_gram g x B

theorem raw_ricci_pair_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (u v : V) :
    ContDiff ℝ ∞ (fun x => D.ricci x u v) := by
  have hu := euclidean_field_contMDiff (contDiff_const (c := u) : ContDiff ℝ ∞ (fun _ : V => u))
  have hv := euclidean_field_contMDiff (contDiff_const (c := v) : ContDiff ℝ ∞ (fun _ : V => v))
  have h := M04.contMDiffOn_ricci D isOpen_univ hu.contMDiffOn hv.contMDiffOn
  exact contDiffOn_univ.mp h.contDiffOn



theorem raw_ricciSharp_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (z : V) :
    ContDiff ℝ ∞ (fun x => RicciFlow.ricciSharp D x z) := by
  simp only [raw_ricciSharp_inverse_gram]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (raw_inverseGram_entry_contDiff g i j).smul
    ((raw_ricci_pair_contDiff D z (EuclideanSpace.single i 1)).smul contDiff_const)



def rawRicciLinear {g : RiemannianMetric n V} (D : LeviCivitaData g) (x : V) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap {
    toFun := RicciFlow.ricciSharp D x
    map_add' := by
      intro u v
      simp only [raw_ricciSharp_inverse_gram, ← M13.ricciLinear_apply, map_add,
        LinearMap.add_apply, add_smul, smul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c u
      simp only [raw_ricciSharp_inverse_gram, ← M13.ricciLinear_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      module }

theorem rawRicciLinear_contDiff {g : RiemannianMetric n V} (D : LeviCivitaData g) :
    ContDiff ℝ ∞ (rawRicciLinear D) := by
  apply contDiff_clm_apply_iff.mpr
  intro z
  exact raw_ricciSharp_contDiff D z



theorem exists_raw_compact_ricciSharp_bound {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {K : Set V} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ z : V,
      @norm V inferInstance (RicciFlow.ricciSharp D x z) ≤ C * ‖z‖ := by
  obtain ⟨C, hC, hb⟩ :=
    (hK.image (rawRicciLinear_contDiff D).continuous).isBounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro x hx z
  exact ((rawRicciLinear D x).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (hb _ ⟨x, hx, rfl⟩) (norm_nonneg z))

end PoincareConjecture.M35.Uniqueness.Heat
