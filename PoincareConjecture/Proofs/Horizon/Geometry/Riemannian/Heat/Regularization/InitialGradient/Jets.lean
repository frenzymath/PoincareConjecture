import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient.Dirichlet








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Elliptic.InteriorEstimates

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)



theorem exists_heat_test_initial_coordinate_jet_bound
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {V K : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVs : closure V ⊆ e.source) (hK : IsCompact K) (hKV : K ⊆ V)
    (f : M → ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω),
      e '' V ⊆ Ω → ∀ (φ : EnergyTest D Ω), (φ : M → ℝ) = f →
      ∀ {t : ℝ} (ht : 0 < t), ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun z => heatPowerContinuous D S 0 t ht
          (toDomainL2 D Ω (φ : H1Zero D Ω)) (e z) - f (e z)) x‖ ≤ C * t := by
  obtain ⟨P, hP, hKP, hPV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  have hPc : IsCompact (closure P) :=
    hVc.of_isClosed_subset isClosed_closure (hPV.trans subset_closure)
  have hPs : closure P ⊆ e.source := hPV.trans (subset_closure.trans hVs)
  obtain ⟨q, A, hA, hbound⟩ := uniform_interior_estimate_of_elliptic_powers
    hV hP hPc hPV hK hKP (coordinatePrincipalCoefficients g e)
    (coordinateDriftCoefficients g e)
    (fun i j => (contDiffOn_coordinatePrincipalCoefficients e he hei i j).mono
      (subset_closure.trans hVs))
    (fun x hx => coordinatePrincipalCoefficients_posDef e he hei (hVs (subset_closure hx)))
    (fun i => (contDiffOn_coordinateDriftCoefficients e he hei i).mono
      (subset_closure.trans hVs)) m
  obtain ⟨B, hB, hcoord⟩ :=
    g.exists_eLpNorm_coordinate_pullback_restrict_le e he hei hP hPc hPs
  let T := ∑ j ∈ Finset.range (q + 1),
    (eLpNorm ((D.laplacian)^[j + 1] f) 2 g.volumeMeasure).toReal
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => ENNReal.toReal_nonneg)
  refine ⟨A * B * (T + 1), mul_pos (mul_pos hA hB) (by positivity), ?_⟩
  intro Ω S hVΩ φ hφ t ht x hx
  subst f
  let u := fun y => heatPowerContinuous D S 0 t ht
    (toDomainL2 D Ω (φ : H1Zero D Ω)) y - φ y
  have hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u Ω :=
    (contMDiffOn_heatPowerContinuous D S 0 t ht _).sub φ.smooth.contMDiffOn
  have huc : ContDiffOn ℝ ∞ (u ∘ e) V :=
    contMDiffOn_iff_contDiffOn.mp
      (hu.comp (he.mono (subset_closure.trans hVs)) (fun z hz => hVΩ ⟨z, hz, rfl⟩))
  have hPΩ : e '' P ⊆ Ω := (image_mono (subset_closure.trans hPV)).trans hVΩ
  have hnorm (j : ℕ) :
      (eLpNorm ((secondOrderOperator (coordinatePrincipalCoefficients g e)
        (coordinateDriftCoefficients g e))^[j] (u ∘ e)) 2 (volume.restrict P)).toReal ≤
      B * (t * (eLpNorm ((D.laplacian)^[j + 1] (φ : M → ℝ)) 2 g.volumeMeasure).toReal) := by
    have heq := iterate_secondOrderOperator_coordinate_eq_laplacian D e he hei
      S.isOpen hu hP (subset_closure.trans hPs) hPΩ j
    have hae : ((secondOrderOperator (coordinatePrincipalCoefficients g e)
        (coordinateDriftCoefficients g e))^[j] (u ∘ e)) =ᵐ[volume.restrict P]
        (fun z => ((D.laplacian)^[j] u) (e z)) := by
      filter_upwards [ae_restrict_mem hP.measurableSet] with z hz
      exact heq hz
    rw [eLpNorm_congr_ae hae]
    obtain ⟨hmem, hnorm⟩ := eLpNorm_iterate_laplacian_heat_test_sub_le D S φ j ht
    exact ((hcoord Ω hPΩ _ hmem).2).trans
      (mul_le_mul_of_nonneg_left hnorm hB.le)
  apply (hbound huc x hx).trans
  calc
    _ ≤ A * ∑ j ∈ Finset.range (q + 1),
        B * (t * (eLpNorm ((D.laplacian)^[j + 1] (φ : M → ℝ)) 2 g.volumeMeasure).toReal) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hnorm j)) hA.le
    _ = A * B * T * t := by
      simp only [T, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ A * B * (T + 1) * t := by gcongr; exact le_add_of_nonneg_right zero_le_one

end PoincareConjecture.LeviCivitaData.Dirichlet
