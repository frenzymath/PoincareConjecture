import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.CoordinateOperator







set_option autoImplicit false

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

omit [NeZero n] [MeasurableSpace M] [BorelSpace M] [T3Space M] in
theorem coordinatePrincipalCoefficients_posDef
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) : (coordinatePrincipalCoefficients g e x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    change coordinatePrincipalCoefficients g e x j i = coordinatePrincipalCoefficients g e x i j
    exact coordinatePrincipalCoefficients_symm e he hei hx j i
  · intro v hv
    have hv' : (WithLp.toLp 2 v : E) ≠ 0 := fun h => hv (congrArg WithLp.ofLp h)
    have hp := coordinatePrincipalCoefficients_pos (g := g) e he hei hx (WithLp.toLp 2 v) hv'
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, PiLp.toLp_apply, mul_left_comm, mul_comm, mul_assoc] using hp

theorem exists_heatPowerContinuous_coordinate_jet_bound
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {V K : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVs : closure V ⊆ e.source) (hK : IsCompact K) (hKV : K ⊆ V)
    (k m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω),
      e '' V ⊆ Ω → ∀ {t : ℝ} (hat : a ≤ t)
      (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)), ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m
        (fun z => heatPowerContinuous D S k t (ha.trans_le hat) f (e z)) x‖ ≤ C * ‖f‖ := by
  obtain ⟨P, hP, hKP, hPV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  have hPc : IsCompact (closure P) :=
    hVc.of_isClosed_subset isClosed_closure (hPV.trans subset_closure)
  have hPs : closure P ⊆ e.source := hPV.trans (subset_closure.trans hVs)
  have hPV' : P ⊆ V := subset_closure.trans hPV
  obtain ⟨q, A, hA, hbound⟩ := uniform_interior_estimate_of_elliptic_powers
    hV hP hPc hPV hK hKP (coordinatePrincipalCoefficients g e)
    (coordinateDriftCoefficients g e)
    (fun i j => (contDiffOn_coordinatePrincipalCoefficients e he hei i j).mono
      (subset_closure.trans hVs))
    (fun x hx => coordinatePrincipalCoefficients_posDef e he hei (hVs (subset_closure hx)))
    (fun i => (contDiffOn_coordinateDriftCoefficients e he hei i).mono
      (subset_closure.trans hVs)) m
  obtain ⟨B, hB, hcoord⟩ := g.exists_eLpNorm_coordinate_pullback_le e he hei hP hPc hPs
  let T : ℝ := ∑ j ∈ Finset.range (q + 1), (((k + j).factorial : ℝ) / a ^ (k + j))
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => by positivity)
  refine ⟨A * B * (T + 1), mul_pos (mul_pos hA hB) (by positivity), ?_⟩
  intro Ω S hVΩ t hat f x hx
  have ht : 0 < t := ha.trans_le hat
  let u : M → ℝ := heatPowerContinuous D S k t ht f
  have hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u Ω :=
    contMDiffOn_heatPowerContinuous D S k t ht f
  have huc : ContDiffOn ℝ ∞ (u ∘ e) V := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact hu.comp (he.mono (subset_closure.trans hVs)) (fun z hz => hVΩ ⟨z, hz, rfl⟩)
  have hPΩ : e '' P ⊆ Ω := (image_mono hPV').trans hVΩ
  have hPimage := e.isOpen_image_of_subset_source hP (subset_closure.trans hPs)
  have hnorm (j : ℕ) :
      (eLpNorm ((secondOrderOperator (coordinatePrincipalCoefficients g e)
        (coordinateDriftCoefficients g e))^[j] (u ∘ e)) 2 (volume.restrict P)).toReal ≤
        B * ((((k + j).factorial : ℝ) / a ^ (k + j)) * ‖f‖) := by
    have heq := iterate_secondOrderOperator_coordinate_eq_laplacian D e he hei
      S.isOpen hu hP (subset_closure.trans hPs) hPΩ j
    have hae : ((secondOrderOperator (coordinatePrincipalCoefficients g e)
        (coordinateDriftCoefficients g e))^[j] (u ∘ e)) =ᵐ[volume.restrict P]
        (fun z => ((D.laplacian)^[j] u) (e z)) := by
      filter_upwards [ae_restrict_mem hP.measurableSet] with z hz
      exact heq hz
    rw [eLpNorm_congr_ae hae]
    have hmem : MemLp ((D.laplacian)^[j] u) 2 (g.volumeMeasure.restrict (e '' P)) := by
      have heqlap := iterate_laplacian_heatPowerContinuous D S j k t ht f
      have heqae : ((D.laplacian)^[j] u) =ᵐ[g.volumeMeasure.restrict (e '' P)]
          (fun y => (-1 : ℝ)^j * heatPowerContinuous D S (k + j) t ht f y) := by
        filter_upwards [ae_restrict_mem hPimage.measurableSet] with y hy
        exact heqlap (hPΩ hy)
      apply (memLp_congr_ae heqae).mpr
      exact ((memLp_heatPowerContinuous D S (k + j) t ht f).mono_measure
        (Measure.restrict_mono hPΩ le_rfl)).const_mul _
    have hc := (hcoord ((D.laplacian)^[j] u) hmem).2
    apply hc.trans
    exact mul_le_mul_of_nonneg_left
      (eLpNorm_iterate_laplacian_heatPowerContinuous_restrict_le D S
        hPimage.measurableSet hPΩ j k ha hat f) hB.le
  have hj := hbound huc x hx
  apply hj.trans
  calc
    A * ∑ j ∈ Finset.range (q + 1),
        (eLpNorm ((secondOrderOperator (coordinatePrincipalCoefficients g e)
          (coordinateDriftCoefficients g e))^[j] (u ∘ e)) 2 (volume.restrict P)).toReal
        ≤ A * ∑ j ∈ Finset.range (q + 1),
          B * ((((k + j).factorial : ℝ) / a ^ (k + j)) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hnorm j)) hA.le
    _ = A * B * T * ‖f‖ := by
      simp only [T, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ A * B * (T + 1) * ‖f‖ := by gcongr; exact le_add_of_nonneg_right zero_le_one

end PoincareConjecture.LeviCivitaData.Dirichlet
