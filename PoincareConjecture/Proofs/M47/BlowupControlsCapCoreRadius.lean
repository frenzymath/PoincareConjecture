import PoincareConjecture.Proofs.M47.CanonicalCoreVolumeMargin
import PoincareConjecture.Proofs.M34.Standard.CapBallVolumeImage

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem exists_cap_image_core_radius_tolerance {g : RiemannianMetric 3 M}
    (N : CapCertificate g) {Lambda : ℝ} (hLambda : 1 < Lambda) :
    ∃ nu : ℝ, 0 < nu ∧
      ∀ {X : Type v} [TopologicalSpace X]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
        (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
        (e : OpenPartialHomeomorph M X),
      ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source → N.carrier ⊆ e.source →
      (∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
        h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
          Lambda * g.tangentNorm x w) →
      (∀ x ∈ N.carrier, N.connection.scalarCurvature x ≤ D.scalarCurvature (e x) + nu) →
      ∀ y ∈ N.core, ∀ r : ℝ, 0 < r →
        BddAbove (D.scalarCurvature '' h.ball (e y) r) →
        scalarCurvatureSupOn h D (h.ball (e y) r) = r⁻¹ ^ 2 →
        r ≤ Lambda * N.core_radius y := by
  obtain ⟨B, hB1, hB⟩ := Proofs.M47.cap_core_radii_bounded N
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hLpos : 0 < Lambda := zero_lt_one.trans hLambda
  have hLinv : 0 < Lambda⁻¹ := inv_pos.mpr hLpos
  have hLinv1 : Lambda⁻¹ < 1 := (inv_lt_one₀ hLpos).mpr hLambda
  have hfactor : 0 < 1 - Lambda⁻¹ ^ 2 := by nlinarith
  let nu := (1 - Lambda⁻¹ ^ 2) * B⁻¹ ^ 2 / 2
  have hnu : 0 < nu := half_pos (mul_pos hfactor (sq_pos_of_pos (inv_pos.mpr hBpos)))
  refine ⟨nu, hnu, ?_⟩
  intro X _ _ _ h D e hf hsource hupper hscalar y hy r hr hb hnorm
  let r0 := N.core_radius y
  have hr0 : 0 < r0 := N.core_radius_pos y hy
  have hballsource : g.ball y r0 ⊆ e.source :=
    fun _ hz => hsource (N.core_ball_subset y hy (subset_closure hz))
  have hyball : y ∈ g.ball y r0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) y y < ENNReal.ofReal r0
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr0
  by_contra hnot
  have hlarge : Lambda * r0 < r := lt_of_not_ge hnot
  have himage : e '' g.ball y r0 ⊆ h.ball (e y) r :=
    g.image_ball_subset_ball_of_tangentNorm_le_on_open h e e.open_source hf hLpos
      hupper hballsource hlarge.le
  have hsup : r0⁻¹ ^ 2 ≤ r⁻¹ ^ 2 + nu := by
    rw [← N.core_radius_eq y hy, scalarCurvatureSupOn, ← image_eq_range]
    apply csSup_le ⟨N.connection.scalarCurvature y,
      mem_image_of_mem N.connection.scalarCurvature hyball⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzcarrier := N.core_ball_subset y hy (subset_closure hz)
    have hnew := le_csSup hb (mem_image_of_mem D.scalarCurvature
      (himage (mem_image_of_mem e hz)))
    have hnew' : D.scalarCurvature (e z) ≤ r⁻¹ ^ 2 := by
      simpa only [← hnorm, scalarCurvatureSupOn, image_eq_range] using hnew
    exact (hscalar z hzcarrier).trans (add_le_add hnew' le_rfl)
  have hBsq : B⁻¹ ^ 2 ≤ r0⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_pos.mpr hBpos).le
      ((inv_le_inv₀ hBpos hr0).mpr (hB y hy).2) 2
  have hgap : nu < (1 - Lambda⁻¹ ^ 2) * r0⁻¹ ^ 2 := by
    have hle := mul_le_mul_of_nonneg_left hBsq hfactor.le
    dsimp [nu] at *
    nlinarith [mul_pos hfactor (sq_pos_of_pos (inv_pos.mpr hBpos))]
  have hrinv : r⁻¹ ^ 2 ≤ Lambda⁻¹ ^ 2 * r0⁻¹ ^ 2 := by
    have h := pow_le_pow_left₀ (inv_pos.mpr hr).le
      ((inv_le_inv₀ hr (mul_pos hLpos hr0)).mpr hlarge.le) 2
    simpa only [mul_inv, mul_pow] using h
  nlinarith

end PoincareConjecture.M47
