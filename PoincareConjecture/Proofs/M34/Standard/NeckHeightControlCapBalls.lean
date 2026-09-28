import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlNormalized









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {m : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [IsManifold (𝓡 m) ∞ X]
  [T3Space X] [ConnectedSpace X] {g : RiemannianMetric 3 M} (N : CapCertificate g)






theorem exists_normalized_ball_in_standard_recut_image
    (h : RiemannianMetric m X) (hcomplete : MetricComplete h)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 m) 1 e e.source)
    (hi : ContMDiffOn (𝓡 m) (𝓡 3) 1 e.symm e.target)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 8)
    (haccuracy : N.epsilon < epsilon)
    (hcapture : closure (N.recutCarrier (2 / epsilon - N.epsilon⁻¹)) ⊆ e.source)
    (hbound : ∀ x ∈ closure (N.recutCarrier (2 / epsilon - N.epsilon⁻¹)),
      ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ 2 * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 m) e x v))
    {R : X → ℝ} (hR : Continuous R)
    (hboundary : ∀ x ∈ N.boundary_sphere, (2 * N.end_neck.scale ^ 2)⁻¹ ≤ R (e x))
    {o : M} (ho : o ∈ N.closed_core) (hRo : 0 < R (e o)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (Real.sqrt (R (e o)))⁻¹ ∧
      sSup (R '' h.ball (e o) r) = r⁻¹ ^ 2 ∧
      IsCompact (closure (h.ball (e o) r)) ∧
      closure (h.ball (e o) r) ⊆ e '' N.recutCarrier (2 / epsilon - N.epsilon⁻¹) := by
  let c := 1 / (4 * epsilon) - N.epsilon⁻¹
  let d := 1 / (2 * epsilon) - N.epsilon⁻¹
  let b := 2 / epsilon - N.epsilon⁻¹
  let L := N.end_neck.scale / (4 * epsilon)
  have he := hepsilon.ne'
  have hs := N.end_neck.scale_pos.ne'
  have hquarter : 0 < 1 / (4 * epsilon) := by positivity
  have htwo : 1 / (2 * epsilon) = 2 * (1 / (4 * epsilon)) := by ring
  have hone : 1 / epsilon = 4 * (1 / (4 * epsilon)) := by ring
  have height : 2 / epsilon = 8 * (1 / (4 * epsilon)) := by ring
  have hc : -N.epsilon⁻¹ < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c, d]; linarith
  have hdb : d < b := by dsimp [d, b]; linarith
  have hbinv : epsilon⁻¹ < N.epsilon⁻¹ :=
    (inv_lt_inv₀ hepsilon N.epsilon_pos).mpr haccuracy
  have hb : b < N.epsilon⁻¹ := by
    dsimp [b]
    rw [div_eq_mul_inv]
    linarith
  have hL : 0 < L := div_pos N.end_neck.scale_pos (by positivity)
  have hmu : 0 < (2 * N.end_neck.scale ^ 2)⁻¹ := by positivity
  have hgap : 1 < (2 * N.end_neck.scale ^ 2)⁻¹ * L ^ 2 := by
    have hid : (2 * N.end_neck.scale ^ 2)⁻¹ * L ^ 2 = 1 / (32 * epsilon ^ 2) := by
      dsimp [L]
      field_simp
      ring
    rw [hid]
    apply (lt_div_iff₀ (by positivity : 0 < 32 * epsilon ^ 2)).mpr
    have hsq := (sq_le_sq₀ hepsilon.le (by norm_num : (0 : ℝ) ≤ 1 / 8)).mpr hsmall
    nlinarith
  have hlength : (2 / N.end_neck.scale) * 2 * L ≤ b - d := by
    have hid : (2 / N.end_neck.scale) * 2 * L = 1 / epsilon := by
      dsimp [L]
      field_simp
      ring
    rw [hid]
    dsimp [b, d]
    linarith
  exact N.exists_normalized_ball_in_image_recutCarrier h hcomplete e hf hi hc hcd hdb hb
    (by norm_num : (0 : ℝ) < 2) hcapture hbound hmu hL hgap hlength hR hboundary ho hRo

end PoincareConjecture.CapCertificate
