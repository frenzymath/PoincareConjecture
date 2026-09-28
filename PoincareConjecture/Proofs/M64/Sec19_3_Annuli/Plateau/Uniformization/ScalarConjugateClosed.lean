import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugateBoundaryForm













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ







theorem scalarCoverFormOfDifferential_uniform_bound
    (g : RiemannianMetric 2 Plane) (J : Plane → Plane →L[ℝ] ℝ)
    (hB : ContinuousOn (scalarCoverFormOfDifferential g J) (closure scalarCoverStrip)) :
    ∃ K : ℝ≥0, ∀ z ∈ closure scalarCoverStrip,
      ‖scalarCoverFormOfDifferential g J z‖₊ ≤ K := by
  let S : Set Cover := Icc (1, 0) (2, 1)
  have hS : S ⊆ closure scalarCoverStrip := by
    intro z hz
    rw [scalarCoverStrip_closure]
    exact ⟨hz.1.1, hz.2.1⟩
  obtain ⟨C, hC⟩ := (show IsCompact S from isCompact_Icc).exists_bound_of_continuousOn
    (hB.mono hS)
  refine ⟨⟨max 0 C, le_max_left _ _⟩, ?_⟩
  intro z hz
  have hzrad : z.1 ∈ Icc (1 : ℝ) 2 := by
    rw [scalarCoverStrip_closure] at hz
    exact hz
  have hper : Function.Periodic (fun t : ℝ => scalarCoverFormOfDifferential g J (z.1, t)) 1 := by
    intro t
    simpa only [Prod.mk_add_mk, add_zero] using
      scalarCoverFormOfDifferential_periodic g J (z.1, t)
  have hfrac : scalarCoverFormOfDifferential g J (z.1, Int.fract z.2) =
      scalarCoverFormOfDifferential g J z := by
    simpa only [Int.fract, mul_one, Prod.eta] using hper.sub_int_mul_eq (Int.floor z.2)
  have hmem : (z.1, Int.fract z.2) ∈ S :=
    ⟨⟨hzrad.1, Int.fract_nonneg _⟩, ⟨hzrad.2, (Int.fract_lt_one _).le⟩⟩
  change ‖scalarCoverFormOfDifferential g J z‖ ≤ max 0 C
  rw [← hfrac]
  exact (hC _ hmem).trans (le_max_right _ _)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







theorem exists_scalar_conjugate_closed_differential
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (P : ℝ) (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P) :
    ∃ (J : Plane → Plane →L[ℝ] ℝ) (K : ℝ≥0) (W : Cover → ℝ),
      ContinuousOn J (closure scalarAnnulus) ∧ EqOn J (fderiv ℝ H) scalarAnnulus ∧
      (∀ x ∈ closure scalarAnnulus, x ∉ scalarAnnulus → J x ≠ 0) ∧
      LipschitzWith K W ∧ EqOn W V scalarCoverStrip ∧
      ContinuousOn (scalarCoverFormOfDifferential g J) (closure scalarCoverStrip) ∧
      (∀ z ∈ closure scalarCoverStrip, W (z + (0, 1)) = W z + P) ∧
      ∀ z ∈ closure scalarCoverStrip,
        HasFDerivWithinAt W (scalarCoverFormOfDifferential g J z) (closure scalarCoverStrip) z := by
  obtain ⟨J, hJc, hJeq, hJn, hBc, hBeq⟩ :=
    exists_scalarCoverForm_boundary_extension D hHc hHs hlap hinner houter
  obtain ⟨K, hK⟩ := scalarCoverFormOfDifferential_uniform_bound g J hBc
  have hVL : LipschitzOnWith K V scalarCoverStrip := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hdV z hz).differentiableAt) _ scalarCoverStrip_convex
    intro z hz
    rw [(hdV z hz).fderiv, ← hBeq hz]
    exact hK z (subset_closure hz)
  obtain ⟨W, hW, hWV⟩ := hVL.extend_real
  have hdW (z : Cover) (hz : z ∈ scalarCoverStrip) :
      HasFDerivAt W (scalarCoverFormOfDifferential g J z) z := by
    rw [hBeq hz]
    apply (hdV z hz).congr_of_eventuallyEq
    filter_upwards [scalarCoverStrip_isOpen.mem_nhds hz] with y hy
    exact (hWV hy).symm
  have hperiod : ∀ z ∈ closure scalarCoverStrip, W (z + (0, 1)) = W z + P := by
    apply closure_minimal _ (isClosed_eq
      (hW.continuous.comp (continuous_id.add continuous_const))
      (hW.continuous.add continuous_const))
    intro z hz
    change W (z + (0, 1)) = W z + P
    have hz' : z + (0, 1) ∈ scalarCoverStrip := by simpa [scalarCoverStrip] using hz
    rw [← hWV hz', ← hWV hz]
    exact hdeck z hz
  refine ⟨J, K, W, hJc, hJeq, hJn, hW, hWV.symm, hBc, hperiod, ?_⟩
  intro z hz
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hdW y hy).differentiableAt.differentiableWithinAt)
    scalarCoverStrip_convex scalarCoverStrip_isOpen
    (fun _ _ => hW.continuous.continuousWithinAt)
  apply ((hBc z hz).mono subset_closure).tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hdW y hy).fderiv.symm

end PoincareConjecture.M64Uniformization
