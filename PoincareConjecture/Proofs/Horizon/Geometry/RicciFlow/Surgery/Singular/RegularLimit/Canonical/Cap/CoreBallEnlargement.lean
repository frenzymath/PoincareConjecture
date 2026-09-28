import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.CoreBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.CompactCollar



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}




theorem exists_eventually_cap_core_ball_enlargement
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (L : ℝ) {cmax : ℝ} (hcmax : 1 < cmax) :
    ∃ c : ℝ, 1 < c ∧ c < cmax ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t),
        H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
        ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
        N.core_radius (H.reference.forward t ht x) ≤ L →
        let r := N.core_radius (H.reference.forward t ht x)
        let S := H.regularReferencePreimage P04 t ht
          ((F.metric t).ball (H.reference.forward t ht x) r)
        (H.terminalMetric P04).ball x (r / c) ⊆ S ∧
        S ⊆ (H.terminalMetric P04).ball x (c * r) ∧
        ∃ R : ℝ, c * r < R ∧ IsCompact (closure ((H.terminalMetric P04).ball x R)) := by
  obtain ⟨δ, hδ, henlarge⟩ :=
    (H.terminalMetric P04).exists_uniform_precompact_ball_enlargement hA
  have hcont : ContinuousAt (fun c : ℝ => (c - c⁻¹) * L) 1 :=
    (continuousAt_id.sub (continuousAt_id.inv₀ one_ne_zero)).mul_const L
  have hsmall : ∀ᶠ c : ℝ in 𝓝 1, (c - c⁻¹) * L < δ := by
    have hh := hcont.eventually (Iio_mem_nhds (show (1 - (1 : ℝ)⁻¹) * L < δ by simpa))
    exact hh
  have hchoose : ∀ᶠ c : ℝ in 𝓝[>] 1, 1 < c ∧ c < cmax ∧ (c - c⁻¹) * L < δ := by
    have hmax : ∀ᶠ c : ℝ in 𝓝[>] 1, c < cmax :=
      nhdsWithin_le_nhds (Iio_mem_nhds hcmax)
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
      hmax] with c hc hs hmax'
    exact ⟨hc, hmax', hs⟩
  obtain ⟨c, hc, hcmax', hmargin⟩ := hchoose.exists
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hcinv : c⁻¹ < 1 := (inv_lt_one₀ hcpos).mpr hc
  have hfactor : 0 ≤ c - c⁻¹ := by linarith
  refine ⟨c, hc, hcmax', ?_⟩
  filter_upwards [H.eventually_cap_core_ball_comparison P04 hA hc] with t hcompare
  intro ht N hcapture x hx hrL
  dsimp only
  let r := N.core_radius (H.reference.forward t ht x)
  obtain ⟨hsmallball, hlargeball, _⟩ := hcompare ht N hcapture x hx
  have hBN : (F.metric t).ball (H.reference.forward t ht x) r ⊆ N.carrier :=
    fun z hz => N.core_ball_subset _ hx (subset_closure hz)
  have hSA := H.regularReferencePreimage_subset P04 t ht
    ((F.metric t).ball (H.reference.forward t ht x) r)
    ((image_mono hBN).trans hcapture)
  refine ⟨hsmallball, hlargeball, r / c + δ, ?_,
    henlarge x (r / c) (div_pos (N.core_radius_pos _ hx) hcpos) (hsmallball.trans hSA)⟩
  have hh := (mul_le_mul_of_nonneg_left hrL hfactor).trans_lt hmargin
  change (c - c⁻¹) * r < δ at hh
  rw [div_eq_mul_inv]
  nlinarith

end PoincareConjecture.SingularTimeAssumptions
