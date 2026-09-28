import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Intervals.Completion
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.EmbeddedCircle
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Circle.CompactArc.Embedding







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.SaddleLevel
open _root_.PoincareConjecture

namespace M38Schoenflies










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1




theorem exists_exterior_interval_parametrizations
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) :
    let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
    ∃ H : S2 → Real, ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ H ∧
      (∀ q, H q = h p → mfderiv (𝓡 2) 𝓘(Real, Real) H q ≠ 0) ∧
      (∀ q ∈ K, H =ᶠ[𝓝 q] h) ∧ K ⊆ H ⁻¹' {h p} ∧
      ∀ q ∈ K, ∃ (γ : Real → S2) (a b : Real) (z : S2),
        ContMDiff 𝓘(Real, Real) (𝓡 2) ∞ γ ∧ Topology.IsEmbedding γ ∧
        (∀ t, Function.Injective (mfderiv 𝓘(Real, Real) (𝓡 2) γ t)) ∧
        a < b ∧ γ '' Icc a b = connectedComponentIn K q ∧ z ∉ K ∧
        range γ = connectedComponentIn (H ⁻¹' {h p}) q \ {z} := by
  let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
  obtain ⟨_, _, hK, _, _, _⟩ :=
    compact_regular_exterior hh hunique e he0 hep hform hr hrs
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨H, hH, hreg, hgerm, hKL, hproper⟩ :=
    exists_regular_completion_with_proper_components hh hunique e he0 hep he hei hform hr hrs
  refine ⟨H, hH, hreg, hgerm, hKL, ?_⟩
  intro q hq
  obtain ⟨hn, z, hz, hzK⟩ := hproper q hq
  have hJ : IsCompact (connectedComponentIn K q) := by
    rw [connectedComponentIn_eq_image hq]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  obtain ⟨f, hf, hfi, hfd, hfr⟩ :=
    exists_smooth_circle_regularLevelComponent hH (h p) hreg q (hKL hq)
  have hJr : connectedComponentIn K q ⊆ range f := by
    rw [hfr]
    exact connectedComponentIn_mono q hKL
  obtain ⟨γ, a, b, hγ, _, hγd, _, hγJ, hab, _, hγe, hγr⟩ :=
    Poincare.Geometry.Manifold.Circle.exists_interval_parametrization_in_circle_of_injective_mfderiv
      hf hfi hfd hJ (isConnected_connectedComponentIn_iff.mpr hq) hJr
      (hfr ▸ hz) (fun hzJ => hzK (connectedComponentIn_subset K q hzJ))
  exact ⟨γ, a, b, z, hγ, hγe, hγd, hab hn, hγJ, hzK, hfr ▸ hγr⟩

end Poincare.Manifold.Schoenflies.SaddleLevel

end

end M38Schoenflies
