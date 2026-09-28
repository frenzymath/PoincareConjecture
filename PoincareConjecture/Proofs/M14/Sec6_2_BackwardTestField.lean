import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)

theorem exists_supportedBackwardGaugeTest_at {s : ℝ} (hs : s ∈ Ioo τ₁ τ₂)
    (W : G.Horizontal (p.curve s)) :
    ∃ b : G.gaugeCover.index, ∃ U : Set G.Point,
      ∃ lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b,
      IsOpen U ∧ p.curve s ∈ U ∧
      ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U ∧
      (∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q) ∧
      ∃ η : ℝ → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ η ∧
        tsupport η ⊆ Ioo τ₁ τ₂ ∧ (∀ r ∈ tsupport η, p.curve r ∈ U) ∧
        ((G.gaugeCover.metric b).spatialTangentEquiv
          (lift (p.curve s)).1 (lift (p.curve s)).2 (η s)).val = W.val := by
  obtain ⟨b, U, lift, hU, hsU, hlift, hright, _⟩ := exists_smooth_gauge_lift G (p.curve s)
  let J := Ioo τ₁ τ₂ ∩ p.curve ⁻¹' U
  have hJ : IsOpen J := p.curve_regular.continuousOn.isOpen_inter_preimage isOpen_Ioo hU
  obtain ⟨ζ, hζs, _, hζ, _, hζone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hJ.mem_nhds ⟨hs, hsU⟩)
  have hW : ∃ v : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (lift (p.curve s))),
      v.val = W.val := by
    rw [hright _ hsU]
    exact ⟨W, rfl⟩
  obtain ⟨v, hv⟩ := hW
  obtain ⟨w, hw⟩ := ((G.gaugeCover.metric b).spatialTangentEquiv
    (lift (p.curve s)).1 (lift (p.curve s)).2).surjective v
  refine ⟨b, U, lift, hU, hsU, hlift, hright, fun r => ζ r • w,
    hζ.smul contDiff_const, ?_, ?_, ?_⟩
  · intro r hr
    exact (hζs (tsupport_smul_subset_left ζ (fun _ => w) hr)).1
  · intro r hr
    exact (hζs (tsupport_smul_subset_left ζ (fun _ => w) hr)).2
  · have hvalue : (G.gaugeCover.metric b).spatialTangentEquiv
        (lift (p.curve s)).1 (lift (p.curve s)).2 (ζ s • w) = v := by
      rw [hζone, one_smul, hw]
    exact (congrArg Subtype.val hvalue).trans hv

end PoincareConjecture.M14
