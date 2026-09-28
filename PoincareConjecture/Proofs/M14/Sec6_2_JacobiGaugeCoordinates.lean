import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeFields

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b} {J : Set ℝ}

theorem gaugeLift_spatialCurve_contDiffOn
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β J) :
    ContDiffOn ℝ ∞ (fun s => (β s).2.val) J := by
  have hi : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) := contMDiff_subtype_val
  exact (hi.comp_contMDiffOn (fun s hs => (hβ s hs).snd)).contDiffOn

theorem exists_horizontalGauge_coordinates {q : G.Point} {s : ℝ}
    (h : (G.gaugeCover.cylinder b).toSpacetime (β s) = q) (Y : G.Horizontal q) :
    ∃ v : EuclideanSpace ℝ (Fin n),
      HEq Y ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 v) := by
  refine ⟨((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2).symm (h.symm ▸ Y), ?_⟩
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (eqRec_heq _ _).symm

theorem exists_smooth_horizontalGauge_coordinates {γ : ℝ → G.Point}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β J)
    (hrec : ∀ s ∈ J, (G.gaugeCover.cylinder b).toSpacetime (β s) = γ s)
    (Y : ∀ s, G.Horizontal (γ s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s) (Y s)) J) :
    ∃ f : ℝ → EuclideanSpace ℝ (Fin n), ContDiffOn ℝ ∞ f J ∧
      ∀ s ∈ J, HEq (Y s) ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 (f s)) := by
  classical
  let f : ℝ → EuclideanSpace ℝ (Fin n) := fun s =>
    ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2).symm
    (if hs : s ∈ J then (hrec s hs).symm ▸ Y s else 0)
  have hfield (s : ℝ) (hs : s ∈ J) :
      HEq (Y s) ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 (f s)) := by
    dsimp only [f]
    rw [ContinuousLinearEquiv.apply_symm_apply, dif_pos hs]
    exact (eqRec_heq _ _).symm
  let Y' := fun s => (G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 (f s)
  have hY' : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        ((G.gaugeCover.cylinder b).toSpacetime (β s)) (Y' s)) J :=
    hY.congr (fun s hs => Bundle.TotalSpace.ext (hrec s hs) (hfield s hs).symm)
  refine ⟨f, ?_, hfield⟩
  intro s hs
  have hp := movingGauge_horizontalField_pullback_contMDiffWithinAt
    (G.gaugeCover.cylinder b).toMovingSpacetimeGauge
    (G.gaugeCover.metric b).toMovingSpacetimeGaugeGeometry (hβ s hs) (hY' s hs)
  have hc := (G.gaugeCover.spatial b).tangentBundle_snd_contMDiff.contMDiffAt.comp_contMDiffWithinAt
    s hp
  have hf : ContMDiffWithinAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞ f J s := by
    apply hc.congr
    · intro r _
      exact (((G.gaugeCover.metric b).spatialTangentEquiv (β r).1 (β r).2).symm_apply_apply
        (f r)).symm
    · exact (((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2).symm_apply_apply
        (f s)).symm
  exact hf.contDiffWithinAt

end PoincareConjecture.M14
