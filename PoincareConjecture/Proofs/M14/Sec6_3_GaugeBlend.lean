import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetShift
import PoincareConjecture.Proofs.M09.SmoothJoinCutoff
import PoincareConjecture.Definitions.M14GeneralizedLGeometry

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

open Proofs.M09

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)
  (α β : ℝ → G.Point)

noncomputable def gaugeBlend (c d s : ℝ) : G.Point :=
  (G.gaugeCover.cylinder b).toSpacetime ((lift (β s)).1,
    (G.gaugeCover.spatial b).affineShift (lift (α s)).2
      (smoothJoinCutoff ((s - c) / d) • ((lift (β s)).2.val - (lift (α s)).2.val)))

theorem gaugeBlend_time (c d s : ℝ)
    (hβ : (G.gaugeCover.cylinder b).toSpacetime (lift (β s)) = β s) :
    G.spacetime.timeFunction (gaugeBlend b lift α β c d s) =
      G.spacetime.timeFunction (β s) := by
  rw [gaugeBlend, (G.gaugeCover.cylinder b).time_eq]
  exact ((G.gaugeCover.cylinder b).time_eq (lift (β s))).symm.trans
    (congrArg G.spacetime.timeFunction hβ)

theorem gaugeBlend_eq_left {c d s : ℝ} (hd : 0 < d) (hs : s ≤ c - d)
    (hα : (G.gaugeCover.cylinder b).toSpacetime (lift (α s)) = α s)
    (htime : (lift (α s)).1 = (lift (β s)).1) :
    gaugeBlend b lift α β c d s = α s := by
  have hχ : smoothJoinCutoff ((s - c) / d) = 0 :=
    smoothJoinCutoff_zero ((div_le_iff₀ hd).mpr (by linarith))
  simp only [gaugeBlend, hχ, zero_smul, TopologicalSpace.Opens.affineShift_zero, ← htime,
    Prod.mk.eta, hα]

theorem gaugeBlend_eq_right {c d s : ℝ} (hd : 0 < d) (hs : c + d ≤ s)
    (hβ : (G.gaugeCover.cylinder b).toSpacetime (lift (β s)) = β s) :
    gaugeBlend b lift α β c d s = β s := by
  have hχ : smoothJoinCutoff ((s - c) / d) = 1 :=
    smoothJoinCutoff_one ((le_div_iff₀ hd).mpr (by linarith))
  have hshift : (G.gaugeCover.spatial b).affineShift (lift (α s)).2
      ((lift (β s)).2.val - (lift (α s)).2.val) = (lift (β s)).2 := by
    apply Subtype.ext
    rw [(G.gaugeCover.spatial b).affineShift_val (by
      simpa only [add_sub_cancel] using (lift (β s)).2.property), add_sub_cancel]
  simp only [gaugeBlend, hχ, one_smul, hshift, Prod.mk.eta, hβ]

theorem gaugeBlend_contMDiffAt {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    {k : ℕ∞ω} (hk : k ≤ ∞) {c d s : ℝ}
    (hα : ContMDiffAt (𝓘(ℝ, ℝ)) (spacetimeModel n) k α s)
    (hβ : ContMDiffAt (𝓘(ℝ, ℝ)) (spacetimeModel n) k β s)
    (hαU : α s ∈ U) (hβU : β s ∈ U)
    (hmem : smoothJoinBlend (fun t => (lift (α t)).2.val)
      (fun t => (lift (β t)).2.val) c d s ∈ G.gaugeCover.spatial b) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (spacetimeModel n) k (gaugeBlend b lift α β c d) s := by
  have hA := (((hlift _ hαU).contMDiffAt (hU.mem_nhds hαU)).of_le hk).comp s hα
  have hB := (((hlift _ hβU).contMDiffAt (hU.mem_nhds hβU)).of_le hk).comp s hβ
  have hAv : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) k (fun t => (lift (α t)).2.val) s :=
    contMDiff_subtype_val.contMDiffAt.comp s hA.snd
  have hBv : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) k (fun t => (lift (β t)).2.val) s :=
    contMDiff_subtype_val.contMDiffAt.comp s hB.snd
  have hχ : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) k
      (fun t => smoothJoinCutoff ((t - c) / d)) s :=
    ((smoothJoinCutoff_contDiff.of_le hk).comp
      ((contDiff_id.sub contDiff_const).div_const d)).contMDiff.contMDiffAt
  have hshift := hχ.smul (hBv.sub hAv)
  have hspace := ((((G.gaugeCover.spatial b).affineShift_contMDiffOn _ hmem).contMDiffAt
    ((G.gaugeCover.spatial b).affineShift_domain_isOpen.mem_nhds hmem)).of_le hk).comp s
      (hA.snd.prodMk hshift)
  exact ((G.gaugeCover.cylinder b).smooth.of_le hk).contMDiffAt.comp s
    (hB.fst.prodMk hspace)

end PoincareConjecture.M14
