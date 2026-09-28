import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetShift
import PoincareConjecture.Proofs.M14.Sec6_1_CompactPerturbation

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))

noncomputable def backwardGaugeFamily (v t : ℝ) : G.Point :=
  (G.gaugeCover.cylinder b).toSpacetime ((lift (p.curve t)).1,
    (G.gaugeCover.spatial b).affineShift (lift (p.curve t)).2 (v • η t))

noncomputable def supportedBackwardGaugeFamily (v t : ℝ) : G.Point := by
  classical
  exact if t ∈ tsupport η then backwardGaugeFamily p b lift η v t else p.curve t

theorem supportedBackwardGaugeFamily_eq_of_not_tsupport {t : ℝ} (ht : t ∉ tsupport η)
    (v : ℝ) : supportedBackwardGaugeFamily p b lift η v t = p.curve t := by
  simp only [supportedBackwardGaugeFamily, if_neg ht]

theorem supportedBackwardGaugeFamily_eq_gauge {t : ℝ}
    (ht : (G.gaugeCover.cylinder b).toSpacetime (lift (p.curve t)) = p.curve t) (v : ℝ) :
    supportedBackwardGaugeFamily p b lift η v t = backwardGaugeFamily p b lift η v t := by
  by_cases hs : t ∈ tsupport η
  · simp only [supportedBackwardGaugeFamily, if_pos hs]
  · rw [supportedBackwardGaugeFamily_eq_of_not_tsupport p b lift η hs]
    simp only [backwardGaugeFamily, image_eq_zero_of_notMem_tsupport hs, smul_zero,
      TopologicalSpace.Opens.affineShift_zero, Prod.mk.eta]
    exact ht.symm

theorem supportedBackwardGaugeFamily_at_zero
    (hsrc : ∀ t ∈ tsupport η,
      (G.gaugeCover.cylinder b).toSpacetime (lift (p.curve t)) = p.curve t) (t : ℝ) :
    supportedBackwardGaugeFamily p b lift η 0 t = p.curve t := by
  by_cases hs : t ∈ tsupport η
  · rw [supportedBackwardGaugeFamily_eq_gauge p b lift η (hsrc t hs)]
    simp only [backwardGaugeFamily, zero_smul, TopologicalSpace.Opens.affineShift_zero,
      Prod.mk.eta, hsrc t hs]
  · exact supportedBackwardGaugeFamily_eq_of_not_tsupport p b lift η hs 0

theorem supportedBackwardGaugeFamily_time
    (hclock : ∀ t ∈ tsupport η, (lift (p.curve t)).1.val =
      G.spacetime.timeFunction (p.curve t)) {t : ℝ} (ht : t ∈ Icc τ₁ τ₂) (v : ℝ) :
    G.spacetime.timeFunction (supportedBackwardGaugeFamily p b lift η v t) = T - t := by
  by_cases hs : t ∈ tsupport η
  · simp only [supportedBackwardGaugeFamily, if_pos hs, backwardGaugeFamily,
      (G.gaugeCover.cylinder b).time_eq, hclock t hs, p.curve_time t ht]
  · rw [supportedBackwardGaugeFamily_eq_of_not_tsupport p b lift η hs,
      p.curve_time t ht]

theorem backwardGaugeFamily_contMDiffAt {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiff ℝ ∞ η) {t v : ℝ} (ht : t ∈ Ioo τ₁ τ₂) (hsrc : p.curve t ∈ U)
    (hshift : (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 (backwardGaugeFamily p b lift η v) t := by
  have hp := (p.curve_regular t ht).contMDiffAt (isOpen_Ioo.mem_nhds ht)
  have hL := (((hlift _ hsrc).contMDiffAt (hU.mem_nhds hsrc)).of_le (by simp)).comp t hp
  have hηC1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hη1 : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun s => v • η s) t :=
    ((contDiff_const (c := v)).smul hηC1).contMDiff.contMDiffAt
  have hS := ((((G.gaugeCover.spatial b).affineShift_contMDiffOn _ hshift).contMDiffAt
    ((G.gaugeCover.spatial b).affineShift_domain_isOpen.mem_nhds hshift)).of_le
      (by simp)).comp t (hL.snd.prodMk hη1)
  exact ((G.gaugeCover.cylinder b).smooth.of_le (by simp)).contMDiffAt.comp t
    (hL.fst.prodMk hS)

theorem supportedBackwardGaugeFamily_contMDiffOn {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η) (hsrc : ∀ t ∈ tsupport η, p.curve t ∈ U) {v : ℝ}
    (hshift : ∀ t ∈ tsupport η,
      (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1
      (supportedBackwardGaugeFamily p b lift η v) (Ioo τ₁ τ₂) := by
  intro t ht
  by_cases hs : t ∈ tsupport η
  · have hp := (p.curve_regular t ht).contMDiffAt (isOpen_Ioo.mem_nhds ht)
    have heq : supportedBackwardGaugeFamily p b lift η v =ᶠ[𝓝 t]
        backwardGaugeFamily p b lift η v := by
      filter_upwards [hp.continuousAt.preimage_mem_nhds (hU.mem_nhds (hsrc t hs))]
        with s hsp
      exact supportedBackwardGaugeFamily_eq_gauge p b lift η (hright _ hsp) v
    exact ((backwardGaugeFamily_contMDiffAt p b lift η hU hlift hη ht (hsrc t hs)
      (hshift t hs)).congr_of_eventuallyEq heq).contMDiffWithinAt
  · have heq : supportedBackwardGaugeFamily p b lift η v =ᶠ[𝓝 t] p.curve := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hs] with s hsp
      exact supportedBackwardGaugeFamily_eq_of_not_tsupport p b lift η hsp v
    exact (p.curve_regular t ht).congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

theorem supportedBackwardGaugeFamily_continuousOn {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η) (hsupport : tsupport η ⊆ Ioo τ₁ τ₂)
    (hsrc : ∀ t ∈ tsupport η, p.curve t ∈ U) {v : ℝ}
    (hshift : ∀ t ∈ tsupport η,
      (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b) :
    ContinuousOn (supportedBackwardGaugeFamily p b lift η v) (Icc τ₁ τ₂) := by
  intro t ht
  by_cases hs : t ∈ tsupport η
  · exact (((supportedBackwardGaugeFamily_contMDiffOn p b lift η hU hlift hright hη
      hsrc hshift) t (hsupport hs)).contMDiffAt
        (isOpen_Ioo.mem_nhds (hsupport hs))).continuousAt.continuousWithinAt
  · have heq : supportedBackwardGaugeFamily p b lift η v =ᶠ[𝓝 t] p.curve := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hs] with s hsp
      exact supportedBackwardGaugeFamily_eq_of_not_tsupport p b lift η hsp v
    exact (p.curve_continuous t ht).congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

end PoincareConjecture.M14
