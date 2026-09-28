import PoincareConjecture.Proofs.M14.Sec6_3_ParameterizedGaugeFamily
import PoincareConjecture.Proofs.M14.Mathlib.CompactFamilyTube










set_option autoImplicit false

open Set

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {P : Type v} (f : ℝ × P → G.Point) (j : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j) (χ : ℝ → ℝ) (d : P → EuclideanSpace ℝ (Fin n))



theorem supportedGaugeTranslateFamily_eq_of_not_tsupport {z : ℝ × P}
    (hs : z.1 ∉ tsupport χ) : supportedGaugeTranslateFamily f j lift χ d z = f z := by
  simp only [supportedGaugeTranslateFamily, if_neg hs]



theorem supportedGaugeTranslateFamily_eq_of_zero {z : ℝ × P}
    (hz : (G.gaugeCover.cylinder j).toSpacetime (lift (f z)) = f z) (hd : d z.2 = 0) :
    supportedGaugeTranslateFamily f j lift χ d z = f z := by
  rw [supportedGaugeTranslateFamily_eq_gauge f j lift χ d hz]
  simp only [gaugeTranslateFamily, hd, smul_zero,
    TopologicalSpace.Opens.affineShift_zero, Prod.mk.eta, hz]



theorem supportedGaugeTranslateFamily_time {z : ℝ × P}
    (hz : z.1 ∈ tsupport χ → (G.gaugeCover.cylinder j).toSpacetime (lift (f z)) = f z) :
    G.spacetime.timeFunction (supportedGaugeTranslateFamily f j lift χ d z) =
      G.spacetime.timeFunction (f z) := by
  by_cases hs : z.1 ∈ tsupport χ
  · rw [supportedGaugeTranslateFamily_eq_gauge f j lift χ d (hz hs)]
    simp only [gaugeTranslateFamily, (G.gaugeCover.cylinder j).time_eq]
    exact ((G.gaugeCover.cylinder j).time_eq (lift (f z))).symm.trans
      (congrArg G.spacetime.timeFunction (hz hs))
  · rw [supportedGaugeTranslateFamily_eq_of_not_tsupport f j lift χ d hs]



theorem supportedGaugeTranslateFamily_eq_target {z : ℝ × P}
    (hz : (G.gaugeCover.cylinder j).toSpacetime (lift (f z)) = f z)
    (hχ : χ z.1 = 1) (y : G.gaugeCover.spatial j)
    (hd : d z.2 = y.val - (lift (f z)).2.val) :
    supportedGaugeTranslateFamily f j lift χ d z =
      (G.gaugeCover.cylinder j).toSpacetime ((lift (f z)).1, y) := by
  rw [supportedGaugeTranslateFamily_eq_gauge f j lift χ d hz]
  have hshift : (lift (f z)).2.val + χ z.1 • d z.2 ∈ G.gaugeCover.spatial j := by
    rw [hχ, one_smul, hd, add_comm, sub_add_cancel]
    exact y.property
  have hpoint : (G.gaugeCover.spatial j).affineShift (lift (f z)).2 (χ z.1 • d z.2) = y := by
    apply Subtype.ext
    rw [(G.gaugeCover.spatial j).affineShift_val hshift, hχ, one_smul, hd,
      add_comm, sub_add_cancel]
  simp only [gaugeTranslateFamily, hpoint]

variable [TopologicalSpace P]




theorem exists_supportedGaugeTranslate_tube {C : Set ℝ} {U : Set P} {V : Set G.Point}
    (hC : IsCompact C) (hU : IsOpen U) (hf : ContinuousOn f (C ×ˢ U))
    (hlift : ContinuousOn lift V) (hχ : Continuous χ) (hd : ContinuousOn d U)
    (hsrc : ∀ z ∈ C ×ˢ U, z.1 ∈ tsupport χ → f z ∈ V)
    {p : P} (hp : p ∈ U) (hdp : d p = 0) :
    ∃ N : Set P, IsOpen N ∧ p ∈ N ∧ N ⊆ U ∧
      ∀ z ∈ C ×ˢ N, z.1 ∈ tsupport χ →
        (lift (f z)).2.val + χ z.1 • d z.2 ∈ G.gaugeCover.spatial j := by
  let K := C ∩ tsupport χ
  have hK : IsCompact K := hC.inter_right (isClosed_tsupport χ)
  have hL : ContinuousOn (fun z : ℝ × P => lift (f z)) (K ×ˢ U) :=
    hlift.comp (hf.mono (fun _ hz => ⟨hz.1.1, hz.2⟩))
      (fun z hz => hsrc z ⟨hz.1.1, hz.2⟩ hz.1.2)
  let F := fun z : ℝ × P => (lift (f z)).2.val + χ z.1 • d z.2
  have hF : ContinuousOn F (K ×ˢ U) :=
    (continuous_subtype_val.comp_continuousOn hL.snd).add
      ((hχ.comp continuous_fst).continuousOn.smul
        (hd.comp continuousOn_snd (fun _ hz => hz.2)))
  have hcenter (s : ℝ) (_hs : s ∈ K) : F (s, p) ∈ G.gaugeCover.spatial j := by
    simpa only [F, hdp, smul_zero, add_zero] using (lift (f (s, p))).2.property
  obtain ⟨N, hN, hpN, hNU, hshift⟩ := exists_open_parameter_tube hK hU hF
    (G.gaugeCover.spatial j).isOpen hp hcenter
  exact ⟨N, hN, hpN, hNU, fun z hz hs => hshift z.1 ⟨hz.1, hs⟩ z.2 hz.2⟩

end PoincareConjecture.M14
