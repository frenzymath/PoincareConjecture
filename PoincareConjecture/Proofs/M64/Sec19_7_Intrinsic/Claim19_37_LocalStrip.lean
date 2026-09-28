import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_UniformMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_local_normal_strip
    (K : ℝ) {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ N : IntrinsicAnnulus, N.GaussianCurvatureBound K →
        ∃ normal : ℝ → AnnulusCoordinates, ContDiff ℝ ∞ normal ∧
          (∀ s, N.metric.inner (intrinsicAnnulusBoundary 1 s) (normal s) (normal s) = 1 ∧
            N.metric.inner (intrinsicAnnulusBoundary 1 s) (normal s)
              (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) s) = 0 ∧
            0 < inner ℝ (intrinsicAnnulusBoundary 1 s) (normal s)) ∧
          ∀ a : ℝ, intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
            ∃ (b epsilon : ℝ) (U : Set ℝ) (u : ℝ × ℝ → AnnulusCoordinates),
              0 < b ∧ b ≤ R ∧ 0 < epsilon ∧ b < epsilon ∧ IsOpen U ∧ a ∈ U ∧
              ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (U ×ˢ Ioo (-epsilon) epsilon) ∧
              (∀ s ∈ U, u (s, 0) = intrinsicAnnulusBoundary 1 s) ∧
              (∀ s ∈ U, curveVelocity (n := 2) (fun t => u (s, t)) 0 = normal s) ∧
              (∀ s ∈ U, N.metric.IsGeodesicOn (fun t => u (s, t))
                (Ioo (-epsilon) epsilon)) ∧
              (∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖u (a, t)‖ ∧ ‖u (a, t)‖ < 2) ∧
              ∀ t ∈ Icc (0 : ℝ) b,
                (∀ v : ℝ × ℝ,
                  (1 - delta) ^ 2 *
                    ((intrinsicBoundarySpeed N.metric 1 a) ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
                    N.metric.inner (u (a, t))
                      (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v)) ∧
                Function.Injective (fderiv ℝ u (a, t)) := by
  obtain ⟨R, hR, hRsmall, hmetric⟩ :=
    m64Intrinsic_exists_uniform_normal_metric_radius K hdelta hdelta1 halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  intro N hK
  obtain ⟨normal, hnormal, hn, hfamily⟩ :=
    m64Intrinsic_exists_local_normal_geodesic_variation N (by norm_num : (1 : ℝ) ≠ 0)
  refine ⟨normal, hnormal, hn, ?_⟩
  intro a hturn
  obtain ⟨U, epsilon, phase, hU, ha, hepsilon, hsmooth, hinit, hgeo, hflow⟩ := hfamily a
  let u : ℝ × ℝ → AnnulusCoordinates := fun p => (phase p).1
  have hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (U ×ˢ Ioo (-epsilon) epsilon) :=
    contMDiffOn_iff_contDiffOn.mpr hsmooth.fst
  have hz : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨neg_neg_iff_pos.mpr hepsilon, hepsilon⟩
  have hboundary (s : ℝ) (hs : s ∈ U) : u (s, 0) = intrinsicAnnulusBoundary 1 s :=
    congrArg Prod.fst (hinit s hs)
  have hvelocity (s : ℝ) (hs : s ∈ U) :
      curveVelocity (n := 2) (fun t => u (s, t)) 0 = normal s := by
    rw [m64Intrinsic_curveVelocity_eq_deriv, (hflow s hs 0 hz).1.deriv]
    exact congrArg Prod.snd (hinit s hs)
  have hderiv : HasDerivAt (fun t => u (a, t)) (normal a) 0 := by
    have h := (hflow a ha 0 hz).1
    rw [show (phase (a, 0)).2 = normal a from congrArg Prod.snd (hinit a ha)] at h
    exact h
  obtain ⟨eta, heta, henter⟩ :=
    m64Intrinsic_inward_curve_enters_annulus (hboundary a ha) hderiv (hn a).2.2
  let b := min R (min (epsilon / 2) (eta / 2))
  have hb : 0 < b := lt_min hR (lt_min (half_pos hepsilon) (half_pos heta))
  have hbR : b ≤ R := min_le_left _ _
  have hbE : b < epsilon :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hepsilon)
  have hbEta : b < eta :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self heta)
  have hsub : Icc (0 : ℝ) b ⊆ Ioo (-epsilon) epsilon := by
    intro t ht
    exact ⟨(neg_neg_iff_pos.mpr hepsilon).trans_le ht.1, ht.2.trans_lt hbE⟩
  have hinside (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) b) :
      1 < ‖u (a, t)‖ ∧ ‖u (a, t)‖ < 2 := henter t ⟨ht.1, ht.2.trans hbEta⟩
  refine ⟨b, epsilon, U, u, hb, hbR, hepsilon, hbE, hU, ha,
    hu, hboundary, hvelocity, hgeo, hinside, ?_⟩
  exact hmetric b hb hbR N 1 (by norm_num) hK u U (Ioo (-epsilon) epsilon)
    hU isOpen_Ioo hsub hu hgeo hboundary normal hnormal
    (fun s => (hn s).1) (fun s => (hn s).2.1) hvelocity a ha hturn
    (fun t ht => ⟨(hinside t ht).1.le, (hinside t ht).2.le⟩)

end PoincareConjecture
