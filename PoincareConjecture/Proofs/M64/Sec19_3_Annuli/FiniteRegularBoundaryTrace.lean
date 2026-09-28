import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteC2BoundaryReference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m64C2ShrinkingCurve_exists_regular_trace_with_curvature
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (sigma : M64PeriodicDegreeOneLift) (hsigma : ContDiff ℝ 1 sigma.map) :
    ∃ (d : ℝ → M) (L : M64PeriodicDegreeOneLift),
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ d ∧ Function.Periodic d curvePeriod ∧
      (∀ x, curveVelocity (n := n) d x ≠ 0) ∧ ContDiff ℝ 1 L.map ∧
      (∀ x, d (L.map x) = c (sigma.map x) t) ∧
      ∀ x, ((F.metric t).tangentNorm (d (L.map x))
          (curveVelocity (n := n) d (L.map x)))⁻¹ •
        rampHorizontalCovariantDerivative (F.connection t) d
          (fun y => ((F.metric t).tangentNorm (d y) (curveVelocity (n := n) d y))⁻¹ •
            curveVelocity (n := n) d y) (L.map x) =
          m62CurvatureVector F c t (sigma.map x) := by
  classical
  let : Nonempty M := ⟨c 0 t⟩
  have hi := M63.c2ShrinkingCurve_intrinsic_regularity F isCompact_univ
    (ht.1.trans ht.2) le_rfl (Or.inl rfl) hc
  let tau := (a + t) / 2
  let s := (t + b) / 2
  have hat : a < tau := by dsimp only [tau]; linarith [ht.1]
  have htt : tau < t := by dsimp only [tau]; linarith [ht.1]
  have hts : t < s := by dsimp only [s]; linarith [ht.2]
  have hsb : s < b := by dsimp only [s]; linarith [ht.2]
  have hslab : Icc tau s ⊆ Icc a b := Icc_subset_Icc hat.le hsb.le
  have ht' : t ∈ Icc tau s := ⟨htt.le, hts.le⟩
  obtain ⟨phi, d, hphi, -, hpos, hshift, hd, hds, hrel⟩ :=
    M63.exists_fixed_smooth_relabeling F isCompact_univ hc hi hat (htt.trans hts) hslab
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by norm_num)
  obtain ⟨H, hH⟩ := m64DegreeOneLift_of_contDiff hphi1
    (strictMono_of_deriv_pos hpos).monotone hshift
  let L := H.comp sigma
  have hLC1 : ContDiff ℝ 1 L.map := by
    change ContDiff ℝ 1 (H.map ∘ sigma.map)
    rw [hH]
    exact hphi1.comp hsigma
  have hcurv (x : ℝ) : m62CurvatureVector F d t (phi x) =
      m62CurvatureVector F c t x := by
    have hdt : t ∈ interior (Icc tau s) := by
      simpa only [interior_Icc] using (show t ∈ Ioo tau s from ⟨htt, hts⟩)
    have hct : t ∈ interior (Icc a b) := by simpa only [interior_Icc] using ht
    rw [← hd.1.equation t hdt (phi x), ← hc.equation t hct x]
    have heq : (fun z => d (phi x) z) =ᶠ[𝓝 t] fun z => c x z := by
      filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo tau s from ⟨htt, hts⟩)] with z hz
      exact (hrel z (Ioo_subset_Icc_self hz) x).symm
    exact congrArg (fun T : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => T 1)
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n))
  refine ⟨fun x => d x t, L, hds t ht', hd.1.periodic t ht',
    hd.1.immersed t ht', hLC1, ?_, ?_⟩
  · intro x
    change d (H.map (sigma.map x)) t = _
    rw [hH]
    exact (hrel t ht' (sigma.map x)).symm
  · intro x
    change m62CurvatureVector F d t (H.map (sigma.map x)) = _
    rw [hH]
    exact hcurv (sigma.map x)

theorem m64C2ShrinkingCurve_exists_regular_trace
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (sigma : M64PeriodicDegreeOneLift) (hsigma : ContDiff ℝ 1 sigma.map) :
    ∃ (d : ℝ → M) (L : M64PeriodicDegreeOneLift),
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ d ∧ Function.Periodic d curvePeriod ∧
      (∀ x, curveVelocity (n := n) d x ≠ 0) ∧ ContDiff ℝ 1 L.map ∧
      ∀ x, d (L.map x) = c (sigma.map x) t := by
  obtain ⟨d, L, hd, hperiod, hv, hL, htrace, -⟩ :=
    m64C2ShrinkingCurve_exists_regular_trace_with_curvature F hc ht sigma hsigma
  exact ⟨d, L, hd, hperiod, hv, hL, htrace⟩

end PoincareConjecture
