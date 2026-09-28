import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryMotion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryTransport
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusBoundaryRegularity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusFamily














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}






theorem m64FreeAnnulus_exists_c2_moving_family_with_literal_competitors
    (F : RicciFlow n M (Icc a b)) {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (F.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ U : Set LoopPlane, IsOpen U ∧
      m64AnnulusDomain ⊆ U ∧ ∃ v : ℝ × LoopPlane → M,
      ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
        (Ioo (-delta) delta ×ˢ U) ∧
      (∀ p, v (0, p) = A.map p) ∧
      (∀ z x s, v (z, annulusPoint (x + curvePeriod) s) =
        v (z, annulusPoint x s)) ∧
      (∀ h ∈ Ioo (-delta) delta, ∀ x,
        v (h, annulusPoint x 0) = c0 (sigma0.map x) (t + h)) ∧
      (∀ h ∈ Ioo (-delta) delta, ∀ x,
        v (h, annulusPoint x 1) = c1 (sigma1.map x) (t + h)) ∧
      (∀ x, curveVelocity (fun z => v (z, annulusPoint x 0)) 0 =
        m62CurvatureVector F c0 t (sigma0.map x)) ∧
      (∀ x, curveVelocity (fun z => v (z, annulusPoint x 1)) 0 =
        m62CurvatureVector F c1 t (sigma1.map x)) ∧
      ∀ h ∈ Ioo (-delta) delta,
        ∃ B : M64Annulus (F.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
          B.area = m64AnnulusArea (F.metric (t + h)) (fun p => v (h, p)) := by
  have hct0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c0 (sigma0.map x) t) := by
    simpa only [A.lower_boundary, Function.comp_apply] using
      m64Annulus_slice_contMDiff A hO hdom hA (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
  have hct1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c1 (sigma1.map x) t) := by
    simpa only [A.upper_boundary, Function.comp_apply] using
      m64Annulus_slice_contMDiff A hO hdom hA (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  obtain ⟨epsilon0, hepsilon0, f0, hf0, hp0, ha0, hv0⟩ :=
    m64C2ShrinkingCurve_exists_free_centered_motion F hc0 ht
      (m64PeriodicDegreeOneLift_continuous_map sigma0) sigma0.period_shift hct0
  obtain ⟨epsilon1, hepsilon1, f1, hf1, hp1, ha1, hv1⟩ :=
    m64C2ShrinkingCurve_exists_free_centered_motion F hc1 ht
      (m64PeriodicDegreeOneLift_continuous_map sigma1) sigma1.period_shift hct1
  let timeRadius := min (t - a) (b - t) / 2
  have htimeRadius : 0 < timeRadius :=
    half_pos (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2))
  let epsilon := min (min epsilon0 epsilon1) timeRadius
  have hepsilon : 0 < epsilon := lt_min (lt_min hepsilon0 hepsilon1) htimeRadius
  have he0 : epsilon ≤ epsilon0 := (min_le_left _ _).trans (min_le_left _ _)
  have he1 : epsilon ≤ epsilon1 := (min_le_left _ _).trans (min_le_right _ _)
  have hsub0 : Ioo (-epsilon) epsilon ⊆ Ioo (-epsilon0) epsilon0 :=
    Ioo_subset_Ioo (neg_le_neg he0) he0
  have hsub1 : Ioo (-epsilon) epsilon ⊆ Ioo (-epsilon1) epsilon1 :=
    Ioo_subset_Ioo (neg_le_neg he1) he1
  have htime (h : ℝ) (hh : h ∈ Ioo (-epsilon) epsilon) : t + h ∈ Icc a b := by
    have hleft := min_le_left (t - a) (b - t)
    have hright := min_le_right (t - a) (b - t)
    have he : epsilon ≤ timeRadius := min_le_right _ _
    dsimp only [timeRadius] at he
    constructor <;> linarith [ht.1, ht.2, hh.1, hh.2]
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hinit0 (x : ℝ) : f0 0 x = c0 (sigma0.map x) t := by
    simpa only [add_zero] using ha0 0 (hsub0 hzero) x
  have hinit1 (x : ℝ) : f1 0 x = c1 (sigma1.map x) t := by
    simpa only [add_zero] using ha1 0 (hsub1 hzero) x
  obtain ⟨delta, hdelta, U, hU, hDU, v, hv, hbase, hperiodic, hlo, hup, hadmit⟩ :=
    m64Annulus_exists_smooth_moving_boundary_family A hO hdom hA hepsilon
      f0 f1 (hf0.mono (prod_mono_left hsub0)) (hf1.mono (prod_mono_left hsub1))
      hinit0 hinit1 hp0 hp1
  let d := min delta epsilon
  have hd : 0 < d := lt_min hdelta hepsilon
  have hdD : Ioo (-d) d ⊆ Ioo (-delta) delta :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hdE : Ioo (-d) d ⊆ Ioo (-epsilon) epsilon :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  refine ⟨d, hd, U, hU, hDU, v, hv.mono (prod_mono_left hdD), hbase, hperiodic,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh x
    exact (hlo h x).trans (ha0 h (hsub0 (hdE hh)) x)
  · intro h hh x
    exact (hup h x).trans (ha1 h (hsub1 (hdE hh)) x)
  · intro x
    exact (congrArg (fun f : ℝ → M => curveVelocity (n := n) f 0)
      (funext (fun z => hlo z x))).trans (hv0 x)
  · intro x
    exact (congrArg (fun f : ℝ → M => curveVelocity (n := n) f 0)
      (funext (fun z => hup z x))).trans (hv1 x)
  · intro h hh
    obtain ⟨C, hC⟩ := hadmit h (hdD hh) (F.metric (t + h))
    have heq0 : f0 h = (fun x => c0 x (t + h)) ∘ sigma0.map :=
      funext (ha0 h (hsub0 (hdE hh)))
    have heq1 : f1 h = (fun x => c1 x (t + h)) ∘ sigma1.map :=
      funext (ha1 h (hsub1 (hdE hh)))
    have hfree : ∃ C' : M64Annulus (F.metric (t + h))
        ((fun x => c0 x (t + h)) ∘ sigma0.map)
        ((fun x => c1 x (t + h)) ∘ sigma1.map),
        C'.map = fun p => v (h, p) := heq0 ▸ heq1 ▸ ⟨C, hC⟩
    obtain ⟨C', hC'⟩ := hfree
    obtain ⟨B, hB⟩ := m64C2ShrinkingCurves_freeBoundaryAreaTransport F hc0 hc1
      (htime h (hdE hh)) sigma0 sigma1 C'
    refine ⟨B, hB.trans ?_⟩
    change m64AnnulusArea (F.metric (t + h)) C'.map = _
    rw [hC']

end PoincareConjecture
