import PoincareConjecture.Proofs.M64.Mathlib.MonotonePeriodicLipschitz
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryLiftAlgebra
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ArbitraryC2IntrinsicRegularity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedRelabelingAssembly
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry
import Mathlib.Analysis.Calculus.ContDiff.RCLike





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture





theorem m64DegreeOneLift_of_contDiff {phi : ℝ → ℝ} (hphi : ContDiff ℝ 1 phi)
    (hm : Monotone phi)
    (hshift : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod) :
    ∃ L : M64PeriodicDegreeOneLift, L.map = phi := by
  obtain ⟨K, hK⟩ := hphi.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (0 : ℝ) curvePeriod) isCompact_Icc
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hglobal := m64Monotone_lipschitz_of_periodic_interval hP hm hshift hK
  refine ⟨⟨phi, hm, hshift, K, K.coe_nonneg, ?_⟩, rfl⟩
  intro x y
  simpa only [Real.dist_eq] using hglobal.dist_le_mul x y

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}






theorem m64C2ShrinkingCurve_exists_finite_reference
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (sigma : M64PeriodicDegreeOneLift) (hsigma : ContDiff ℝ 1 sigma.map) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (∀ z ∈ Ioo (-epsilon) epsilon, t + z ∈ Ioo a b) ∧
      ∃ L : M64PeriodicDegreeOneLift, ContDiff ℝ 1 L.map ∧
        ∃ f : ℝ → ℝ → M,
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (Function.uncurry f)
            (Ioo (-epsilon) epsilon ×ˢ univ) ∧
          (∀ z, Function.Periodic (f z) curvePeriod) ∧
          (∀ z ∈ Ioo (-epsilon) epsilon, ∀ x, f z (L.map x) = c (sigma.map x) (t + z)) ∧
          ∀ x, curveVelocity (n := n) (fun z => f z (L.map x)) 0 =
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
  obtain ⟨phi, d, hphi, -, hpos, hshift, hd, -, hrel⟩ :=
    M63.exists_fixed_smooth_relabeling F isCompact_univ hc hi hat (htt.trans hts) hslab
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by norm_num)
  obtain ⟨H, hH⟩ := m64DegreeOneLift_of_contDiff hphi1
    (strictMono_of_deriv_pos hpos).monotone hshift
  let L := H.comp sigma
  have hL (x : ℝ) : L.map x = phi (sigma.map x) := by
    change H.map (sigma.map x) = _
    rw [hH]
  have hLC1 : ContDiff ℝ 1 L.map := by
    change ContDiff ℝ 1 (H.map ∘ sigma.map)
    rw [hH]
    exact hphi1.comp hsigma
  let epsilon := min (t - tau) (s - t) / 2
  have hepsilon : 0 < epsilon := half_pos (lt_min (sub_pos.mpr htt) (sub_pos.mpr hts))
  have htime (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) : t + z ∈ Ioo tau s := by
    dsimp only [epsilon] at hz
    constructor <;> linarith [min_le_left (t - tau) (s - t),
      min_le_right (t - tau) (s - t), hz.1, hz.2]
  have hfull (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) : t + z ∈ Ioo a b :=
    ⟨hat.trans (htime z hz).1, (htime z hz).2.trans hsb⟩
  let f : ℝ → ℝ → M := fun z x => d x (if t + z ∈ Icc tau s then t + z else t)
  have hfnear (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) (x : ℝ) : f z x = d x (t + z) := by
    simp only [f, if_pos (Ioo_subset_Icc_self (htime z hz))]
  have hdlocal : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => d q.1 q.2) (univ ×ˢ Ioo tau s) := by
    simpa only [interior_Icc] using hd.2
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (Function.uncurry f)
      (Ioo (-epsilon) epsilon ×ˢ univ) :=
    (hdlocal.comp (contDiff_snd.prodMk (contDiff_const.add contDiff_fst)).contMDiff.contMDiffOn
      (fun q hq => ⟨mem_univ _, htime q.1 hq.1⟩)).congr
        (fun q hq => hfnear q.1 hq.1 q.2)
  have hperiod (z : ℝ) : Function.Periodic (f z) curvePeriod := by
    intro x
    unfold f
    split_ifs with hz
    · exact hd.1.periodic _ hz x
    · exact hd.1.periodic t ⟨htt.le, hts.le⟩ x
  have hagree (z : ℝ) (hz : z ∈ Ioo (-epsilon) epsilon) (x : ℝ) :
      f z (L.map x) = c (sigma.map x) (t + z) := by
    rw [hfnear z hz, hL]
    exact (hrel (t + z) (Ioo_subset_Icc_self (htime z hz)) (sigma.map x)).symm
  refine ⟨epsilon, hepsilon, hfull, L, hLC1, f, hf, hperiod, hagree, ?_⟩
  intro x
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have heq : (fun z => f z (L.map x)) =ᶠ[𝓝 (0 : ℝ)]
      fun z => c (sigma.map x) (t + z) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with z hz
    exact hagree z hz x
  have hvelocity : curveVelocity (n := n) (fun z => f z (L.map x)) 0 =
      curveVelocity (n := n) (fun z => c (sigma.map x) (t + z)) 0 :=
    congrArg (fun D : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => D 1)
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n))
  have hcjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1
      (fun q : ℝ × ℝ => c q.1 q.2) (univ ×ˢ Ioo a b) := by
    simpa only [interior_Icc] using hc.joint_c1
  have hct : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun z => c (sigma.map x) z) t :=
    (hcjoint.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      ⟨mem_univ _, ht⟩)).comp t
        ((contDiffAt_const (c := sigma.map x)).prodMk contDiffAt_id).contMDiffAt
  have hchain := M63.curveVelocity_comp (gamma := fun z => c (sigma.map x) z)
    (phi := fun z => t + z)
    (by simpa only [add_zero] using hct.mdifferentiableAt one_ne_zero)
    ((hasDerivAt_id (0 : ℝ)).const_add t)
  have hchain' : curveVelocity (n := n) (fun z => c (sigma.map x) (t + z)) 0 =
      curveVelocity (n := n) (fun z => c (sigma.map x) z) (t + 0) := by
    simpa only [one_smul] using hchain
  have ht0 := congrArg (fun z : ℝ =>
    (curveVelocity (n := n) (fun z => c (sigma.map x) z) z : EuclideanSpace ℝ (Fin n)))
      (add_zero t)
  exact hvelocity.trans (hchain'.trans
    (ht0.trans (hc.equation t (by simpa only [interior_Icc] using ht) (sigma.map x))))

end PoincareConjecture
