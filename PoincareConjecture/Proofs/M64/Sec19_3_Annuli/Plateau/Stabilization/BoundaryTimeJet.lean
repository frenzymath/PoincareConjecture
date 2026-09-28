import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.UniformTimeJet
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.CompactRetractionMetric












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem uniform_boundary_time_jet_bound
    (g : RiemannianMetric n M) {f beta : ℝ × ℝ → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1 f (Ioo (-epsilon) epsilon ×ˢ univ))
    (hbeta : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1 beta
      (Ioo (-epsilon) epsilon ×ˢ univ))
    {K : Set ℝ} (hK : IsCompact K)
    (hbase : ∀ x ∈ K, f (0, x) = beta (0, x))
    (hvelocity : ∀ x ∈ K,
      curveVelocity (n := n) (fun s => f (s, x)) 0 =
        curveVelocity (n := n) (fun s => beta (s, x)) 0)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ h ∈ Ioo (-delta) delta,
      ∀ x ∈ K, g.edist (f (h, x)) (beta (h, x)) ≤ ENNReal.ofReal (eta * |h|) := by
  let : Nonempty M := ⟨f (0, 0)⟩
  obtain ⟨d, e, he, hemb, hinj⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨O, rho, hO, heO, hrho, hrhoe, -, -⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  obtain ⟨C, hC, V, hV, hdiag, hmetric⟩ := compact_metric_control_near_diagonal g
    (isCompact_range he.continuous) hO heO (hrho.of_le (m := 1) (by simp))
  let U : Set (ℝ × ℝ) := Ioo (-epsilon) epsilon ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  let F : ℝ × ℝ → EuclideanSpace ℝ (Fin d) := e ∘ f
  let B : ℝ × ℝ → EuclideanSpace ℝ (Fin d) := e ∘ beta
  have hF : ContDiffOn ℝ 1 F U :=
    ((he.of_le (m := 1) (by simp)).comp_contMDiffOn hf).contDiffOn
  have hB : ContDiffOn ℝ 1 B U :=
    ((he.of_le (m := 1) (by simp)).comp_contMDiffOn hbeta).contDiffOn
  let pair : ℝ × ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
    fun q => (F q, B q)
  have hpair : ContinuousOn pair U := hF.continuousOn.prodMk hB.continuousOn
  have hW : IsOpen (U ∩ pair ⁻¹' V) := hpair.isOpen_inter_preimage hU hV
  have hzeroW : ({0} : Set ℝ) ×ˢ K ⊆ U ∩ pair ⁻¹' V := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    rcases mem_singleton_iff.mp hs with rfl
    refine ⟨⟨hzero, mem_univ _⟩, ?_⟩
    change (e (f (0, x)), e (beta (0, x))) ∈ V
    rw [hbase x hx]
    exact hdiag _ (mem_range_self _)
  obtain ⟨J, L, hJ, -, h0J, hKL, hJL⟩ :=
    generalized_tube_lemma isCompact_singleton hK hW hzeroW
  obtain ⟨delta0, hdelta0, hball⟩ := Metric.mem_nhds_iff.mp
    (hJ.mem_nhds (h0J (mem_singleton 0)))
  have hsmall0 : Ioo (-delta0) delta0 ⊆ J := by
    intro h hh
    exact hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hh)
  have hderiv (x : ℝ) (hx : x ∈ K) :
      fderiv ℝ (fun q => F q - B q) (0, x) (1, 0) = 0 := by
    have hmem : (0, x) ∈ U := ⟨hzero, mem_univ _⟩
    have hFat := (hF.contDiffAt (hU.mem_nhds hmem)).differentiableAt one_ne_zero
    have hBat := (hB.contDiffAt (hU.mem_nhds hmem)).differentiableAt one_ne_zero
    have hline := (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 x)
    have hFt := hFat.hasFDerivAt.comp_hasDerivAt 0 hline
    have hBt := hBat.hasFDerivAt.comp_hasDerivAt 0 hline
    have hfm := (hf.contMDiffAt (hU.mem_nhds hmem)).mdifferentiableAt one_ne_zero
    have hbm := (hbeta.contMDiffAt (hU.mem_nhds hmem)).mdifferentiableAt one_ne_zero
    have hfl : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => f (s, x)) 0 :=
      hfm.comp 0 hline.differentiableAt.mdifferentiableAt
    have hbl : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => beta (s, x)) 0 :=
      hbm.comp 0 hline.differentiableAt.mdifferentiableAt
    have hfe := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
      (I'' := 𝓡 d) 0 (he.mdifferentiable (by simp) _)
        hfl (1 : ℝ)
    have hbe := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
      (I'' := 𝓡 d) 0 (he.mdifferentiable (by simp) _)
        hbl (1 : ℝ)
    have htime : deriv (fun s => F (s, x)) 0 = deriv (fun s => B (s, x)) 0 := by
      simp +instances only [mfderiv_eq_fderiv,
        Function.comp_def] at hfe hbe
      change fderiv ℝ (fun s => e (f (s, x))) 0 1 =
        fderiv ℝ (fun s => e (beta (s, x))) 0 1
      erw [hfe, hbe]
      change (mfderiv (𝓡 n) (𝓡 d) e (f (0, x)))
        (curveVelocity (fun s => f (s, x)) 0) =
          (mfderiv (𝓡 n) (𝓡 d) e (beta (0, x)))
            (curveVelocity (fun s => beta (s, x)) 0)
      rw [hbase x hx, hvelocity x hx]
    change HasDerivAt (fun s => F (s, x)) (fderiv ℝ F (0, x) (1, 0)) 0 at hFt
    change HasDerivAt (fun s => B (s, x)) (fderiv ℝ B (0, x) (1, 0)) 0 at hBt
    change fderiv ℝ (F - B) (0, x) (1, 0) = 0
    rw [fderiv_sub hFat hBat, sub_apply,
      ← hFt.deriv, ← hBt.deriv, htime, sub_self]
  obtain ⟨delta1, hdelta1, hnorm⟩ := uniform_time_zero_jet_bound hepsilon (hF.sub hB) hK
    (fun x hx => by simp only [F, B, Function.comp_def, hbase x hx, sub_self])
    hderiv (div_pos heta hC)
  refine ⟨min delta0 delta1, lt_min hdelta0 hdelta1, ?_⟩
  intro h hh x hx
  have hh0 : h ∈ Ioo (-delta0) delta0 :=
    ⟨(neg_le_neg (min_le_left _ _)).trans_lt hh.1, hh.2.trans_le (min_le_left _ _)⟩
  have hh1 : h ∈ Ioo (-delta1) delta1 :=
    ⟨(neg_le_neg (min_le_right _ _)).trans_lt hh.1, hh.2.trans_le (min_le_right _ _)⟩
  have hm := hmetric (pair (h, x)) (hJL ⟨hsmall0 hh0, hKL hx⟩).2
  change g.edist (rho (e (f (h, x)))) (rho (e (beta (h, x)))) ≤
    ENNReal.ofReal (C * ‖F (h, x) - B (h, x)‖) at hm
  rw [hrhoe, hrhoe] at hm
  apply hm.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    C * ‖F (h, x) - B (h, x)‖ ≤ C * (eta / C * |h|) :=
      mul_le_mul_of_nonneg_left (hnorm h hh1 x hx) hC.le
    _ = eta * |h| := by field_simp

end PoincareConjecture.M64
