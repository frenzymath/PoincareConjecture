import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetHalfDiskProjection
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryParity
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Sqrt











set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

variable {n : ℕ}




def normalizedResidualFrame
    (G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (q : Fin n → ℂ) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  let a := residualRealColumn q
  let b := residualImagColumn q
  let s := (Real.sqrt (G a a))⁻¹
  (s • a, s • b)

private theorem contDiffOn_normalizedResidualFrame :
    ContDiffOn ℝ ∞
      (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) × (Fin n → ℂ) =>
          normalizedResidualFrame p.1 p.2)
      {p | 0 < p.1 (residualRealColumn p.2) (residualRealColumn p.2)} := by
  let V := {p : (EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) × (Fin n → ℂ) |
      0 < p.1 (residualRealColumn p.2) (residualRealColumn p.2)}
  have ha : ContDiff ℝ ∞ (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) × (Fin n → ℂ) => residualRealColumn p.2) :=
    residualRealColumn.contDiff.comp contDiff_snd
  have hb : ContDiff ℝ ∞ (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) × (Fin n → ℂ) => residualImagColumn p.2) :=
    residualImagColumn.contDiff.comp contDiff_snd
  have hs : ContDiffOn ℝ ∞
      (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) × (Fin n → ℂ) =>
          (Real.sqrt (p.1 (residualRealColumn p.2) (residualRealColumn p.2)))⁻¹) V :=
    (((contDiff_fst.clm_apply ha).clm_apply ha).contDiffOn.sqrt
      (fun _ h => ne_of_gt h)).inv (fun _ h => (Real.sqrt_pos.mpr h).ne')
  exact (hs.smul ha.contDiffOn).prodMk (hs.smul hb.contDiffOn)




theorem normalizedResidualFrame_orthonormal
    (G : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (q : Fin n → ℂ)
    (hpos : 0 < G (residualRealColumn q) (residualRealColumn q))
    (hcross : G (residualRealColumn q) (residualImagColumn q) = 0)
    (hdiag : G (residualImagColumn q) (residualImagColumn q) =
      G (residualRealColumn q) (residualRealColumn q)) :
    let F := normalizedResidualFrame G q
    G F.1 F.1 = 1 ∧ G F.1 F.2 = 0 ∧ G F.2 F.2 = 1 := by
  let rho := G (residualRealColumn q) (residualRealColumn q)
  have hs : Real.sqrt rho ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hscale : (Real.sqrt rho)⁻¹ * ((Real.sqrt rho)⁻¹ * rho) = 1 := by
    field_simp
    exact (Real.sq_sqrt hpos.le).symm
  simpa only [normalizedResidualFrame, map_smul, smul_apply, smul_eq_mul,
    hcross, hdiag, mul_zero, rho] using
      And.intro hscale (And.intro (show (0 : ℝ) = 0 from rfl) hscale)

private theorem compact_comp_sqrt_holder
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℂ → E} {H : E → F} {K : Set ℂ} {V : Set E}
    (hK : IsCompact K) (hq : ContinuousOn q K) (hV : IsOpen V)
    (hqV : MapsTo q K V) (hH : ContDiffOn ℝ 1 H V)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z ∈ K, ∀ w ∈ K, ‖q z - q w‖ ≤ C * Real.sqrt ‖z - w‖) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ K, ∀ w ∈ K,
      ‖H (q z) - H (q w)‖ ≤ D * Real.sqrt ‖z - w‖ := by
  have hloc : LocallyLipschitzOn (q '' K) H := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨L, T, hT, hL⟩ :=
      (hH.contDiffAt (hV.mem_nhds (hqV hz))).exists_lipschitzOnWith
    exact ⟨L, T, mem_nhdsWithin_of_mem_nhds hT, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact (hK.image_of_continuousOn hq)
  refine ⟨L * C, mul_nonneg L.coe_nonneg hC, ?_⟩
  intro z hz w hw
  calc
    ‖H (q z) - H (q w)‖ ≤ L * ‖q z - q w‖ := by
      simpa only [dist_eq_norm] using
        hL.dist_le_mul (q z) (mem_image_of_mem q hz) (q w) (mem_image_of_mem q hw)
    _ ≤ L * (C * Real.sqrt ‖z - w‖) :=
      mul_le_mul_of_nonneg_left (hb z hz w hw) L.coe_nonneg
    _ = _ := by ring

set_option maxHeartbeats 1800000 in






theorem halfDisk_normalizedResidualFrame {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ}
    {r : ℝ} (hr : 0 < r) (m : ℕ)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hQ : ContinuousOn Q (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hQ1 : ContDiffOn ℝ 1 Q (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hQne : ∀ z ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}, Q z ≠ 0)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im},
      M65StrictTrace.halfDiskGradient H r z = z ^ m • Q z)
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T I) (T I) ∧
        g.inner (H z) (T 1) (T I) = 0)
    (hDQ1 : MemLp (fun z => fderiv ℝ Q z 1)
      2 (volume.restrict (ball (0 : ℂ) r ∩ {z | 0 < z.im})))
    (hDQI : MemLp (fun z => fderiv ℝ Q z I)
      2 (volume.restrict (ball (0 : ℂ) r ∩ {z | 0 < z.im})))
    {C : ℝ} (hC : 0 ≤ C)
    (hholder : ∀ z ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im},
      ∀ w ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im},
        ‖Q z - Q w‖ ≤ C * Real.sqrt ‖z - w‖) :
    let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
    let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
    let F := fun z => normalizedResidualFrame (g.euclideanCoefficients (H z)) (Q z)
    ContinuousOn F K ∧ ContDiffOn ℝ 1 F W ∧
      (∀ z ∈ K, g.inner (H z) (F z).1 (F z).1 = 1 ∧
        g.inner (H z) (F z).1 (F z).2 = 0 ∧
        g.inner (H z) (F z).2 (F z).2 = 1) ∧
      MemLp (fun z => fderiv ℝ F z 1) 2 (volume.restrict W) ∧
      MemLp (fun z => fderiv ℝ F z I) 2 (volume.restrict W) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ K, ∀ w ∈ K,
        ‖F z - F w‖ ≤ D * Real.sqrt ‖z - w‖ := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  let G := fun z => g.euclideanCoefficients (H z)
  let a := fun z => residualRealColumn (Q z)
  let b := fun z => residualImagColumn (Q z)
  let F := fun z => normalizedResidualFrame (G z) (Q z)
  obtain ⟨hW, _hKclosed, hKun, hclosure⟩ := M65StrictTrace.halfDisk_differential_domain hr
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) r).inter_right
    (isClosed_le continuous_const continuous_im)
  have hWK : W ⊆ K := fun z hz => ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hKW : K ⊆ closure W := by rw [hclosure]
  have hKconv : Convex ℝ K := (convex_closedBall (0 : ℂ) r).inter
    ((convex_Ici (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hG : ContDiffOn ℝ 1 G K :=
    ((contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).of_le
      (by simp)).comp_contDiffOn hH
  have ha : ContinuousOn a K := residualRealColumn.continuous.comp_continuousOn hQ
  have hb : ContinuousOn b K := residualImagColumn.continuous.comp_continuousOn hQ
  have hconfW (z : ℂ) (hz : z ∈ W) : G z (a z) (b z) = 0 ∧
      G z (b z) (b z) = G z (a z) (a z) := by
    have hf := hfactor z (hWK hz)
    have hc := hconf z (hWK hz)
    have hn := M65StrictTrace.halfDisk_mem_nhds hz
    simp only [M65StrictTrace.halfDiskGradient, fderivWithin_of_mem_nhds hn] at hf
    change complexGradient H z = z ^ m • Q z at hf
    dsimp only at hc
    rw [fderivWithin_of_mem_nhds hn] at hc
    change G z (fderiv ℝ H z 1) (fderiv ℝ H z 1) =
        G z (fderiv ℝ H z I) (fderiv ℝ H z I) ∧
      G z (fderiv ℝ H z 1) (fderiv ℝ H z I) = 0 at hc
    obtain ⟨he1, heI⟩ := residual_columns_complexGradient H z
    rw [hf] at he1 heI
    have hzne : z ≠ 0 := by
      intro he
      have hi : 0 < z.im := hz.2
      simp only [he, zero_im, lt_self_iff_false] at hi
    exact residual_columns_conformal_of_smul (G z) (fun v w => g.symm (H z) v w)
      (pow_ne_zero m hzne) (Q z) (by simpa only [he1, heI] using hc.2)
      (by simpa only [he1, heI] using hc.1.symm)
  have hcross : EqOn (fun z => G z (a z) (b z)) (fun _ => 0) K :=
    (show EqOn (fun z => G z (a z) (b z)) (fun _ => 0) W from
      fun z hz => (hconfW z hz).1).of_subset_closure
        ((hG.continuousOn.clm_apply ha).clm_apply hb) continuousOn_const hWK hKW
  have hdiag : EqOn (fun z => G z (b z) (b z)) (fun z => G z (a z) (a z)) K :=
    (show EqOn (fun z => G z (b z) (b z)) (fun z => G z (a z) (a z)) W from
      fun z hz => (hconfW z hz).2).of_subset_closure
        ((hG.continuousOn.clm_apply hb).clm_apply hb)
        ((hG.continuousOn.clm_apply ha).clm_apply ha) hWK hKW
  have hpos (z : ℂ) (hz : z ∈ K) : 0 < G z (a z) (a z) :=
    residual_columns_factor_pos (G z) (g.pos (H z)) (hQne z hz) (hdiag hz)
  let E := (EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) × (Fin n → ℂ)
  let : NormedAddCommGroup E := inferInstance
  let : NormedSpace ℝ E := inferInstance
  let q : ℂ → E := fun z => (G z, Q z)
  let V : Set E := {p | 0 < p.1 (residualRealColumn p.2) (residualRealColumn p.2)}
  let N : E → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun p => normalizedResidualFrame p.1 p.2
  have hV : IsOpen V := isOpen_lt continuous_const
    ((continuous_fst.clm_apply (residualRealColumn.continuous.comp continuous_snd)).clm_apply
      (residualRealColumn.continuous.comp continuous_snd))
  have hq : ContinuousOn q K := hG.continuousOn.prodMk hQ
  have hq1 : ContDiffOn ℝ 1 q W := (hG.mono hWK).prodMk hQ1
  have hqV : MapsTo q K V := fun z hz => hpos z hz
  have hN : ContDiffOn ℝ 1 N V := contDiffOn_normalizedResidualFrame.of_le (by simp)
  have hpart (v : ℂ) (hv : v = 1 ∨ v = I) :
      MemLp (fun z => fderiv ℝ F z v) 2 (volume.restrict W) := by
    have hdG := compact_within_derivative_memLp hK hKun hW hWK hG v
    rw [inter_eq_right.mpr hWK] at hdG
    have hdQ : MemLp (fun z => fderiv ℝ Q z v) 2 (volume.restrict W) :=
      hv.elim (fun h => h ▸ hDQ1) (fun h => h ▸ hDQI)
    have hdq : MemLp (fun z => fderiv ℝ q z v) 2 (volume.restrict (K ∩ W)) := by
      rw [inter_eq_right.mpr hWK]
      have hraw : MemLp (fun z => (fderiv ℝ G z v, fderiv ℝ Q z v))
          2 (volume.restrict W) := memLp_prod_iff.mpr ⟨hdG, hdQ⟩
      apply hraw.ae_eq
      filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
      have hh := ((hG.mono hWK).contDiffAt (hW.mem_nhds hz)).differentiableAt one_ne_zero
      have hqz := (hQ1.contDiffAt (hW.mem_nhds hz)).differentiableAt one_ne_zero
      exact (congrArg (fun L : ℂ →L[ℝ] E => L v)
        (hh.hasFDerivAt.prodMk hqz.hasFDerivAt).fderiv).symm
    have hh := actual_comp_derivative_memLp hK hW hV hq hq1 hqV hN v hdq
    change MemLp (fun z => fderiv ℝ F z v) 2 (volume.restrict (K ∩ W)) at hh
    rwa [inter_eq_right.mpr hWK] at hh
  refine ⟨hN.continuousOn.comp hq hqV, hN.comp hq1 (hqV.mono hWK Subset.rfl),
    (fun z hz => normalizedResidualFrame_orthonormal (G z) (Q z)
      (hpos z hz) (hcross hz) (hdiag hz)), hpart 1 (Or.inl rfl), hpart I (Or.inr rfl), ?_⟩
  obtain ⟨L, hL⟩ := hG.exists_lipschitzOnWith one_ne_zero hKconv hK
  have hqholder : ∀ z ∈ K, ∀ w ∈ K,
      ‖q z - q w‖ ≤ (L * Real.sqrt (2 * r) + C) * Real.sqrt ‖z - w‖ := by
    intro z hz w hw
    have hd : ‖z - w‖ ≤ 2 * r := by
      have hh := norm_sub_le z w
      have hz' := mem_closedBall_zero_iff.mp hz.1
      have hw' := mem_closedBall_zero_iff.mp hw.1
      linarith
    have hds : ‖z - w‖ ≤ Real.sqrt (2 * r) * Real.sqrt ‖z - w‖ := by
      calc
        _ = Real.sqrt ‖z - w‖ * Real.sqrt ‖z - w‖ := (Real.mul_self_sqrt (norm_nonneg _)).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hd) (Real.sqrt_nonneg _)
    have hGb : ‖G z - G w‖ ≤ L * ‖z - w‖ := by
      simpa only [dist_eq_norm] using hL.dist_le_mul z hz w hw
    change max ‖G z - G w‖ ‖Q z - Q w‖ ≤ _
    apply max_le
    · calc
        _ ≤ L * ‖z - w‖ := hGb
        _ ≤ L * (Real.sqrt (2 * r) * Real.sqrt ‖z - w‖) :=
          mul_le_mul_of_nonneg_left hds L.coe_nonneg
        _ ≤ _ := by nlinarith [Real.sqrt_nonneg ‖z - w‖]
    · calc
        _ ≤ C * Real.sqrt ‖z - w‖ := hholder z hz w hw
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (mul_nonneg L.coe_nonneg (Real.sqrt_nonneg _)))
          (Real.sqrt_nonneg _)
  exact compact_comp_sqrt_holder hK hq hV hqV hN
    (by positivity : 0 ≤ (L : ℝ) * Real.sqrt (2 * r) + C) hqholder

end PoincareConjecture.M65Branch

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace
open scoped Manifold

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

set_option maxHeartbeats 1200000 in





theorem boundary_branch_frame (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let p := e.symm x
    let chart := chartAt LoopAmbient (S.disk.map x)
    let P := e ∘ boundaryCoordinate p
    let H := chart ∘ S.disk.map ∘ P
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE)
      (r : ℝ) (m : ℕ) (Q : ℂ → Fin 3 → ℂ), 0 < r ∧ Even m ∧
      let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
      let F := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
      MapsTo P K loopDiskSet ∧ MapsTo (S.disk.map ∘ P) K chart.source ∧
      ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (chart.symm y)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y b)) ∧
      (∀ z ∈ K, ∀ v : ℂ,
        gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
          diskConformalFactor g S.disk.map (P z) *
            ‖Complex.I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2) ∧
      (∀ z ∈ W, dbar (complexGradient H) z =
        harmonicMatrix DE H z (complexGradient H z)) ∧
      ContinuousOn Q K ∧ ContDiffOn ℝ 1 Q W ∧
      (∀ z ∈ K, Q z ≠ 0) ∧
      (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) ∧
      ContinuousOn F K ∧ ContDiffOn ℝ 1 F W ∧
      (∀ z ∈ K, gE.inner (H z) (F z).1 (F z).1 = 1 ∧
        gE.inner (H z) (F z).1 (F z).2 = 0 ∧
        gE.inner (H z) (F z).2 (F z).2 = 1) ∧
      MemLp (fun z => fderiv ℝ F z 1) 2 (volume.restrict W) ∧
      MemLp (fun z => fderiv ℝ F z I) 2 (volume.restrict W) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ w ∈ K,
        ‖F z - F w‖ ≤ C * Real.sqrt ‖z - w‖ := by
  obtain ⟨gE, DE, r, m, Q, hr, hm, hP, hsrc, hH, hHi, hg, hn, heq,
      hQc, hQi, hQne, hf, h1, hI, C, hC, hholder⟩ :=
    S.boundary_branch_residual_even_holder hinj hsmooth hregular hx
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let P := e ∘ boundaryCoordinate (e.symm x)
  let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ P
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  have hconf (z : ℂ) (hz : z ∈ K) :
      let T := fderivWithin ℝ H K z
      gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
        gE.inner (H z) (T 1) (T I) = 0 := by
    let T := fderivWithin ℝ H K z
    have hn1 := hn z hz 1
    have hnI := hn z hz I
    have hsum := hn z hz (1 + I)
    have hnorm : ‖(1 : ℂ) + I‖ ^ 2 = 2 := by
      norm_num [Complex.sq_norm, Complex.normSq_apply]
    simp only [norm_one, norm_I, one_pow, mul_one] at hn1 hnI
    rw [hnorm, map_add] at hsum
    change gE.inner (H z) (T 1 + T I) (T 1 + T I) = _ at hsum
    simp only [map_add, add_apply] at hsum
    rw [gE.symm (H z) (T I) (T 1)] at hsum
    exact ⟨hn1.trans hnI.symm, by linarith⟩
  obtain ⟨hFc, hFi, hForth, hF1, hFI, hFholder⟩ :=
    halfDisk_normalizedResidualFrame gE hr m hH hQc hQi hQne hf hconf h1 hI hC hholder
  exact ⟨gE, DE, r, m, Q, hr, hm, hP, hsrc, hH, hHi, hg, hn, heq,
    hQc, hQi, hQne, hf, hFc, hFi, hForth, hF1, hFI, hFholder⟩

end PoincareConjecture.M65MinimalDisk
