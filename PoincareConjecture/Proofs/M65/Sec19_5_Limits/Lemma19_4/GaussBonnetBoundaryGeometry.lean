import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryFactor
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceBoundaryReality










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65StrictTrace

open M65Branch






theorem halfDisk_Jordan_differential_factor_holder
    {g : RiemannianMetric 3 LoopAmbient} (D : LeviCivitaData g)
    {H : ℂ → LoopAmbient} {r : ℝ} (hr : 0 < r)
    {c : ℝ → LoopAmbient} {I J : Set ℝ} {U : Set LoopAmbient}
    {sigma : LoopAmbient → ℝ} {V : LoopAmbient → LoopAmbient} (j : Fin 3)
    (hI : IsOpen I) (hU : IsOpen U) (hc : ContDiffOn ℝ ∞ c I)
    (hsigma : ContDiffOn ℝ ∞ sigma U) (hV : ContDiffOn ℝ ∞ V U)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hHU : MapsTo H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) U)
    (hparam : ∀ q ∈ U, sigma q ∈ I)
    (hinv : ∀ s ∈ J, sigma (c s) = s)
    (hVeq : ∀ q ∈ U, V q = deriv c (sigma q))
    (hj : ∀ q ∈ U, V q j ≠ 0)
    (harc : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ r → H (s : ℂ) ∈ c '' J)
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T Complex.I) (T Complex.I) ∧
        g.inner (H z) (T 1) (T Complex.I) = 0)
    (heq : ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z))
    (hnot : ¬∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0,
      fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z = 0) :
    ∃ (d : ℝ) (m : ℕ) (q : ℂ → Fin 3 → ℂ), 0 < d ∧ d < r ∧
      ContinuousOn q (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) ∧
      ContDiffOn ℝ 1 q (ball (0 : ℂ) d ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im}, q z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im},
        halfDiskGradient H r z = z ^ m • q z) ∧
      MemLp (fun z => fderiv ℝ q z 1)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      MemLp (fun z => fderiv ℝ q z Complex.I)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
        ∀ w ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
          ‖q z - q w‖ ≤ C * Real.sqrt ‖z - w‖ := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let K2 := closedBall (0 : ℂ) (r / 2) ∩ {z | 0 ≤ z.im}
  let W2 := ball (0 : ℂ) (r / 2) ∩ {z | 0 < z.im}
  have hr2 : 0 < r / 2 := half_pos hr
  have hK2 : K2 ⊆ K :=
    inter_subset_inter (closedBall_subset_closedBall (by linarith)) Subset.rfl
  have hW2 : W2 ⊆ ball (0 : ℂ) r ∩ {z | 0 < z.im} :=
    inter_subset_inter (ball_subset_ball (by linarith)) Subset.rfl
  have hWK : W2 ⊆ K2 := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hder (z : ℂ) (hz : z ∈ K2) :
      fderivWithin ℝ H K2 z = fderivWithin ℝ H K z :=
    fderivWithin_subset hK2 ((halfDisk_differential_domain hr2).2.2.1 z hz)
      ((hH z (hK2 hz)).differentiableWithinAt one_ne_zero)
  have hgrad (z : ℂ) (hz : z ∈ K2) :
      halfDiskGradient H (r / 2) z = halfDiskGradient H r z := by
    change coordinateComplexification (fderivWithin ℝ H K2 z 1) -
        Complex.I • coordinateComplexification (fderivWithin ℝ H K2 z Complex.I) =
      coordinateComplexification (fderivWithin ℝ H K z 1) -
        Complex.I • coordinateComplexification (fderivWithin ℝ H K z Complex.I)
    rw [hder z hz]
  let L := fun q => complexifyOperator (rowFrame (g.inner q) (V q) j)
  let F := halfDiskFramedGradient H L (r / 2)
  let A := halfDiskFramedMatrix D H L (r / 2)
  have hG : ContDiffOn ℝ ∞ g.euclideanCoefficients U :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).contDiffOn
  have hL : ContDiffOn ℝ ∞ L U := complexifyOperator.contDiff.comp_contDiffOn
    (contDiffOn_rowFrame j hG hV hj)
  have hunit (z : ℂ) (hz : z ∈ K2) : IsUnit (L (H z)) :=
    rowFrame_complex_isUnit _ _ j (hj _ (hHU (hK2 hz))) (g.pos _)
  have hH2 := hH.mono hK2
  have hHi2 := hHi.mono hW2
  have hHU2 := hHU.mono hK2 Subset.rfl
  obtain ⟨_hFc, hAc⟩ := halfDiskFramed_fields_continuousOn D hr2 hU hL hH2 hHU2 hunit
  obtain ⟨_hFi, hAi, hFeq⟩ := halfDiskFramed_fields_equation D hU hL hHi2
    (hHU2.mono hWK Subset.rfl) (fun z hz => hunit z (hWK hz))
    (fun z hz => heq z (hW2 hz))
  have hreal (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (r / 2)) (hi : z.im = 0) :
      boundaryReflection j (F z) = F z := by
    have hzlt : ‖z‖ < r := (mem_closedBall_zero_iff.mp hz).trans_lt (by linarith)
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    have hz2 : z ∈ K2 := ⟨hz, by simp [hi]⟩
    have hzK : z ∈ K := hK2 hz2
    have hmr : (z.re : ℂ) ∈ K := he.symm ▸ hzK
    have hh := halfDisk_rowFrame_reality j hI hU hc hsigma hH hHU hparam hinv hVeq hj harc
      (by simpa only [he] using hzlt)
      (hconf (z.re : ℂ) hmr).1 (hconf (z.re : ℂ) hmr).2
    have hh' : boundaryReflection j (halfDiskFramedGradient H L r z) =
        halfDiskFramedGradient H L r z :=
      Eq.mp (congrArg (fun w => boundaryReflection j (halfDiskFramedGradient H L r w) =
        halfDiskFramedGradient H L r w) he) hh
    simpa only [F, halfDiskFramedGradient, hgrad z hz2] using hh'
  have hnot2 : ¬∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0, fderivWithin ℝ H K2 z = 0 := by
    intro hn
    apply hnot
    have hball : ∀ᶠ z : ℂ in 𝓝 0, z ∈ ball (0 : ℂ) (r / 2) :=
      isOpen_ball.mem_nhds (mem_ball_self hr2)
    filter_upwards [hn, hball.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hz hb hi
    rwa [hder z ⟨ball_subset_closedBall hb, hi⟩] at hz
  obtain ⟨d, m, q, hd, hdr2, hqc, hqi, hqne, hfactor, hq1, hqI, hholder⟩ :=
    halfDisk_differential_factor_holder (boundaryReflection j) (boundaryReflection_smul j)
      (boundaryReflection_involutive j) hr2 hH2 hHi2
      ((hL.of_le (by simp)).comp hH2 hHU2) hunit hAc hAi
      (fun z hz hi => hFeq z ⟨hz, hi⟩) hreal hnot2
  refine ⟨d, m, q, hd, hdr2.trans (by linarith), hqc, hqi, hqne, ?_, hq1, hqI, hholder⟩
  intro z hz
  rw [← hgrad z ⟨closedBall_subset_closedBall hdr2.le hz.1, hz.2⟩]
  exact hfactor z hz




theorem halfDisk_Jordan_differential_factor
    {g : RiemannianMetric 3 LoopAmbient} (D : LeviCivitaData g)
    {H : ℂ → LoopAmbient} {r : ℝ} (hr : 0 < r)
    {c : ℝ → LoopAmbient} {I J : Set ℝ} {U : Set LoopAmbient}
    {sigma : LoopAmbient → ℝ} {V : LoopAmbient → LoopAmbient} (j : Fin 3)
    (hI : IsOpen I) (hU : IsOpen U) (hc : ContDiffOn ℝ ∞ c I)
    (hsigma : ContDiffOn ℝ ∞ sigma U) (hV : ContDiffOn ℝ ∞ V U)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hHU : MapsTo H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) U)
    (hparam : ∀ q ∈ U, sigma q ∈ I)
    (hinv : ∀ s ∈ J, sigma (c s) = s)
    (hVeq : ∀ q ∈ U, V q = deriv c (sigma q))
    (hj : ∀ q ∈ U, V q j ≠ 0)
    (harc : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ r → H (s : ℂ) ∈ c '' J)
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T Complex.I) (T Complex.I) ∧
        g.inner (H z) (T 1) (T Complex.I) = 0)
    (heq : ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z))
    (hnot : ¬∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0,
      fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z = 0) :
    ∃ (d : ℝ) (m : ℕ) (q : ℂ → Fin 3 → ℂ), 0 < d ∧ d < r ∧
      ContinuousOn q (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) ∧
      ContDiffOn ℝ 1 q (ball (0 : ℂ) d ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im}, q z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im},
        halfDiskGradient H r z = z ^ m • q z) ∧
      MemLp (fun z => fderiv ℝ q z 1)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      MemLp (fun z => fderiv ℝ q z Complex.I)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) := by
  obtain ⟨d, m, q, hd, hdr, hcq, hCq, hn, hf, h1, hI', _⟩ :=
    halfDisk_Jordan_differential_factor_holder D hr j hI hU hc hsigma hV hH hHi hHU
      hparam hinv hVeq hj harc hconf heq hnot
  exact ⟨d, m, q, hd, hdr, hcq, hCq, hn, hf, h1, hI'⟩

end PoincareConjecture.M65StrictTrace
