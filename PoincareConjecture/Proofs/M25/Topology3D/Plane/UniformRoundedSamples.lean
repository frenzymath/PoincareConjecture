import PoincareConjecture.Proofs.M25.Topology3D.Plane.InscribedPolygon
import PoincareConjecture.Proofs.M25.Topology3D.Plane.MonotoneChords
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedTubeDirection
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SampledRounding
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem exists_uniform_rounded_tube_samples
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0)
    {K : Set ℝ} (hK : IsCompact K) (c : ℝ → ℝ → E)
    (hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => c p.1 p.2))
    (hper : ∀ z, Periodic (c z) (2 * Real.pi))
    (htarget : ∀ z ∈ K, ∀ s ∈ Icc 0 (2 * Real.pi), (z, c z s) ∈ T.target)
    (hproj : ∀ z ∈ K, ∀ s : ℝ,
      curveTubeProjection q0 T (z, c z s) = sphereCircleParameter e s)
    (hzero : ∀ z ∈ K, ∀ s ∈ Icc 0 (2 * Real.pi), curveTubeHeight T (z, c z s) = 0)
    {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∃ n : ℕ, 3 ≤ n ∧
      let h : ℝ := 2 * Real.pi / n
      0 < h ∧ h < ε ∧
      (∀ z ∈ K, IsSimplePolygon
        (inscribedPolygon (c z) (fun i : Fin (n + 1) => h * (i.val : ℝ)))) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ →
        (∀ s, δ ≤ |s| → ρ s = |s|) →
        (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) →
        (∀ s, |deriv ρ s| ≤ 1) →
        let G : ℝ → ℝ → E := fun z t =>
          roundedVertexPath ρ (fun j : ℤ => c z (h * (j : ℝ))) (t / h)
        ContDiff ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2) ∧
        (∀ z, Periodic (G z) (2 * Real.pi)) ∧
        ∀ z ∈ K, ∀ s ∈ Icc 0 (2 * Real.pi),
          ((z, s), G z s) ∈ curveTubeAngularDomain e q0 T ∧
          0 < fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y)) (G z s)
            (deriv (G z) s) ∧ |curveTubeHeight T (z, G z s)| < A := by
  let C : ℝ × ℝ → E := fun p => c p.1 p.2
  let d : ℝ → ℝ → E := fun z t => fderiv ℝ C (z, t) (0, 1)
  have hdcont : Continuous (fun p : ℝ × ℝ => d p.1 p.2) :=
    ((hc.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hd (z t : ℝ) : HasDerivAt (c z) (d z t) t :=
    (hc.differentiable (by simp) (z, t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))
  obtain ⟨ηc, hηc, _, hchord⟩ := exists_uniform_monotone_tube_chords e q0 T hInv hx hK
    hc.continuous.continuousOn (fun z _ t _ => hd z t) hdcont.continuousOn htarget hproj
  obtain ⟨ηp, hηp, _, hpositive⟩ := exists_uniform_positive_rounded_tube_projection e q0 T
    hInv hx hK hc.continuous.continuousOn (fun z _ t _ => hd z t)
    hdcont.continuousOn htarget hproj
  let W : Set (ℝ × E) := T.target ∩ curveTubeHeight T ⁻¹' Ioo (-A) A
  have hW : IsOpen W := (contDiffOn_curveTubeHeight T hInv hx).continuousOn.isOpen_inter_preimage
    T.open_target isOpen_Ioo
  let f : ℝ × ℝ → ℝ × E := fun p => (p.1, c p.1 p.2)
  have hf : Continuous f := continuous_fst.prodMk hc.continuous
  have hS : IsCompact (f '' (K ×ˢ Icc 0 (2 * Real.pi))) :=
    (hK.prod isCompact_Icc).image hf
  have hSW : f '' (K ×ˢ Icc 0 (2 * Real.pi)) ⊆ W := by
    rintro y ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩
    refine ⟨htarget z hz s hs, ?_⟩
    change -A < curveTubeHeight T (z, c z s) ∧ curveTubeHeight T (z, c z s) < A
    rw [hzero z hz s hs]
    exact ⟨neg_neg_of_pos hA, hA⟩
  obtain ⟨ξ, hξ, hthick⟩ := hS.exists_thickening_subset_open hW hSW
  obtain ⟨ηh, hηh, _, hestimate⟩ := exists_uniform_rounded_sampling_estimates
    (l := 0) (u := 2 * Real.pi) hK hc.continuous.continuousOn
    (fun z _ t _ => hd z t) hdcont.continuousOn hξ
  let η := min ε (min ηc (min ηp ηh))
  have hη : 0 < η := lt_min hε (lt_min hηc (lt_min hηp hηh))
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 : ℝ) (2 * Real.pi / η))
  have hn2 : (2 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn3 : 3 ≤ n := by
    have : 2 < n := by exact_mod_cast hn2
    omega
  have hn0 : (0 : ℝ) < n := by linarith
  have : NeZero n := ⟨by omega⟩
  let h : ℝ := 2 * Real.pi / n
  have hh : 0 < h := div_pos (by positivity) hn0
  have hhη : h < η := by
    have hb := (div_lt_iff₀ hη).mp ((le_max_right _ _).trans_lt hn)
    exact (div_lt_iff₀ hn0).mpr (by simpa only [mul_comm] using hb)
  have hhε : h < ε := hhη.trans_le (min_le_left _ _)
  have hhc : h < ηc := hhη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhp : h < ηp := hhη.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhh : h < ηh := hhη.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hperiod : h * (n : ℝ) = 2 * Real.pi := div_mul_cancel₀ _ hn0.ne'
  let s : Fin (n + 1) → ℝ := fun i => h * (i.val : ℝ)
  have hs : StrictMono s := fun i j hij =>
    mul_lt_mul_of_pos_left (by exact_mod_cast hij) hh
  have hs0 : s 0 = 0 := by simp only [s, Fin.val_zero, Nat.cast_zero, mul_zero]
  have hsN : s (Fin.last n) = 2 * Real.pi := hperiod
  have hsI (i : Fin (n + 1)) : s i ∈ Icc 0 (2 * Real.pi) := by
    rw [← hs0, ← hsN]
    exact ⟨hs.monotone (Fin.zero_le i), hs.monotone (Fin.le_last i)⟩
  have hmesh (i : Fin n) : s i.succ - s i.castSucc < ηc := by
    change h * ((i.val + 1 : ℕ) : ℝ) - h * (i.val : ℝ) < ηc
    push_cast
    nlinarith
  refine ⟨n, hn3, hh, hhε, ?_, ?_⟩
  · intro z hz
    let p := inscribedPolygon (c z) s
    let g : Fin n → ℝ → ℝ := fun i t =>
      curveTubeAngle e q0 T ((z, s i.castSucc), p.edgePath ℝ i t)
    have hloop : c z (2 * Real.pi) = c z 0 := (hper z).eq
    have hedge (i : Fin n) : p.edgePath ℝ i =
        AffineMap.lineMap (c z (s i.castSucc)) (c z (s i.succ)) :=
      inscribedPolygon_edgePath (c z) s (by simpa only [hsN, hs0] using hloop) i
    have hch (i : Fin n) := hchord z hz (s i.castSucc) (hsI i.castSucc)
      (s i.succ) (hsI i.succ) (hs (show i.castSucc < i.succ from Nat.lt_succ_self _))
      (hmesh i)
    have hm (i : Fin n) : StrictMonoOn (g i) (Icc (0 : ℝ) 1) := by
      simpa only [g, hedge] using (hch i).2.1
    have himg (i : Fin n) : g i '' Icc (0 : ℝ) 1 = Icc (s i.castSucc) (s i.succ) := by
      simpa only [g, hedge] using (hch i).2.2
    have hrecover (i : Fin n) (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) :
        curveTubeProjection q0 T (z, p.edgePath ℝ i t) = sphereCircleParameter e (g i t) :=
      (sphereCircleParameter_curveTubeAngle e q0 T ((z, s i.castSucc), p.edgePath ℝ i t)).symm
    exact (inscribedPolygon_simple_and_bijOn_projection e (c z)
      (fun y => curveTubeProjection q0 T (z, y)) hn3 s hs hs0 hsN hloop g hm himg hrecover).1
  · intro δ hδ hδhalf ρ hρ htail hbound hder
    dsimp only
    have hρdiff := hρ.differentiable (by simp)
    have hvertices (j : ℤ) : ContDiff ℝ ∞ (fun z => c z (h * (j : ℝ))) :=
      hc.comp (contDiff_id.prodMk contDiff_const)
    have hG := (contDiff_roundedVertexPath hδ hδhalf htail hbound hρ hvertices).comp
      (contDiff_fst.prodMk (contDiff_snd.div_const h))
    refine ⟨hG, ?_, ?_⟩
    · intro z
      have hbase : Periodic (c z) (h * (n : ℝ)) := hperiod ▸ hper z
      simpa only [hperiod] using periodic_rounded_uniform_sampling ρ (c z) hh.ne' hbase
    · intro z hz t ht
      have hdir := hpositive h hh hhp δ hδ hδhalf ρ hρdiff htail hbound hder z hz t ht
      refine ⟨hdir.1, hdir.2, ?_⟩
      have hclose := hestimate h hh hhh δ hδ hδhalf ρ hρdiff htail hbound hder z hz t ht
      have hmem : (z, roundedVertexPath ρ (fun j : ℤ => c z (h * (j : ℝ))) (t / h)) ∈ W := by
        apply hthick
        apply mem_thickening_iff.mpr
        refine ⟨f (z, t), ⟨(z, t), ⟨hz, ht⟩, rfl⟩, ?_⟩
        simpa only [f, dist_prod_same_left] using hclose.1
      exact abs_lt.mpr hmem.2

end PoincareConjecture.M25.Topology3D
