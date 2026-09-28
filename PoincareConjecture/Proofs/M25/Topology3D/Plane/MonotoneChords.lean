import PoincareConjecture.Proofs.M25.Topology3D.Plane.ChordNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubeAngle
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.AffineMap











set_option autoImplicit false

open Set Metric Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D




theorem exists_uniform_monotone_tube_chords
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0)
    {K : Set ℝ} (hK : IsCompact K) {c d : ℝ → ℝ → E} {l u : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2) (K ×ˢ Icc l u))
    (hd : ∀ z ∈ K, ∀ s ∈ Icc l u, HasDerivAt (c z) (d z s) s)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => d p.1 p.2) (K ×ˢ Icc l u))
    (htarget : ∀ z ∈ K, ∀ s ∈ Icc l u, (z, c z s) ∈ T.target)
    (hproj : ∀ z ∈ K, ∀ s : ℝ,
      curveTubeProjection q0 T (z, c z s) = sphereCircleParameter e s) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi ∧
      ∀ z ∈ K, ∀ a ∈ Icc l u, ∀ b ∈ Icc l u, a < b → b - a < δ →
        let L : ℝ → E := AffineMap.lineMap (c z a) (c z b)
        let f : ℝ → ℝ := fun t => curveTubeAngle e q0 T ((z, a), L t)
        (∀ t ∈ Icc (0 : ℝ) 1,
          ((z, a), L t) ∈ curveTubeAngularDomain e q0 T ∧
            0 < fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, a), y)) (L t)
              (slope (c z) a b)) ∧
          StrictMonoOn f (Icc (0 : ℝ) 1) ∧ f '' Icc (0 : ℝ) 1 = Icc a b := by
  let A := curveTubeAngle e q0 T
  let V := curveTubeAngularDomain e q0 T
  let D : (ℝ × ℝ) × E → E →L[ℝ] ℝ := fun p => fderiv ℝ (fun y : E => A (p.1, y)) p.2
  obtain ⟨hV, hA⟩ := curveTubeAngle_regular e q0 T hInv hx
  have hD : ContinuousOn D V := (contDiffOn_fderiv_curveTubeAngle e q0 T hInv hx).continuousOn
  let B : Set ((ℝ × ℝ) × (E × E)) := {p | (p.1, p.2.1) ∈ V}
  let J : (ℝ × ℝ) × (E × E) → ℝ := fun p => D (p.1, p.2.1) p.2.2
  have hB : IsOpen B := hV.preimage (continuous_fst.prodMk continuous_snd.fst)
  have hJ : ContinuousOn J B :=
    (hD.comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
      (fun _ hp => hp)).clm_apply continuous_snd.snd.continuousOn
  let W := B ∩ J ⁻¹' Ioi 0
  have hW : IsOpen W := hJ.isOpen_inter_preimage hB isOpen_Ioi
  have hbase : ∀ z ∈ K, ∀ s ∈ Icc l u, ((z, s), (c z s, d z s)) ∈ W := by
    intro z hz s hs
    have hmem := mem_curveTubeAngularDomain_of_projection e q0 T z s s (c z s)
      (htarget z hz s hs) (hproj z hz s)
      (show s - s ∈ Ioo (-Real.pi) Real.pi by simp [Real.pi_pos])
    refine ⟨hmem, ?_⟩
    have hcal := fderiv_curveTubeAngle_apply_velocity e q0 T hInv hx (c z) z s
      (hd z hz s hs).differentiableAt (htarget z hz s hs) (hproj z hz)
    rw [(hd z hz s hs).deriv] at hcal
    change 0 < fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y)) (c z s) (d z s)
    rw [hcal]
    norm_num
  obtain ⟨δ0, hδ0, hshort⟩ := exists_uniform_short_chord_direction_mem_open hK hc
    (fun z hz s hs => (hd z hz s hs).hasDerivWithinAt) hcont hW hbase
  have hδpi : min δ0 (Real.pi / 2) < Real.pi :=
    (min_le_right _ _).trans_lt (half_lt_self Real.pi_pos)
  refine ⟨min δ0 (Real.pi / 2), lt_min hδ0 (half_pos Real.pi_pos), hδpi, ?_⟩
  intro z hz a ha b hb hab hmesh
  let L : ℝ → E := AffineMap.lineMap (c z a) (c z b)
  let f : ℝ → ℝ := fun t => A ((z, a), L t)
  have hch := hshort z hz a ha b hb hab (hmesh.trans_le (min_le_left _ _))
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, ((z, a), L t) ∈ V := fun t ht => (hch t ht).1
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < D ((z, a), L t) (slope (c z) a b) :=
    fun t ht => (hch t ht).2
  refine ⟨fun t ht => ⟨hmem t ht, hpos t ht⟩, ?_⟩
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (D ((z, a), L t) (c z b - c z a)) t := by
    intro t ht
    have hslice : DifferentiableAt ℝ (fun y : E => A ((z, a), y)) (L t) :=
      (ContDiffAt.comp (g := A) (f := fun y : E => ((z, a), y)) (L t)
        (hA.contDiffAt (hV.mem_nhds (hmem t ht)))
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact hslice.hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hm : StrictMonoOn f (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    have hsec : (b - a) • slope (c z) a b = c z b - c z a := by
      simpa only [vsub_eq_sub] using sub_smul_slope (c z) a b
    rw [(hder t ht').deriv, ← hsec, map_smul, smul_eq_mul]
    exact mul_pos (sub_pos.mpr hab) (hpos t ht')
  have hf0 : f 0 = a := by
    change A ((z, a), AffineMap.lineMap (c z a) (c z b) 0) = a
    rw [AffineMap.lineMap_apply_zero]
    exact curveTubeAngle_apply e q0 T z a a (c z a) (hproj z hz a)
      (by simp [Real.pi_pos, Real.pi_pos.le])
  have hf1 : f 1 = b := by
    change A ((z, a), AffineMap.lineMap (c z a) (c z b) 1) = b
    rw [AffineMap.lineMap_apply_one]
    exact curveTubeAngle_apply e q0 T z a b (c z b) (hproj z hz b)
      ⟨by linarith [Real.pi_pos], (hmesh.trans hδpi).le⟩
  refine ⟨hm, ?_⟩
  simpa only [hf0, hf1] using hf.image_Icc_of_monotoneOn (by norm_num) hm.monotoneOn

end PoincareConjecture.M25.Topology3D
