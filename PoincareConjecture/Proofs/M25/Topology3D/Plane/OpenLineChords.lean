import PoincareConjecture.Proofs.M25.Topology3D.Plane.ChordNeighborhood
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem exists_uniform_monotone_openLine_chords
    (T : OpenPartialHomeomorph
      ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    {K : Set ℝ} (hK : IsCompact K)
    {c d : ℝ → ℝ → ℝ × ℝ} {l u : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2) (K ×ˢ Icc l u))
    (hd : ∀ z ∈ K, ∀ s ∈ Icc l u, HasDerivAt (c z) (d z s) s)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => d p.1 p.2) (K ×ˢ Icc l u))
    (htarget : ∀ z ∈ K, ∀ s ∈ Icc l u, ((z, 0), c z s) ∈ T.target)
    (hproj : ∀ z ∈ K, ∀ s : ℝ, (T.symm ((z, 0), c z s)).2.1 = s)
    (hzero : ∀ z ∈ K, ∀ s ∈ Icc l u, (T.symm ((z, 0), c z s)).2.2 = 0)
    {A : ℝ} (hA : 0 < A) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ K, ∀ a ∈ Icc l u, ∀ b ∈ Icc l u, a < b → b - a < δ →
        let L : ℝ → ℝ × ℝ := AffineMap.lineMap (c z a) (c z b)
        let P : ℝ × (ℝ × ℝ) → ℝ :=
          fun p => (T.symm ((p.1, 0), p.2)).2.1
        let f : ℝ → ℝ := fun t => P (z, L t)
        (∀ t ∈ Icc (0 : ℝ) 1,
          ((z, 0), L t) ∈ T.target ∧
          0 < fderiv ℝ P (z, L t) (0, slope (c z) a b) ∧
          |(T.symm ((z, 0), L t)).2.2| < A) ∧
        StrictMonoOn f (Icc (0 : ℝ) 1) ∧
        f '' Icc (0 : ℝ) 1 = Icc a b := by
  let j : (ℝ × (ℝ × ℝ)) → ((ℝ × ℝ) × (ℝ × ℝ)) :=
    fun p => ((p.1, 0), p.2)
  let V : Set (ℝ × (ℝ × ℝ)) := j ⁻¹' T.target
  let P : ℝ × (ℝ × ℝ) → ℝ :=
    fun p => (T.symm ((p.1, 0), p.2)).2.1
  let H : ℝ × (ℝ × ℝ) → ℝ :=
    fun p => (T.symm ((p.1, 0), p.2)).2.2
  have hj : ContDiff ℝ ∞ j := by
    have hfirst : ContDiff ℝ ∞
        (fun p : ℝ × (ℝ × ℝ) => (p.1, (0 : ℝ))) :=
      contDiff_fst.prodMk (contDiff_const :
        ContDiff ℝ ∞ (fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ)))
    simpa only [j] using hfirst.prodMk contDiff_snd
  have hV : IsOpen V := T.open_target.preimage hj.continuous
  have hcoords : ContDiffOn ℝ ∞ (fun p => T.symm (j p)) V := by
    apply hInv.comp hj.contDiffOn
    intro p hp
    exact hp
  have hP : ContDiffOn ℝ ∞ P V := by
    simpa only [P, j] using hcoords.snd.fst
  have hH : ContDiffOn ℝ ∞ H V := by
    simpa only [H, j] using hcoords.snd.snd
  let S : ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) → (ℝ × (ℝ × ℝ)) :=
    fun q => (q.1.1, q.2.1)
  let B : Set ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) := S ⁻¹' V
  let J : ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) → ℝ :=
    fun q => fderiv ℝ P (S q) (0, q.2.2)
  let N : ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) → ℝ := fun q => H (S q)
  have hS : ContDiff ℝ ∞ S := by
    simpa only [S] using contDiff_fst.fst.prodMk contDiff_snd.fst
  have hB : IsOpen B := hV.preimage hS.continuous
  have hfd : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ P p) V := by
    exact hP.continuousOn_fderiv_of_isOpen hV (by simp)
  have hJ : ContinuousOn J B := by
    have hbase : ContinuousOn (fun q => fderiv ℝ P (S q)) B :=
      hfd.comp hS.continuous.continuousOn (fun _ hq => hq)
    exact hbase.clm_apply ((continuous_const.prodMk continuous_snd.snd).continuousOn)
  have hN : ContinuousOn N B := hH.continuousOn.comp hS.continuous.continuousOn
    (fun _ hq => hq)
  let W : Set ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) :=
    B ∩ J ⁻¹' Ioi 0 ∩ (B ∩ N ⁻¹' Ioo (-A) A)
  have hW : IsOpen W := by
    have hJ' : IsOpen (B ∩ J ⁻¹' Ioi 0) :=
      hJ.isOpen_inter_preimage hB isOpen_Ioi
    have hN' : IsOpen (B ∩ N ⁻¹' Ioo (-A) A) :=
      hN.isOpen_inter_preimage hB (isOpen_Ioo)
    exact hJ'.inter hN'
  have hbase : ∀ z ∈ K, ∀ s ∈ Icc l u,
      ((z, s), (c z s, d z s)) ∈ W := by
    intro z hz s hs
    have hmem : (z, c z s) ∈ V := by
      change ((z, 0), c z s) ∈ T.target
      exact htarget z hz s hs
    have hcal : fderiv ℝ P (z, c z s) (0, d z s) = 1 := by
      have hp : HasFDerivAt P (fderiv ℝ P (z, c z s)) (z, c z s) :=
        (hP.contDiffAt (hV.mem_nhds hmem)).differentiableAt (by simp) |>.hasFDerivAt
      have hconst : HasFDerivAt (fun _ : ℝ => z) (0 : ℝ →L[ℝ] ℝ) s :=
        hasFDerivAt_const z s
      have hcp := hconst.prodMk (hd z hz s hs).hasFDerivAt
      have hc := hp.comp s hcp
      have hid : HasDerivAt (fun v : ℝ => v) 1 s := hasDerivAt_id s
      have hcomp : HasDerivAt (fun v : ℝ => P (z, c z v))
          ((fderiv ℝ P (z, c z s)) (0, d z s)) s := by
        simpa [Function.comp_def] using hc.hasDerivAt
      exact (hid.unique (by simpa only [P, hproj z hz] using hcomp)).symm
    have hzero' : H (z, c z s) = 0 := hzero z hz s hs
    have hNmem : N ((z, s), (c z s, d z s)) ∈ Ioo (-A) A := by
      change -A < H (z, c z s) ∧ H (z, c z s) < A
      rw [hzero']
      exact ⟨by linarith, hA⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, hNmem⟩⟩
    · change (z, c z s) ∈ V
      exact hmem
    · change 0 < (fderiv ℝ P (z, c z s)) (0, d z s)
      rw [hcal]
      norm_num
    · change (z, c z s) ∈ V
      exact hmem
  obtain ⟨δ, hδ, hshort⟩ := exists_uniform_short_chord_direction_mem_open hK hc
    (fun z hz s hs => (hd z hz s hs).hasDerivWithinAt) hcont hW hbase
  refine ⟨δ, hδ, ?_⟩
  intro z hz a ha b hb hab hmesh
  let L : ℝ → ℝ × ℝ := AffineMap.lineMap (c z a) (c z b)
  let f : ℝ → ℝ := fun t => P (z, L t)
  have hch : ∀ t ∈ Icc (0 : ℝ) 1,
      ((z, a), (L t, slope (c z) a b)) ∈ W := by
    intro t ht
    exact hshort z hz a ha b hb hab hmesh t ht
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (z, L t) ∈ V := by
    intro t ht
    have hh := (hch t ht).1.1
    change (z, L t) ∈ V at hh
    exact hh
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1,
      0 < fderiv ℝ P (z, L t) (0, slope (c z) a b) := by
    intro t ht
    have hh := (hch t ht).1.2
    change 0 < (fderiv ℝ P (z, L t)) (0, slope (c z) a b) at hh
    exact hh
  have hheight : ∀ t ∈ Icc (0 : ℝ) 1, |H (z, L t)| < A := by
    intro t ht
    have hh := (hch t ht).2.2
    change -A < H (z, L t) ∧ H (z, L t) < A at hh
    exact (abs_lt.mpr hh)
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f (fderiv ℝ P (z, L t) (0, c z b - c z a)) t := by
    intro t ht
    have hslice : DifferentiableAt ℝ (fun y : ℝ × ℝ => P (z, y)) (L t) := by
      have hp := hP.contDiffAt (hV.mem_nhds (hmem t ht))
      exact (ContDiffAt.comp (g := P) (f := fun y : ℝ × ℝ => (z, y)) (L t)
        hp (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have hh := hslice.hasFDerivAt.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := c z a) (b := c z b) (x := t))
    have hpfull : HasFDerivAt P (fderiv ℝ P (z, L t)) (z, L t) :=
      (hP.contDiffAt (hV.mem_nhds (hmem t ht))).differentiableAt (by simp) |>.hasFDerivAt
    have hpair := hasFDerivAt_prodMk_right (𝕜 := ℝ) z (L t)
    have heq := (hpfull.comp (L t) hpair).fderiv
    have hderval : (fderiv ℝ (fun y : ℝ × ℝ => P (z, y)) (L t))
        (c z b - c z a) = (fderiv ℝ P (z, L t)) (0, c z b - c z a) := by
      have hv := congrArg (fun q => q (c z b - c z a)) heq
      simpa [Function.comp_def] using hv
    have hh' : HasDerivAt (fun t => P (z, L t))
        ((fderiv ℝ (fun y : ℝ × ℝ => P (z, y)) (L t)) (c z b - c z a)) t := by
      simpa [Function.comp_def] using hh
    rw [hderval] at hh'
    exact hh'
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hder t ht).continuousAt.continuousWithinAt
  have hm : StrictMonoOn f (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    have hsec : (b - a) • slope (c z) a b = c z b - c z a := by
      simpa only [vsub_eq_sub] using sub_smul_slope (c z) a b
    have hdir : ((0 : ℝ), (b - a) • slope (c z) a b) =
        (b - a) • ((0 : ℝ), slope (c z) a b) := by ext <;> simp
    rw [(hder t ht').deriv, ← hsec, hdir, map_smul, smul_eq_mul]
    exact mul_pos (sub_pos.mpr hab) (hpos t ht')
  have hf0 : f 0 = a := by
    change P (z, AffineMap.lineMap (c z a) (c z b) 0) = a
    rw [AffineMap.lineMap_apply_zero]
    exact hproj z hz a
  have hf1 : f 1 = b := by
    change P (z, AffineMap.lineMap (c z a) (c z b) 1) = b
    rw [AffineMap.lineMap_apply_one]
    exact hproj z hz b
  refine ⟨?_, hm, ?_⟩
  · intro t ht
    refine ⟨?_, ?_, ?_⟩
    · change ((z, 0), L t) ∈ T.target
      have hh := hmem t ht
      change ((z, 0), L t) ∈ T.target at hh
      exact hh
    · exact hpos t ht
    · simpa only [H] using hheight t ht
  · simpa only [hf0, hf1] using hf.image_Icc_of_monotoneOn (by norm_num) hm.monotoneOn

end PoincareConjecture.M25.Topology3D
