import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusPeriodicHarmonicMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.PeriodicHarmonicTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter InnerProductSpace
open scoped Topology ContDiff

namespace PoincareConjecture

private theorem modulus_integer_translate {f : LoopPlane → ℝ}
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) =
      f (annulusPoint x s))
    (z : ℤ) (p : LoopPlane) :
    f (annulusPoint (z • curvePeriod) 0 + p) = f p := by
  have hp : annulusPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> rfl
  have hshift : annulusPoint (z • curvePeriod) 0 + p =
      annulusPoint (p 0 + z • curvePeriod) (p 1) := by
    ext i
    fin_cases i <;> simp [annulusPoint, add_comm]
  have hper : Function.Periodic (fun x => f (annulusPoint x (p 1))) curvePeriod :=
    fun x => hperiod x (p 1)
  rw [hshift]
  exact (hper.zsmul z (p 0)).trans (congrArg f hp)

private theorem modulus_translated_point {f : LoopPlane → ℝ}
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) =
      f (annulusPoint x s))
    (p : LoopPlane) (hs : p 1 ∈ Icc (0 : ℝ) 1) :
    ∃ T q : LoopPlane, q ∈ m64AnnulusDomain ∧ q 0 < curvePeriod ∧
      q 1 = p 1 ∧ T + p = q ∧ ∀ r : LoopPlane, f (T + r) = f r := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let z := -toIcoDiv hP 0 (p 0)
  let T := annulusPoint (z • curvePeriod) 0
  let q := annulusPoint (toIcoMod hP 0 (p 0)) (p 1)
  have hx := toIcoMod_mem_Ico' hP (p 0)
  refine ⟨T, q, ⟨hx.1, hx.2.le, hs.1, hs.2⟩, hx.2, rfl, ?_,
    modulus_integer_translate hperiod z⟩
  ext i
  fin_cases i <;>
    simp [T, q, z, annulusPoint, toIcoMod, neg_smul, sub_eq_add_neg, add_comm]

private theorem modulus_horizontal_hasDerivAt (s x : ℝ) :
    HasDerivAt (fun y => annulusPoint y s)
      (EuclideanSpace.single (0 : Fin 2) 1) x := by
  have heq : (fun y => annulusPoint y s) = fun y =>
      annulusPoint 0 s + y • EuclideanSpace.single (0 : Fin 2) 1 := by
    funext y
    ext i
    fin_cases i <;> simp [annulusPoint]
  rw [heq]
  simpa only [one_smul, id_eq] using
    ((hasDerivAt_id x).smul_const (EuclideanSpace.single (0 : Fin 2) 1)).const_add
      (annulusPoint 0 s)

private theorem modulus_operator_translate (r : ℝ) (f : LoopPlane → ℝ)
    (T p : LoopPlane) :
    (r * fderiv ℝ (fderiv ℝ (fun q => f (T + q))) p
        (EuclideanSpace.single (0 : Fin 2) 1)
        (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (fderiv ℝ (fun q => f (T + q))) p
        (EuclideanSpace.single (1 : Fin 2) 1)
        (EuclideanSpace.single (1 : Fin 2) 1)) =
      (r * fderiv ℝ (fderiv ℝ f) (T + p)
        (EuclideanSpace.single (0 : Fin 2) 1)
        (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (fderiv ℝ f) (T + p)
        (EuclideanSpace.single (1 : Fin 2) 1)
        (EuclideanSpace.single (1 : Fin 2) 1)) := by
  have h00 : fderiv ℝ (fderiv ℝ (fun q => f (T + q))) p
      (EuclideanSpace.single (0 : Fin 2) 1)
      (EuclideanSpace.single (0 : Fin 2) 1) =
      fderiv ℝ (fderiv ℝ f) (T + p)
        (EuclideanSpace.single (0 : Fin 2) 1)
        (EuclideanSpace.single (0 : Fin 2) 1) := by
    have hcomp := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) 2 T p
    have hcomp' := congrArg
      (fun H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => LoopPlane) ℝ =>
        H ![EuclideanSpace.single (0 : Fin 2) 1,
          EuclideanSpace.single (0 : Fin 2) 1]) hcomp
    simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] using hcomp'
  have h11 : fderiv ℝ (fderiv ℝ (fun q => f (T + q))) p
      (EuclideanSpace.single (1 : Fin 2) 1)
      (EuclideanSpace.single (1 : Fin 2) 1) =
      fderiv ℝ (fderiv ℝ f) (T + p)
        (EuclideanSpace.single (1 : Fin 2) 1)
        (EuclideanSpace.single (1 : Fin 2) 1) := by
    have hcomp := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) 2 T p
    have hcomp' := congrArg
      (fun H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => LoopPlane) ℝ =>
        H ![EuclideanSpace.single (1 : Fin 2) 1,
          EuclideanSpace.single (1 : Fin 2) 1]) hcomp
    simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] using hcomp'
  rw [h00, h11]

theorem m64PeriodicModulus_equation_on_strip_of_open_regularity
    {r : ℝ} {f : LoopPlane → ℝ}
    (hreg : ContDiffOn ℝ ∞ f m64AnnulusOpenStrip)
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) =
      f (annulusPoint x s))
    (heq : ∀ p ∈ m64AnnulusInterior,
      r * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0) :
    ∀ p ∈ m64AnnulusOpenStrip,
      r * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
  intro p hp
  obtain ⟨T, q, hq, hq0lt, hq1, hpoint, hfun⟩ := modulus_translated_point hperiod p
    ⟨hp.1.le, hp.2.le⟩
  have htranslate := modulus_operator_translate r f T p
  have hfun' : (fun z => f (T + z)) = f := funext hfun
  have htranslate' := congrArg (fun g : LoopPlane → ℝ =>
      r * fderiv ℝ (fderiv ℝ g) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ g) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1)) hfun'
  have hp_eq := htranslate'.symm.trans htranslate
  rw [hpoint] at hp_eq
  by_cases hq0 : q 0 = 0
  · let e0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
    let s : ℝ := q 1
    have hs0 : 0 < s := by simpa [s, hq1] using hp.1
    have hs1 : s < 1 := by simpa [s, hq1] using hp.2
    have hpath : HasDerivAt (fun t : ℝ => q + t • e0) e0 0 := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id (0 : ℝ)).smul_const e0).const_add q
    have hqs : q ∈ m64AnnulusOpenStrip := by
      change 0 < q 1 ∧ q 1 < 1
      rw [hq1]
      exact hp
    have h3 : ContDiffAt ℝ 3 f q :=
      (hreg.contDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds hqs)).of_le (by norm_cast)
    have hd := h3.differentiableAt_iteratedFDeriv (m := 2) (by norm_num)
    have h00 := (hd.continuousMultilinear_apply_const
      ![EuclideanSpace.single (0 : Fin 2) 1,
        EuclideanSpace.single (0 : Fin 2) 1]).continuousAt
    have h11 := (hd.continuousMultilinear_apply_const
      ![EuclideanSpace.single (1 : Fin 2) 1,
        EuclideanSpace.single (1 : Fin 2) 1]).continuousAt
    have hOp := (h00.const_mul r).add (h11.const_mul r⁻¹)
    have hpath_lim : Tendsto (fun t : ℝ => q + t • e0) (𝓝 (0 : ℝ)) (𝓝 q) := by
      simpa only [zero_smul, add_zero] using hpath.continuousAt.tendsto
    have hlim := hOp.tendsto.comp hpath_lim
    have hlim' : Tendsto (fun t : ℝ =>
        r * fderiv ℝ (fderiv ℝ f) (q + t • e0)
            (EuclideanSpace.single (0 : Fin 2) 1)
            (EuclideanSpace.single (0 : Fin 2) 1) +
          r⁻¹ * fderiv ℝ (fderiv ℝ f) (q + t • e0)
            (EuclideanSpace.single (1 : Fin 2) 1)
            (EuclideanSpace.single (1 : Fin 2) 1)) (𝓝 (0 : ℝ))
        (𝓝 (r * fderiv ℝ (fderiv ℝ f) q
            (EuclideanSpace.single (0 : Fin 2) 1)
            (EuclideanSpace.single (0 : Fin 2) 1) +
          r⁻¹ * fderiv ℝ (fderiv ℝ f) q
            (EuclideanSpace.single (1 : Fin 2) 1)
            (EuclideanSpace.single (1 : Fin 2) 1))) := by
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Function.comp_def,
        Pi.add_apply] using hlim
    have hpath_eq (t : ℝ) : q + t • e0 = annulusPoint t s := by
      ext i
      fin_cases i <;> simp [e0, s, hq0, annulusPoint]
    have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        r * fderiv ℝ (fderiv ℝ f) (q + t • e0)
            (EuclideanSpace.single (0 : Fin 2) 1)
            (EuclideanSpace.single (0 : Fin 2) 1) +
          r⁻¹ * fderiv ℝ (fderiv ℝ f) (q + t • e0)
            (EuclideanSpace.single (1 : Fin 2) 1)
            (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hP)] with t ht0 htP
      rw [hpath_eq t]
      apply heq
      simpa [m64AnnulusInterior, Set.mem_pi, Fin.forall_fin_two, and_assoc,
        annulusPoint] using (show 0 < t ∧ t < curvePeriod ∧ 0 < s ∧ s < 1 from
          ⟨ht0, htP, hs0, hs1⟩)
    have hlimWithin := hlim'.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi (0 : ℝ)))
    have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds
    have hev' : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)] (fun t =>
        r * fderiv ℝ (fderiv ℝ f) (q + t • e0)
            (EuclideanSpace.single (0 : Fin 2) 1)
            (EuclideanSpace.single (0 : Fin 2) 1) +
          r⁻¹ * fderiv ℝ (fderiv ℝ f) (q + t • e0)
            (EuclideanSpace.single (1 : Fin 2) 1)
            (EuclideanSpace.single (1 : Fin 2) 1)) :=
      hev.mono fun t ht => ht.symm
    have hzero' := Filter.Tendsto.congr' hev' hzero
    have hvalue := tendsto_nhds_unique hzero' hlimWithin
    exact hp_eq.trans hvalue.symm
  · have hqint : q ∈ m64AnnulusInterior := by
      simp only [m64AnnulusInterior, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
        Set.mem_Ioo]
      intro i hi
      fin_cases i
      · exact ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq0lt⟩
      · exact ⟨by simpa [hq1] using hp.1, by simpa [hq1] using hp.2⟩
    exact hp_eq.trans (heq q hqint)

theorem m64PeriodicModulus_equation_on_strip
    {r : ℝ} {f : LoopPlane → ℝ}
    (hreg : ∀ p ∈ m64AnnulusDomain, ContDiffAt ℝ ∞ f p)
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) =
      f (annulusPoint x s))
    (heq : ∀ p ∈ m64AnnulusInterior,
      r * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0) :
    ∀ p ∈ m64AnnulusOpenStrip,
      r * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0 :=
  m64PeriodicModulus_equation_on_strip_of_open_regularity
    (fun _ hp => (m64PeriodicScalar_contDiffAt_of_fundamental hreg hperiod
      ⟨hp.1.le, hp.2.le⟩).contDiffWithinAt) hperiod heq

end PoincareConjecture
