import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactExtension
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientLabelVelocity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorSecondDerivativeLp
import PoincareConjecture.Proofs.M63.Mathlib.CompactPartialDerivativeBounds
import PoincareConjecture.Proofs.M63.Mathlib.ContinuousL2Product
import Mathlib.Topology.CompactOpen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory AddCircle PoincareConjecture.SpectralHeatNative
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "H" => State ((ℤ × Fin 2) × ι)

theorem exists_uniform_spectral_labelVelocity_L2_bound
    (F : RicciFlow n M (Icc a b)) {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {S L : ℝ} (hS : 0 < S) (hSb : S < b - a) [Fact (0 < L)]
    {K : Set (W × W)} (hK : IsCompact K)
    (hKU : K ⊆ {z : W × W | z.1 ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0})
    (Vn : ℕ → C(Icc (0 : ℝ) S, H)) (V : C(Icc (0 : ℝ) S, H))
    (hV : Tendsto Vn atTop (𝓝 V)) (qn : ℕ → ℝ → ℝ → W)
    (hq : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (qn j)) (Icc 0 S ×ˢ univ))
    (hqzero : ∀ j (t : Icc (0 : ℝ) S) (x : ℝ), qn j t.1 x =
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega)
        (Vn j t) (x : AddCircle L)))
    (hphase : ∀ j (t : Icc (0 : ℝ) S), DifferentiableAt ℝ
      (fun r : ℝ => vectorPeriodicSpectralTranslation (L := L) r (Vn j t)) 0)
    (hjets : ∀ j (t : Icc (0 : ℝ) S) (x : AddCircle L),
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) (Vn j t) x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) (Vn j t) x)) ∈ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ w : ℕ → ℝ → C(AddCircle L, ℝ),
      (∀ j, ContinuousOn (w j) (Icc 0 S)) ∧
      (∀ j t, t ∈ Icc 0 S → ∀ x : ℝ, w j t (x : AddCircle L) =
        deriv (fun y => ambientCurvePrincipal F ρ (a + t)
          (qn j t y) (deriv (qn j t) y)) x / 2) ∧
      ∀ j t, t ∈ Icc 0 S →
        ‖ContinuousMap.toLp 2 haarAddCircle ℝ (w j t)‖ ≤ B := by
  classical
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let f : ℝ × (W × W) → ℝ := fun z =>
    ambientCurvePrincipal F ρ (a + z.1) z.2.1 z.2.2
  have hΩ : IsOpen Ω := isOpen_ambientCurveJetDomain F hU hρ
  have hAraw :=
    (ambientCurveCoefficients_contDiffOn F (e := fun _ => (0 : W)) contMDiff_const hU hρ).1
  have hparam : ContDiff ℝ ∞
      (fun z : ℝ × (W × W) => ((a + z.1, z.2.1), z.2.2)) := by fun_prop
  have hf : ContDiffOn ℝ ∞ f (Ico 0 (b - a) ×ˢ Ω) :=
    hAraw.comp (s := Ico 0 (b - a) ×ˢ Ω) hparam.contDiffOn (by
      intro z hz
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩)
  obtain ⟨g, hg, hgc, O, hO, hKO, _hOU, heq⟩ :=
    exists_finiteOrder_initialSlab_extension 2 hΩ hK hKU (hS.trans hSb)
      hS.le hSb f (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  let G := fun t z => (fderiv ℝ g (t, z)).comp
    (ContinuousLinearMap.inr ℝ ℝ (W × W))
  obtain ⟨hG, A, _B, hGbound, _hGlip⟩ := exists_uniform_partial_derivative_bounds hg hgc
  change Continuous (Function.uncurry G) at hG
  change ∀ t z, HasFDerivAt (fun y => g (t, y)) (G t z) z ∧ ‖G t z‖ ≤ A at hGbound
  have hactual (t : ℝ) (ht : t ∈ Icc 0 S) (z : W × W) (hz : z ∈ K) :
      HasFDerivAt (fun y => f (t, y)) (G t z) z := by
    have hnear : ∀ᶠ y in 𝓝 z, (t, y) ∈ O :=
      (continuous_const.prodMk continuous_id).continuousAt (hO.mem_nhds (hKO ⟨ht, hz⟩))
    apply ((hGbound t z).1).congr_of_eventuallyEq
    filter_upwards [hnear] with y hy
    exact (heq ⟨hy, ht.1, mem_univ _⟩).symm
  obtain ⟨P0, hP0⟩ := hK.exists_bound_of_continuousOn
    (continuous_snd.continuousOn : ContinuousOn (fun z : W × W => z.2) K)
  let P : ℝ := max P0 0
  have hP : 0 ≤ P := le_max_right _ _
  have hPbound (z : W × W) (hz : z ∈ K) : ‖z.2‖ ≤ P :=
    (hP0 z hz).trans (le_max_left _ _)
  obtain ⟨C0, hC0⟩ := hV.isCompact_insert_range.exists_bound_of_continuousOn
    (continuousOn_id : ContinuousOn (fun u : C(Icc (0 : ℝ) S, H) => u) (insert V (range Vn)))
  let C : ℝ := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hstate (j : ℕ) (t : Icc (0 : ℝ) S) : ‖Vn j t‖ ≤ C :=
    ((Vn j).norm_coe_le_norm t).trans
      ((hC0 (Vn j) (mem_insert_of_mem _ (mem_range_self j))).trans (le_max_left _ _))
  let D2 : H →L[ℝ] Lp W 2 (haarAddCircle (T := L)) := vectorPeriodicSecondDerivativeLp
  have hD2 (j : ℕ) (t : Icc (0 : ℝ) S) : ‖D2 (Vn j t)‖ ≤ ‖D2‖ * C :=
    (D2.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hstate j t) (norm_nonneg _))
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let Q (u : H) : C(AddCircle L, W) := E.symm.toContinuousLinearMap.compLeftContinuous ℝ _
    (vectorPeriodicJet (L := L) 1 0 (by omega) u)
  let Q1 (u : H) : C(AddCircle L, W) := E.symm.toContinuousLinearMap.compLeftContinuous ℝ _
    (vectorPeriodicJet (L := L) 1 1 (by omega) u)
  have hqeq (j : ℕ) (t : Icc (0 : ℝ) S) :
      qn j t.1 = fun x : ℝ => Q (Vn j t) (x : AddCircle L) := funext (hqzero j t)
  have hfirst (j : ℕ) (t : Icc (0 : ℝ) S) (x : ℝ) :
      HasDerivAt (qn j t.1) (Q1 (Vn j t) (x : AddCircle L)) x := by
    rw [hqeq j t]
    exact E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_vectorPeriodicJet (L := L) (by omega : 0 < 1) (Vn j t) x)
  have hder (j : ℕ) (t : Icc (0 : ℝ) S) :
      deriv (qn j t.1) = fun x : ℝ => Q1 (Vn j t) (x : AddCircle L) :=
    funext fun x => (hfirst j t x).deriv
  have hJ (j : ℕ) (t : Icc (0 : ℝ) S) (x : AddCircle L) :
      (Q (Vn j t) x, Q1 (Vn j t) x) ∈ K := hjets j t x
  have hguard (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 S) (x : ℝ) :
      qn j t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (qn j t x) (deriv (qn j t) x) ≠ 0 := by
    rw [hder j ⟨t, ht⟩, hqeq j ⟨t, ht⟩]
    exact hKU (hJ j ⟨t, ht⟩ (x : AddCircle L))
  let raw := fun j t x => deriv (fun y =>
    ambientCurvePrincipal F ρ (a + t) (qn j t y) (deriv (qn j t) y)) x / 2
  have hregular (j : ℕ) :
      ContDiffOn ℝ ∞ (Function.uncurry (raw j)) (Icc 0 S ×ˢ univ) ∧
        ∀ t ∈ Icc 0 S, Function.Periodic (raw j t) L := by
    apply ambientCurve_labelVelocity_regular F hU hρ hS (by linarith) (hq j)
    · intro t ht x
      rw [hqeq j ⟨t, ht⟩]
      change Q (Vn j ⟨t, ht⟩) ((x + L : ℝ) : AddCircle L) =
        Q (Vn j ⟨t, ht⟩) (x : AddCircle L)
      rw [AddCircle.coe_add_period]
    · exact hguard j
  have hdesc (j : ℕ) : ∃ w : ℝ → C(AddCircle L, ℝ),
      ContinuousOn w (Icc 0 S) ∧
        ∀ t ∈ Icc 0 S, ∀ x : ℝ, w t (x : AddCircle L) = raw j t x := by
    have hrawc : ContinuousOn (Function.uncurry (raw j)) (Icc 0 S ×ˢ univ) :=
      (hregular j).1.continuousOn
    let w : ℝ → C(AddCircle L, ℝ) := fun t => if ht : t ∈ Icc 0 S then
      ⟨((hregular j).2 t ht).lift,
        (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
          (hrawc.comp_continuous (f := fun x : ℝ => (t, x))
            (continuous_const.prodMk continuous_id) (fun _ => ⟨ht, mem_univ _⟩))⟩ else 0
    have hval (t : ℝ) (ht : t ∈ Icc 0 S) (x : ℝ) :
        w t (x : AddCircle L) = raw j t x := by
      simp only [w, dif_pos ht, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
    refine ⟨w, continuousOn_iff_continuous_domRestrict.mpr ?_, hval⟩
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun p : Icc (0 : ℝ) S × ℝ => (p.1, (p.2 : AddCircle L))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    have hc : Continuous (fun p : Icc (0 : ℝ) S × ℝ => raw j p.1.1 p.2) :=
      hrawc.comp_continuous (f := fun p : Icc (0 : ℝ) S × ℝ => (p.1.1, p.2))
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun p => ⟨p.1.2, mem_univ _⟩)
    exact hc.congr (fun p => (hval p.1.1 p.1.2 p.2).symm)
  choose w hw hwval using hdesc
  let T : C(AddCircle L, ℝ) →L[ℝ] Lp ℝ 2 haarAddCircle :=
    ContinuousMap.toLp 2 haarAddCircle ℝ
  have hTnorm : ‖T‖ ≤ 1 := by
    simpa [T, measureUnivNNReal] using
      (ContinuousMap.toLp_norm_le (p := 2) (𝕜 := ℝ) (E := ℝ) haarAddCircle)
  obtain ⟨Mul, hMulnorm, hMul⟩ := exists_continuousL2_product
    (haarAddCircle : Measure (AddCircle L)) (ContinuousLinearMap.id ℝ (W →L[ℝ] ℝ))
  have hMulone : ‖Mul‖ ≤ 1 := hMulnorm.trans ContinuousLinearMap.norm_id_le
  refine ⟨(A : ℝ) / 2 * (‖D2‖ * C + P), by positivity, w, hw, hwval, ?_⟩
  intro j t ht
  let u := Vn j ⟨t, ht⟩
  let J : C(AddCircle L, W × W) := (Q u).prodMk (Q1 u)
  have hJmem (z : AddCircle L) : J z ∈ K := hJ j ⟨t, ht⟩ z
  have hGJ : Continuous (fun z : AddCircle L => G t (J z)) :=
    hG.comp (continuous_const.prodMk J.continuous)
  let lam : C(AddCircle L, W →L[ℝ] ℝ) :=
    ⟨fun z => (1 / 2 : ℝ) • (G t (J z)).comp (ContinuousLinearMap.inr ℝ W W),
      (continuous_const : Continuous (fun _ : AddCircle L => (1 / 2 : ℝ))).smul
        (hGJ.clm_comp (continuous_const : Continuous
          (fun _ : AddCircle L => ContinuousLinearMap.inr ℝ W W)))⟩
  let eta : C(AddCircle L, ℝ) :=
    ⟨fun z => G t (J z) ((J z).2, 0) / 2,
      (hGJ.clm_apply ((continuous_snd.comp J.continuous).prodMk continuous_const)).div_const 2⟩
  have hlamnorm : ‖lam‖ ≤ (A : ℝ) / 2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro z
    change ‖(1 / 2 : ℝ) • (G t (J z)).comp (ContinuousLinearMap.inr ℝ W W)‖ ≤ _
    rw [norm_smul]
    norm_num only [Real.norm_eq_abs, abs_div, abs_one]
    have hc := (G t (J z)).opNorm_comp_le (ContinuousLinearMap.inr ℝ W W)
    have hi := ContinuousLinearMap.norm_inr_le_one ℝ W W
    have hb := (hGbound t (J z)).2
    nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg (G t (J z)))]
  have hetanorm : ‖eta‖ ≤ (A : ℝ) / 2 * P := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro z
    change ‖G t (J z) ((J z).2, 0) / 2‖ ≤ _
    rw [norm_div]
    have hp : ‖((J z).2, (0 : W))‖ = ‖(J z).2‖ := by simp
    have hb := (G t (J z)).le_opNorm ((J z).2, 0)
    rw [hp, Real.norm_eq_abs] at hb
    have hmul := mul_le_mul (hGbound t (J z)).2 (hPbound (J z) (hJmem z))
      (norm_nonneg _) A.property
    norm_num only [Real.norm_eq_abs]
    nlinarith
  obtain ⟨r, _hrc2, hr, _hrder, hrLp⟩ := vectorPeriodicSecondDerivativeLp_spec u
    (hphase j ⟨t, ht⟩)
  change D2 u = ContinuousMap.toLp 2 haarAddCircle ℝ r at hrLp
  have hsecond (x : ℝ) : HasDerivAt (deriv (qn j t)) (r (x : AddCircle L)) x := by
    rw [hder j ⟨t, ht⟩]
    exact hr x
  have hlabel (x : ℝ) : raw j t x =
      lam (x : AddCircle L) (r (x : AddCircle L)) + eta (x : AddCircle L) := by
    have hpair := (hfirst j ⟨t, ht⟩ x).prodMk (hsecond x)
    have ha : HasFDerivAt (fun y => f (t, y)) (G t (J (x : AddCircle L)))
        (qn j t x, deriv (qn j t) x) := by
      rw [hder j ⟨t, ht⟩, hqeq j ⟨t, ht⟩]
      exact hactual t ht (J (x : AddCircle L)) (hJmem _)
    have hchain := ha.comp_hasDerivAt x hpair
    have hd : deriv (fun y => f (t, (qn j t y, deriv (qn j t) y))) x =
        G t (J (x : AddCircle L))
          (Q1 u (x : AddCircle L), r (x : AddCircle L)) := by
      simpa only [Function.comp_def, hqeq j ⟨t, ht⟩, hder j ⟨t, ht⟩] using hchain.deriv
    have hsplit : G t (J (x : AddCircle L))
        (Q1 u (x : AddCircle L), r (x : AddCircle L)) =
      G t (J (x : AddCircle L)) (Q1 u (x : AddCircle L), 0) +
        G t (J (x : AddCircle L)) (0, r (x : AddCircle L)) := by
      rw [← map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    change deriv (fun y => f (t, (qn j t y, deriv (qn j t) y))) x / 2 = _
    rw [hd, hsplit]
    change (G t (J (x : AddCircle L)) (Q1 u (x : AddCircle L), 0) +
        G t (J (x : AddCircle L)) (0, r (x : AddCircle L))) / 2 =
      (1 / 2 : ℝ) * G t (J (x : AddCircle L)) (0, r (x : AddCircle L)) +
        G t (J (x : AddCircle L)) (Q1 u (x : AddCircle L), 0) / 2
    ring
  have heqLp : Mul lam (D2 u) + T eta = T (w j t) := by
    rw [hrLp]
    apply Lp.ext
    filter_upwards [hMul lam (ContinuousMap.toLp 2 haarAddCircle ℝ r),
      ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) r,
      ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) eta,
      ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (w j t),
      Lp.coeFn_add (Mul lam (ContinuousMap.toLp 2 haarAddCircle ℝ r)) (T eta)]
      with z hMz hrz hetaz hwz hout
    rw [hout, Pi.add_apply, hMz, hrz, hetaz, hwz]
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    change lam (x : AddCircle L) (r (x : AddCircle L)) + eta (x : AddCircle L) = _
    rw [hwval j t ht x, hlabel]
  have hprod : ‖Mul lam (D2 u)‖ ≤ (A : ℝ) / 2 * (‖D2‖ * C) := by
    calc
      _ ≤ ‖Mul‖ * ‖lam‖ * ‖D2 u‖ := Mul.le_opNorm₂ _ _
      _ ≤ (1 * ((A : ℝ) / 2)) * ‖D2 u‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hMulone hlamnorm (norm_nonneg lam) (by norm_num)) (norm_nonneg _)
      _ ≤ (A : ℝ) / 2 * (‖D2‖ * C) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_left (hD2 j ⟨t, ht⟩) (by positivity : 0 ≤ (A : ℝ) / 2)
  have hconst : ‖T eta‖ ≤ (A : ℝ) / 2 * P := by
    calc
      _ ≤ ‖T‖ * ‖eta‖ := T.le_opNorm eta
      _ ≤ 1 * ‖eta‖ := mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _)
      _ ≤ (A : ℝ) / 2 * P := by simpa only [one_mul] using hetanorm
  change ‖T (w j t)‖ ≤ _
  rw [← heqLp]
  exact (norm_add_le _ _).trans ((add_le_add hprod hconst).trans_eq (by ring))

end PoincareConjecture.M63
