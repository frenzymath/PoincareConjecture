import PoincareConjecture.Proofs.M03.Existence.DeTurckJetAffineNative
import PoincareConjecture.Proofs.M03.Existence.NativeTensorLaplacianNative
import PoincareConjecture.Proofs.M03.Existence.ParsevalMetricTraceNative









set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.DeTurckGeneratorCorrectionNative

open TensorProbeNative ChartMeasureNative ParsevalTensorNative DeTurckNative
  DeTurckCompatibleJetNative DeTurckJetCoordinatesNative DeTurckJetAffineNative
  DeTurckInverseCompositionNative DeTurckQuasilinearEstimateNative

variable {n : ℕ} {M iota : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Fintype iota]
  (F : iota → SmoothField (n := n) (M := M))
  (charts : FiniteChartData (n := n) (M := M)) (g0 : RiemannianMetric n M)
  {base : M} {K : Set M} (C : Cutoffs (n := n) base K)

def frameCoefficient (i : Fin n) (s : iota) (x : M) : ℝ :=
  g0.inner x (F s x) (C.field i x)

theorem frameCoefficient_contMDiff (i : Fin n) (s : iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (frameCoefficient F g0 C i s) :=
  contMDiff_pairing (metricTensor g0) (F s) (C.field i)

def driftCoefficient (s : iota) (x : M) : ℝ :=
  charts.fieldDivergence (F s) x + ∑ a : iota, ∑ i : Fin n,
    scalarDirectional (F a) (dualCoefficient C g0 (F a) i) x *
      frameCoefficient F g0 C i s x

theorem driftCoefficient_contMDiff (s : iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (driftCoefficient F charts g0 C s) :=
  (charts.fieldDivergence_contMDiff (F s)).add
    (ContMDiff.sum (fun a _ => ContMDiff.sum (fun i _ =>
      (contMDiff_directional (dualCoefficient_contMDiff C g0 (F a) i) (F a)).mul
        (frameCoefficient_contMDiff F g0 C i s))))

def coframeCoefficient (i j : Fin n) (ab : iota × iota) : M → ℝ :=
  coframeComponent F g0 (C.field i) (C.field j) ab

theorem coframeCoefficient_contMDiff (i j : Fin n) (ab : iota × iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (coframeCoefficient F g0 C i j ab) :=
  (frameCoefficient_contMDiff F g0 C i ab.1).mul
    (frameCoefficient_contMDiff F g0 C j ab.2)

def zeroCoefficient (i j : Fin n) (ab : iota × iota) (x : M) : ℝ :=
  -scalarLaplacian F charts (coframeCoefficient F g0 C i j ab) x -
    ∑ s : iota, driftCoefficient F charts g0 C s x *
      scalarDirectional (F s) (coframeCoefficient F g0 C i j ab) x

theorem zeroCoefficient_contMDiff (i j : Fin n) (ab : iota × iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (zeroCoefficient F charts g0 C i j ab) :=
  (scalarLaplacian_contMDiff F charts (coframeCoefficient_contMDiff F g0 C i j ab)).neg.sub
    (ContMDiff.sum (fun s _ => (driftCoefficient_contMDiff F charts g0 C s).mul
      (contMDiff_directional (coframeCoefficient_contMDiff F g0 C i j ab) (F s))))

def firstCoefficient (i j : Fin n) (ab : iota × iota) (s : iota) (x : M) : ℝ :=
  2 * scalarDirectional (F s) (coframeCoefficient F g0 C i j ab) x -
    driftCoefficient F charts g0 C s x * coframeCoefficient F g0 C i j ab x

theorem firstCoefficient_contMDiff (i j : Fin n) (ab : iota × iota) (s : iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (firstCoefficient F charts g0 C i j ab s) :=
  (contMDiff_const.mul
    (contMDiff_directional (coframeCoefficient_contMDiff F g0 C i j ab) (F s))).sub
    ((driftCoefficient_contMDiff F charts g0 C s).mul
      (coframeCoefficient_contMDiff F g0 C i j ab))

def correctionEntry (i j : Fin n) (ab : iota × iota) (q : M → ℝ) (x : M) : ℝ :=
  zeroCoefficient F charts g0 C i j ab x * q x +
    ∑ s : iota, firstCoefficient F charts g0 C i j ab s x * scalarDirectional (F s) q x

theorem correctionEntry_contMDiff (i j : Fin n) (ab : iota × iota)
    {q : M → ℝ} (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (correctionEntry F charts g0 C i j ab q) :=
  ((zeroCoefficient_contMDiff F charts g0 C i j ab).mul hq).add
    (ContMDiff.sum (fun s _ => (firstCoefficient_contMDiff F charts g0 C i j ab s).mul
      (contMDiff_directional hq (F s))))

def generatorCorrection (h : SmoothTensor (n := n) (M := M)) (i j : Fin n) (x : M) : ℝ :=
  ∑ ab : iota × iota, correctionEntry F charts g0 C i j ab (scalarProbe F h ab) x

theorem generatorCorrection_contMDiff (h : SmoothTensor (n := n) (M := M)) (i j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (generatorCorrection F charts g0 C h i j) :=
  ContMDiff.sum (fun ab _ => correctionEntry_contMDiff F charts g0 C i j ab
    (scalarProbe_contMDiff F h ab))


def correctionWordTerms (i j : Fin n) (ab : iota × iota) :
    List iota → List (DirectionalTerm (n := n) (M := M) (iota := iota))
  | [] => by
      classical
      exact [⟨zeroCoefficient F charts g0 C i j ab,
        zeroCoefficient_contMDiff F charts g0 C i j ab, []⟩] ++
        Finset.univ.toList.map (fun s : iota =>
          ⟨firstCoefficient F charts g0 C i j ab s,
            firstCoefficient_contMDiff F charts g0 C i j ab s, [s]⟩)
  | s :: word => differentiateDirectionalTerms F s (correctionWordTerms i j ab word)

theorem correctionWordTerms_order (i j : Fin n) (ab : iota × iota) (word : List iota) :
    ∀ t ∈ correctionWordTerms F charts g0 C i j ab word, t.word.length ≤ word.length + 1 := by
  classical
  induction word with
  | nil =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have ht' := List.mem_singleton.mp ht
      subst t
      simp
    · obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
      simp
  | cons s word ih =>
    rw [correctionWordTerms]
    have h := differentiateDirectionalTerms_order F s
      (correctionWordTerms F charts g0 C i j ab word) ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem correctionWordTerms_eq (i j : Fin n) (ab : iota × iota) (word : List iota)
    {q : M → ℝ} (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) (x : M) :
    directionalTerms F (correctionWordTerms F charts g0 C i j ab word) q x =
      directionalWord F word (correctionEntry F charts g0 C i j ab q) x := by
  classical
  induction word generalizing x with
  | nil =>
    simp [correctionWordTerms, directionalTerms, correctionEntry,
      List.map_map, Function.comp_def, Finset.sum_map_toList, directionalWord]
  | cons s word ih =>
    rw [correctionWordTerms, directionalTerms_differentiate F s _ hq,
      directionalWord_cons]
    exact congrArg (fun f : M → ℝ => scalarDirectional (F s) f x) (funext ih)

theorem generatorCorrection_word (h : SmoothTensor (n := n) (M := M))
    (i j : Fin n) (word : List iota) (x : M) :
    directionalWord F word (generatorCorrection F charts g0 C h i j) x =
      ∑ ab : iota × iota,
        directionalTerms F (correctionWordTerms F charts g0 C i j ab word)
          (scalarProbe F h ab) x := by
  change directionalWord F word (fun y => ∑ ab : iota × iota,
    correctionEntry F charts g0 C i j ab (scalarProbe F h ab) y) x = _
  rw [directionalWord_sum Finset.univ F word _ (fun ab _ =>
    correctionEntry_contMDiff F charts g0 C i j ab (scalarProbe_contMDiff F h ab))]
  apply Finset.sum_congr rfl
  intro ab _
  exact (correctionWordTerms_eq F charts g0 C i j ab word
    (scalarProbe_contMDiff F h ab) x).symm

section CompletedCorrection

variable (μ : Measure M) [IsFiniteMeasure μ]

def correctionWordL2 {k : ℕ} (i j : Fin n) (word : List iota) (hw : word.length ≤ k) :
    NativeProbeL2 (iota := iota) μ (k + 1) →L[ℝ] Lp ℝ 2 μ :=
  ∑ ab : iota × iota,
    (termsL2 μ (correctionWordTerms F charts g0 C i j ab word)
      (fun t ht => (correctionWordTerms_order F charts g0 C i j ab word t ht).trans
        (Nat.add_le_add_right hw 1))).comp (ContinuousLinearMap.proj ab)

theorem correctionWordL2_ae_eq {k : ℕ} (i j : Fin n) (word : List iota)
    (hw : word.length ≤ k) (Q : NativeProbeL2 (iota := iota) μ (k + 1))
    (h : SmoothTensor (n := n) (M := M))
    (hQ : ∀ ab w (hw : w.length ≤ k + 1),
      Q ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (scalarProbe F h ab)) :
    correctionWordL2 F charts g0 C μ i j word hw Q =ᵐ[μ]
      directionalWord F word (generatorCorrection F charts g0 C h i j) := by
  let q (ab : iota × iota) : Lp ℝ 2 μ :=
    termsL2 μ (correctionWordTerms F charts g0 C i j ab word)
      (fun t ht => (correctionWordTerms_order F charts g0 C i j ab word t ht).trans
        (Nat.add_le_add_right hw 1)) (Q ab)
  have hq (ab : iota × iota) : q ab =ᵐ[μ]
      directionalTerms F (correctionWordTerms F charts g0 C i j ab word)
        (scalarProbe F h ab) :=
    termsL2_ae_eq F μ (correctionWordTerms F charts g0 C i j ab word)
      (fun t ht => (correctionWordTerms_order F charts g0 C i j ab word t ht).trans
        (Nat.add_le_add_right hw 1)) (Q ab) (scalarProbe F h ab) (hQ ab)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ q, ae_all_iff.mpr hq]
    with x hsum hterms
  simp only [correctionWordL2, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change (∑ ab : iota × iota, q ab) x = _
  rw [hsum]
  simp only [hterms]
  exact (generatorCorrection_word F charts g0 C h i j word x).symm

def correctionL2 (k : ℕ) : NativeProbeL2 (iota := iota) μ (k + 1) →L[ℝ]
    ((Fin n × Fin n) → WordIndex iota k → Lp ℝ 2 μ) :=
  ContinuousLinearMap.pi (fun ij => ContinuousLinearMap.pi (fun word =>
    correctionWordL2 F charts g0 C μ ij.1 ij.2 (List.ofFn word.2)
      (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ word.1.isLt)))

theorem correctionL2_ae_eq {k : ℕ} (Q : NativeProbeL2 (iota := iota) μ (k + 1))
    (h : SmoothTensor (n := n) (M := M))
    (hQ : ∀ ab w (hw : w.length ≤ k + 1),
      Q ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (scalarProbe F h ab))
    (i j : Fin n) (word : List iota) (hw : word.length ≤ k) :
    correctionL2 F charts g0 C μ k Q (i, j) (wordIndex word hw) =ᵐ[μ]
      directionalWord F word (generatorCorrection F charts g0 C h i j) := by
  simp only [correctionL2, ContinuousLinearMap.pi_apply, wordIndex_word]
  exact correctionWordL2_ae_eq F charts g0 C μ i j word hw Q h hQ

end CompletedCorrection

theorem dualCoefficient_eq_repr_of_cutoffs (V : SmoothField (n := n) (M := M))
    {x : M} (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) base).source)
    (heta : C.eta x = 1) (hzeta : C.zeta x = 1) (i : Fin n) :
    dualCoefficient C g0 V i x = (chartFrameBasis base x hx).repr (V x) i := by
  let b := chartFrameBasis base x hx
  have hfield (j : Fin n) : C.field j x = b j := by
    change C.zeta x • chartFrame base j x = b j
    rw [hzeta, one_smul]
    exact chartFrame_eq_basis base x hx j
  have hmatrix (j k : Fin n) : C.matrix g0 x j k = g0.inner x (b j) (b k) := by
    change C.eta x * g0.inner x (chartFrame base j x) (chartFrame base k x) +
      (1 - C.eta x) * (1 : Matrix (Fin n) (Fin n) ℝ) j k = _
    rw [heta]
    simp only [one_mul, sub_self, zero_mul, add_zero]
    rw [chartFrame_eq_basis base x hx j, chartFrame_eq_basis base x hx k]
  have hpair : (fun j => g0.inner x (C.field j x) (V x)) =
      (C.matrix g0 x).mulVec (fun k => b.repr (V x) k) := by
    funext j
    change g0.inner x (C.field j x) (V x) =
      ∑ k, C.matrix g0 x j k * b.repr (V x) k
    conv_lhs => rw [hfield j, ← b.sum_repr (V x)]
    simp only [map_sum, map_smul, smul_eq_mul, hmatrix]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hinv := (C.matrix g0 x).nonsing_inv_mul
    ((C.matrix g0 x).isUnit_iff_isUnit_det.mp (C.matrix_posDef g0 x).isUnit)
  change ((C.matrix g0 x)⁻¹.mulVec (fun j => g0.inner x (C.field j x) (V x))) i = _
  rw [hpair, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]


theorem exists_frame_neighborhood {x : M} (hx : x ∈ K) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ a y, y ∈ U →
      F a y = ∑ i, dualCoefficient C g0 (F a) i y • C.field i y := by
  have hnear : ∀ᶠ y in 𝓝 x, ∀ a,
      F a y = ∑ i, dualCoefficient C g0 (F a) i y • C.field i y := by
    filter_upwards [C.eta_one x hx, C.zeta_one x (C.mem_eta_support hx),
      (chartAt (EuclideanSpace ℝ (Fin n)) base).open_source.mem_nhds
        (C.eta_support (C.mem_eta_support hx))] with y heta hzeta hy
    intro a
    let b := chartFrameBasis base y hy
    calc
      _ = ∑ i, b.repr (F a y) i • b i := (b.sum_repr (F a y)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [dualCoefficient_eq_repr_of_cutoffs g0 C (F a) hy heta hzeta i]
        change b.repr (F a y) i • b i =
          b.repr (F a y) i • (C.zeta y • chartFrame base i y)
        rw [hzeta, Pi.one_apply, one_smul, chartFrame_eq_basis base y hy i]
  obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp hnear
  exact ⟨U, hUopen, hxU, fun a y hy => hU y hy a⟩

theorem sum_dualCoefficient_mul
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {x : M} (hx : x ∈ K) (i j : Fin n) :
    (∑ a, dualCoefficient C g0 (F a) i x * dualCoefficient C g0 (F a) j x) =
      (C.matrix g0 x)⁻¹ i j := by
  have hxU := C.eta_support (C.mem_eta_support hx)
  have hm : C.matrix g0 x = chartMetricCoefficients g0 base (extChartAt (𝓡 n) base x) := by
    rw [(C.matrix_eventuallyEq g0 (C.eta_one x hx)).eq_of_nhds]
    exact frameMetricJet_value_eq_chartMetricCoefficients g0 base hxU
  calc
    _ = ∑ a, (chartFrameBasis base x hxU).repr (F a x) i *
        (chartFrameBasis base x hxU).repr (F a x) j := by
      apply Finset.sum_congr rfl
      intro a _
      rw [dualCoefficient_eq_repr C g0 (F a) hx i, dualCoefficient_eq_repr C g0 (F a) hx j]
    _ = (chartMetricCoefficients g0 base (extChartAt (𝓡 n) base x))⁻¹ i j :=
      ParsevalFrameNative.chart_parseval_coordinates_eq_inverse_metric g0 F hF base hxU i j
    _ = _ := by rw [← hm]

theorem directional_frame_eq_native
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (i : Fin n) (f : M → ℝ) (x : M) :
    scalarDirectional (C.field i) f x =
      ∑ s, frameCoefficient F g0 C i s x * scalarDirectional (F s) f x := by
  change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (C.field i x) = _
  rw [← hF x (C.field i x), map_sum]
  simp only [map_smul, smul_eq_mul, frameCoefficient, scalarDirectional]


theorem scalarLaplacian_eq_principal_drift
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : x ∈ K) :
    scalarLaplacian F charts f x =
      -(∑ i : Fin n, ∑ j : Fin n,
        (C.matrix g0 x)⁻¹ i j * directionalWord C.field [i, j] f x) -
      ∑ s : iota, driftCoefficient F charts g0 C s x * scalarDirectional (F s) f x := by
  classical
  obtain ⟨U, hUopen, hxU, hframe⟩ := exists_frame_neighborhood F g0 C hx
  have hfirst (a : iota) (q : M → ℝ) : scalarDirectional (F a) q x =
      ∑ i, dualCoefficient C g0 (F a) i x * scalarDirectional (C.field i) q x := by
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) q x (F a x) = _
    rw [hframe a x hxU, map_sum]
    simp only [map_smul, smul_eq_mul, scalarDirectional]
  have hsecond (a : iota) : directionalWord F [a, a] f x =
      (∑ i : Fin n, ∑ j : Fin n,
        dualCoefficient C g0 (F a) i x * dualCoefficient C g0 (F a) j x *
          directionalWord C.field [i, j] f x) +
      ∑ i : Fin n, scalarDirectional (F a) (dualCoefficient C g0 (F a) i) x *
        scalarDirectional (C.field i) f x := by
    have h := second_derivative_eq_of_field_sum C.field
      (fun a y => F a y) (fun a i => dualCoefficient C g0 (F a) i) hUopen
      (fun a i => (dualCoefficient_contMDiff C g0 (F a) i).contMDiffOn)
      hframe hf a a hxU
    change directionalWord F [a, a] f x = _ at h
    rw [h]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, ← hfirst a (dualCoefficient C g0 (F a) j)]
  have htop :
      (∑ a : iota, ∑ i : Fin n, ∑ j : Fin n,
        dualCoefficient C g0 (F a) i x * dualCoefficient C g0 (F a) j x *
          directionalWord C.field [i, j] f x) =
        ∑ i : Fin n, ∑ j : Fin n,
          (C.matrix g0 x)⁻¹ i j * directionalWord C.field [i, j] f x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, sum_dualCoefficient_mul F g0 C hF hx i j]
  have hseconds : (∑ a : iota, directionalWord F [a, a] f x) =
      (∑ i : Fin n, ∑ j : Fin n,
        (C.matrix g0 x)⁻¹ i j * directionalWord C.field [i, j] f x) +
      ∑ a : iota, ∑ i : Fin n,
        scalarDirectional (F a) (dualCoefficient C g0 (F a) i) x *
          scalarDirectional (C.field i) f x := by
    simp_rw [hsecond]
    rw [Finset.sum_add_distrib, htop]
  have hcross :
      (∑ a : iota, ∑ i : Fin n,
        scalarDirectional (F a) (dualCoefficient C g0 (F a) i) x *
          scalarDirectional (C.field i) f x) =
      ∑ s : iota, (∑ a : iota, ∑ i : Fin n,
        scalarDirectional (F a) (dualCoefficient C g0 (F a) i) x *
          frameCoefficient F g0 C i s x) * scalarDirectional (F s) f x := by
    simp_rw [directional_frame_eq_native F g0 C hF, Finset.mul_sum]
    simp only [← mul_assoc, Finset.sum_mul]
    calc
      _ = ∑ a : iota, ∑ s : iota, ∑ i : Fin n,
          (scalarDirectional (F a) (dualCoefficient C g0 (F a) i) x *
            frameCoefficient F g0 C i s x) * scalarDirectional (F s) f x := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hbeta :
      (∑ s : iota, driftCoefficient F charts g0 C s x * scalarDirectional (F s) f x) =
      (∑ s : iota, charts.fieldDivergence (F s) x * scalarDirectional (F s) f x) +
      ∑ a : iota, ∑ i : Fin n,
        scalarDirectional (F a) (dualCoefficient C g0 (F a) i) x *
          scalarDirectional (C.field i) f x := by
    simp only [driftCoefficient, add_mul, Finset.sum_add_distrib]
    rw [hcross]
  have hraw : scalarLaplacian F charts f x =
      -(∑ a : iota, directionalWord F [a, a] f x) -
        ∑ s : iota, charts.fieldDivergence (F s) x * scalarDirectional (F s) f x := by
    simp only [scalarLaplacian, FiniteChartData.fieldAdjoint,
      directionalWord_cons, directionalWord_nil, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hraw, hseconds]
  linarith [hbeta]


theorem smoothTensorLaplacian_eq_principal_correction
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (h : SmoothTensor (n := n) (M := M)) (i j : Fin n) {x : M} (hx : x ∈ K) :
    smoothTensorLaplacian F charts g0 h x (C.field i x) (C.field j x) =
      -(∑ a : Fin n, ∑ b : Fin n, (C.matrix g0 x)⁻¹ a b *
        directionalWord C.field [a, b] (fun y => h y (C.field i y) (C.field j y)) x) +
      generatorCorrection F charts g0 C h i j x := by
  classical
  let c := coframeCoefficient F g0 C i j
  let q := scalarProbe F h
  let H : M → ℝ := fun y => h y (C.field i y) (C.field j y)
  have hc (ab : iota × iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (c ab) :=
    coframeCoefficient_contMDiff F g0 C i j ab
  have hq (ab : iota × iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q ab) :=
    scalarProbe_contMDiff F h ab
  have hH : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ H :=
    contMDiff_pairing h (C.field i) (C.field j)
  have hreconstruction : H = fun y => ∑ ab : iota × iota, c ab y * q ab y := by
    funext y
    have hid := congrArg (fun L => L (C.field i y) (C.field j y))
      (nativeDecode_probes g0 F hF h y)
    rw [nativeDecode_apply] at hid
    apply hid.symm.trans
    apply Finset.sum_congr rfl
    intro ab _
    change h y (F ab.1 y) (F ab.2 y) * g0.inner y (F ab.1 y) (C.field i y) *
      g0.inner y (F ab.2 y) (C.field j y) =
        (g0.inner y (F ab.1 y) (C.field i y) *
          g0.inner y (F ab.2 y) (C.field j y)) * h y (F ab.1 y) (F ab.2 y)
    ring
  have hderiv (s : iota) : scalarDirectional (F s) H x =
      ∑ ab : iota × iota, (c ab x * scalarDirectional (F s) (q ab) x +
        q ab x * scalarDirectional (F s) (c ab) x) := by
    rw [hreconstruction, scalarDirectional_finsetSum_smooth Finset.univ (F s)
      (fun ab y => c ab y * q ab y) (fun ab _ => (hc ab).mul (hq ab))]
    apply Finset.sum_congr rfl
    intro ab _
    exact scalarDirectional_mul (F s) ((hc ab).mdifferentiable (by simp) x)
      ((hq ab).mdifferentiable (by simp) x)
  have hdrift :
      (∑ s : iota, driftCoefficient F charts g0 C s x * scalarDirectional (F s) H x) =
      ∑ ab : iota × iota, ∑ s : iota, driftCoefficient F charts g0 C s x *
        (c ab x * scalarDirectional (F s) (q ab) x +
          q ab x * scalarDirectional (F s) (c ab) x) := by
    simp_rw [hderiv, Finset.mul_sum]
    exact Finset.sum_comm
  have hentry (ab : iota × iota) :
      correctionEntry F charts g0 C i j ab (q ab) x =
      -q ab x * scalarLaplacian F charts (c ab) x +
        2 * (∑ s : iota, scalarDirectional (F s) (c ab) x *
          scalarDirectional (F s) (q ab) x) -
        ∑ s : iota, driftCoefficient F charts g0 C s x *
          (c ab x * scalarDirectional (F s) (q ab) x +
            q ab x * scalarDirectional (F s) (c ab) x) := by
    calc
      _ = -q ab x * scalarLaplacian F charts (c ab) x +
          ∑ s : iota, ((2 * scalarDirectional (F s) (c ab) x -
            driftCoefficient F charts g0 C s x * c ab x) *
            scalarDirectional (F s) (q ab) x -
              (driftCoefficient F charts g0 C s x *
                scalarDirectional (F s) (c ab) x) * q ab x) := by
        change (-scalarLaplacian F charts (c ab) x -
          ∑ s : iota, driftCoefficient F charts g0 C s x *
            scalarDirectional (F s) (c ab) x) * q ab x +
          (∑ s : iota, (2 * scalarDirectional (F s) (c ab) x -
            driftCoefficient F charts g0 C s x * c ab x) *
              scalarDirectional (F s) (q ab) x) = _
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
      _ = -q ab x * scalarLaplacian F charts (c ab) x +
          ∑ s : iota, (2 * (scalarDirectional (F s) (c ab) x *
            scalarDirectional (F s) (q ab) x) -
            driftCoefficient F charts g0 C s x *
              (c ab x * scalarDirectional (F s) (q ab) x +
                q ab x * scalarDirectional (F s) (c ab) x)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  have hcorrection : generatorCorrection F charts g0 C h i j x =
      -(∑ ab : iota × iota, q ab x * scalarLaplacian F charts (c ab) x) +
        2 * (∑ ab : iota × iota, ∑ s : iota,
          scalarDirectional (F s) (c ab) x * scalarDirectional (F s) (q ab) x) -
        ∑ s : iota, driftCoefficient F charts g0 C s x * scalarDirectional (F s) H x := by
    change (∑ ab : iota × iota, correctionEntry F charts g0 C i j ab (q ab) x) = _
    simp_rw [hentry]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hdrift]
    simp only [neg_mul, Finset.sum_neg_distrib]
  have hcomponent := smoothTensorLaplacian_component F charts g0 hF h
    (C.field i) (C.field j) isOpen_univ (C.field i).contMDiff.contMDiffOn
      (C.field j).contMDiff.contMDiffOn (Set.mem_univ x)
  change smoothTensorLaplacian F charts g0 h x (C.field i x) (C.field j x) =
    scalarLaplacian F charts H x -
      (∑ ab : iota × iota, q ab x * scalarLaplacian F charts (c ab) x) +
      2 * (∑ ab : iota × iota, ∑ s : iota,
        scalarDirectional (F s) (c ab) x * scalarDirectional (F s) (q ab) x) at hcomponent
  rw [scalarLaplacian_eq_principal_drift F charts g0 C hF hH hx] at hcomponent
  rw [hcomponent, hcorrection]
  ring


theorem secondDifference_eq_component_word
    (g : RiemannianMetric n M) (h : SmoothTensor (n := n) (M := M))
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    {x : M} (hx : x ∈ K) (a b i j : Fin n) :
    C.secondDifference g0 g x a b i j = directionalWord C.field [a, b]
      (fun y => h y (C.field i y) (C.field j y)) x := by
  have hnear : (fun y => C.matrix g y i j - C.matrix g0 y i j) =ᶠ[𝓝 x]
      fun y => h y (C.field i y) (C.field j y) := by
    filter_upwards [C.matrix_eventuallyEq g (C.eta_one x hx),
      C.matrix_eventuallyEq g0 (C.eta_one x hx),
      C.field_eventuallyEq (C.zeta_one x (C.mem_eta_support hx)) i,
      C.field_eventuallyEq (C.zeta_one x (C.mem_eta_support hx)) j]
      with y hG hG0 hi hj
    rw [hG, hG0, hi, hj]
    change g.inner y (chartFrame base i y) (chartFrame base j y) -
      g0.inner y (chartFrame base i y) (chartFrame base j y) = _
    rw [hmetric]
    ring
  have hfirst : scalarDirectional (C.field b)
      (fun y => C.matrix g y i j - C.matrix g0 y i j) =
      fun y => scalarDirectional (C.field b) (fun z => C.matrix g z i j) y -
        scalarDirectional (C.field b) (fun z => C.matrix g0 z i j) y := by
    funext y
    exact scalarDirectional_sub (C.field b)
      ((C.matrix_entry_contMDiff g i j).mdifferentiable (by simp) y)
      ((C.matrix_entry_contMDiff g0 i j).mdifferentiable (by simp) y)
  have hsecond := scalarDirectional_sub (C.field a)
    (f := scalarDirectional (C.field b) (fun y => C.matrix g y i j))
    (q := scalarDirectional (C.field b) (fun y => C.matrix g0 y i j))
    ((contMDiff_directional (C.matrix_entry_contMDiff g i j) (C.field b)).mdifferentiable
      (by simp) x)
    ((contMDiff_directional (C.matrix_entry_contMDiff g0 i j) (C.field b)).mdifferentiable
      (by simp) x)
  change scalarDirectional (C.field a)
      (scalarDirectional (C.field b) (fun y => C.matrix g y i j)) x -
    scalarDirectional (C.field a)
      (scalarDirectional (C.field b) (fun y => C.matrix g0 y i j)) x = _
  exact hsecond.symm.trans
    ((congrArg (fun f : M → ℝ => scalarDirectional (C.field a) f x) hfirst.symm).trans
      (directionalWord_eventuallyEq C.field [a, b] hnear).eq_of_nhds)


theorem smoothResidualTensor_component
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M))
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    {x : M} (hx : x ∈ K) (i j : Fin n) :
    smoothResidualTensor F charts D B h x (C.field i x) (C.field j x) =
      C.residual g0 g x i j + generatorCorrection F charts g0 C h i j x := by
  have hfield (a : Fin n) : C.field a x = chartFrame base a x :=
    (C.field_eventuallyEq (C.zeta_one x (C.mem_eta_support hx)) a).eq_of_nhds
  have hprincipal : lowerJetContraction (C.jet g0 x).value⁻¹
      (C.secondDifference g0 g x) i j =
      ∑ a : Fin n, ∑ b : Fin n, (C.matrix g0 x)⁻¹ a b *
        directionalWord C.field [a, b] (fun y => h y (C.field i y) (C.field j y)) x := by
    change (∑ a : Fin n, ∑ b : Fin n, (C.matrix g0 x)⁻¹ a b *
      C.secondDifference g0 g x a b i j) = _
    simp_rw [secondDifference_eq_component_word g0 C g h hmetric hx]
  rw [smoothResidualTensor_apply, smoothCoreResidual,
    smoothTensorLaplacian_eq_principal_correction F charts g0 C hF h i j hx,
    C.residual_eq_intrinsic g0 g B D hx i j, hprincipal, hfield i, hfield j]
  ring

end PoincareConjecture.DeTurckGeneratorCorrectionNative

end
