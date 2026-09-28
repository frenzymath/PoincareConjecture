import PoincareConjecture.Proofs.M03.Existence.NativeDirectionalProductNative
import PoincareConjecture.Proofs.M03.Existence.ParsevalChartDirectionalNative
import PoincareConjecture.Proofs.M03.Existence.NativeChartScalarLocalization
import PoincareConjecture.Proofs.M03.Existence.ChartPullbackEnergyNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanMollificationNative









set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped Manifold ContDiff Bundle Topology ENNReal

noncomputable section

universe u v

namespace PoincareConjecture.NativeChartGradientEnergyNative

open TensorProbeNative NativeChartScalarLocalization ChartLpNative EuclideanMollificationNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type v} [Fintype iota]

local notation "E" => EuclideanSpace ℝ (Fin n)


theorem cutoff_chart_gradient_sq_le (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g.inner x (F i x) v • F i x) = v)
    (p : M) {ψ f : M → ℝ}
    (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hψbound : ∀ x, |ψ x| ≤ 1)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hψzero : ∀ x ∉ K, ψ x = 0) {C₀ B : ℝ} (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B)
    (hcoeff : ∀ (a : Fin n) (i : iota) (z : E), z ∈ chartAt E p '' K →
      |chartParsevalCoefficient g F p a i z| ≤ C₀)
    (hDψ : ∀ (i : iota) (x : M), |scalarDirectional (F i) ψ x| ≤ B) (z : E) :
    (∑ a : Fin n,
      (fderiv ℝ (chartScalar p (fun x => ψ x * f x)) z (EuclideanSpace.single a 1)) ^ 2) ≤
      (n : ℝ) * (Fintype.card iota : ℝ) * C₀ ^ 2 *
        (2 * (∑ i, scalarDirectional (F i) f ((chartAt E p).symm z) ^ 2) +
          2 * (Fintype.card iota : ℝ) * B ^ 2 * f ((chartAt E p).symm z) ^ 2) := by
  classical
  have hprod : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => ψ x * f x) := hψ.mul hf
  have hprodzero : ∀ x ∉ K, ψ x * f x = 0 := by
    intro x hx
    rw [hψzero x hx, zero_mul]
  by_cases hzK : z ∈ chartAt E p '' K
  · have hzt : z ∈ (chartAt E p).target := by
      obtain ⟨x, hx, rfl⟩ := hzK
      exact (chartAt E p).map_source (hKs hx)
    rw [fderiv_chartScalar_of_mem p _ hzt]
    have hcoord := coordinate_gradient_sq_le g F hF p hprod hzt hC₀
      (fun a i => hcoeff a i z hzK)
    simp only [PiLp.basisFun_apply] at hcoord
    apply hcoord.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact directional_energy_mul_le F
      ((hψ _).mdifferentiableAt (by simp)) ((hf _).mdifferentiableAt (by simp))
      (hψbound _) hB (fun i => hDψ i _)
  · rw [fderiv_chartScalar_of_notMem p hK hKs hprodzero hzK]
    simp only [ContinuousLinearMap.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero]
    positivity

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]


theorem exists_cutoff_chart_gradientEnergy_bound (g : RiemannianMetric n M)
    (F : iota → SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ i, g.inner x (F i x) v • F i x) = v)
    (p : M) {ψ : M → ℝ} (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ)
    (hψbound : ∀ x, |ψ x| ≤ 1)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).source)
    (hψzero : ∀ x ∉ K, ψ x = 0)
    {A : Set E} (hA : MeasurableSet A) (hAt : A ⊆ (chartAt E p).target)
    (hKA : chartAt E p '' K ⊆ A) {μ : Measure M} {c : ℝ} (hc : 0 < c)
    (hdom : ENNReal.ofReal c • (volume.restrict A).map (chartAt E p).symm ≤ μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
      (hfLp : MemLp f 2 μ) (hDfLp : ∀ i, MemLp (scalarDirectional (F i) f) 2 μ),
      gradientEnergy (n := n) (chartScalar (n := n) p (fun x => ψ x * f x)) ≤
        C * (‖hfLp.toLp f‖ ^ 2 +
          ∑ i, ‖(hDfLp i).toLp (scalarDirectional (F i) f)‖ ^ 2) := by
  classical
  let e : OpenPartialHomeomorph M E := chartAt E p
  have himage : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have himageTarget : e '' K ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hKs hx)
  obtain ⟨C₀, hC₀, hcoeff⟩ := exists_chartParsevalCoefficient_bound g F p himage himageTarget
  obtain ⟨B, hB, hDψ⟩ := exists_scalarDirectional_bound F hψ
  let L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (volume.restrict A) :=
    chartPullbackL2 e hA hAt hc hdom
  let Q : ℝ := (n : ℝ) * (Fintype.card iota : ℝ) * C₀ ^ 2
  let H : ℝ := (Fintype.card iota : ℝ) * B ^ 2
  let N : ℝ := ‖L‖ ^ 2
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hN : 0 ≤ N := sq_nonneg _
  refine ⟨Q * (2 * (1 + H) * N), mul_nonneg hQ (by positivity), ?_⟩
  intro f hf hfLp hDfLp
  let q : E → ℝ := chartScalar p (fun x => ψ x * f x)
  let X : ℝ := ‖hfLp.toLp f‖ ^ 2
  let Y : ℝ := ∑ i, ‖(hDfLp i).toLp (scalarDirectional (F i) f)‖ ^ 2
  have hX : 0 ≤ X := sq_nonneg _
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hprod : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => ψ x * f x) := hψ.mul hf
  have hprodzero : ∀ x ∉ K, ψ x * f x = 0 := by
    intro x hx
    rw [hψzero x hx, zero_mul]
  have hcoord (a : Fin n) :
      MemLp (fun z => fderiv ℝ q z (EuclideanSpace.single a 1)) 2 volume :=
    chartScalar_coordinate_memLp p hprod hK hKs hprodzero a
  have hleftI : Integrable
      (fun z => ∑ a : Fin n, (fderiv ℝ q z (EuclideanSpace.single a 1)) ^ 2) volume :=
    integrable_finsetSum Finset.univ (fun a _ => (hcoord a).integrable_sq)
  have hvalueI : Integrable (fun z => f (e.symm z) ^ 2) (volume.restrict A) :=
    (chartPullback_memLp e hA hAt hc hdom hfLp).integrable_sq
  have hderivI (i : iota) :
      Integrable (fun z => scalarDirectional (F i) f (e.symm z) ^ 2) (volume.restrict A) :=
    (chartPullback_memLp e hA hAt hc hdom (hDfLp i)).integrable_sq
  have hsumI : Integrable
      (fun z => ∑ i, scalarDirectional (F i) f (e.symm z) ^ 2) (volume.restrict A) :=
    integrable_finsetSum Finset.univ (fun i _ => hderivI i)
  have hrhsI : Integrable
      (fun z => Q * (2 * (∑ i, scalarDirectional (F i) f (e.symm z) ^ 2) +
        2 * H * f (e.symm z) ^ 2)) (volume.restrict A) :=
    ((hsumI.const_mul 2).add (hvalueI.const_mul (2 * H))).const_mul Q
  have hpoint (z : E) :
      (∑ a : Fin n, (fderiv ℝ q z (EuclideanSpace.single a 1)) ^ 2) ≤
        Q * (2 * (∑ i, scalarDirectional (F i) f (e.symm z) ^ 2) +
          2 * H * f (e.symm z) ^ 2) := by
    simpa only [Q, H, mul_assoc] using
      cutoff_chart_gradient_sq_le g F hF p hψ hf hψbound hK hKs hψzero hC₀ hB hcoeff hDψ z
  have hzero (z : E) (hz : z ∉ A) :
      (∑ a : Fin n, (fderiv ℝ q z (EuclideanSpace.single a 1)) ^ 2) = 0 := by
    have hzK : z ∉ e '' K := fun hzK => hz (hKA hzK)
    have hd : fderiv ℝ q z = 0 := fderiv_chartScalar_of_notMem p hK hKs hprodzero hzK
    simp only [hd, ContinuousLinearMap.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero]
  have heq : gradientEnergy q =
      ∫ z in A, ∑ a : Fin n, (fderiv ℝ q z (EuclideanSpace.single a 1)) ^ 2 := by
    unfold gradientEnergy
    rw [← integral_finsetSum Finset.univ (fun a _ => (hcoord a).integrable_sq)]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hfirst : gradientEnergy q ≤
      Q * (2 * (∑ i, ∫ z in A, scalarDirectional (F i) f (e.symm z) ^ 2) +
        2 * H * ∫ z in A, f (e.symm z) ^ 2) := by
    rw [heq]
    calc
      _ ≤ ∫ z in A, Q * (2 * (∑ i, scalarDirectional (F i) f (e.symm z) ^ 2) +
          2 * H * f (e.symm z) ^ 2) := integral_mono hleftI.restrict hrhsI hpoint
      _ = _ := by
        rw [integral_const_mul, integral_add (hsumI.const_mul 2) (hvalueI.const_mul (2 * H)),
          integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ (fun i _ => hderivI i)]
  have hvalueBound : (∫ z in A, f (e.symm z) ^ 2) ≤ N * X :=
    chartPullback_integral_sq_le e hA hAt hc hdom hfLp
  have hsumBound : (∑ i, ∫ z in A, scalarDirectional (F i) f (e.symm z) ^ 2) ≤ N * Y := by
    calc
      _ ≤ ∑ i, N * ‖(hDfLp i).toLp (scalarDirectional (F i) f)‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => chartPullback_integral_sq_le e hA hAt hc hdom (hDfLp i))
      _ = _ := (Finset.mul_sum Finset.univ _ N).symm
  have hmiddle : gradientEnergy q ≤ Q * (2 * (N * Y) + 2 * H * (N * X)) :=
    hfirst.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hsumBound (by norm_num))
        (mul_le_mul_of_nonneg_left hvalueBound (mul_nonneg (by norm_num) hH))) hQ)
  calc
    gradientEnergy q ≤ Q * (2 * (N * Y) + 2 * H * (N * X)) := hmiddle
    _ ≤ Q * (2 * (1 + H) * N * (X + Y)) := by
      apply mul_le_mul_of_nonneg_left _ hQ
      nlinarith [mul_nonneg hN hX, mul_nonneg hH (mul_nonneg hN hY)]
    _ = _ := by
      change Q * (2 * (1 + H) * N * (X + Y)) = (Q * (2 * (1 + H) * N)) * (X + Y)
      ring

end PoincareConjecture.NativeChartGradientEnergyNative
