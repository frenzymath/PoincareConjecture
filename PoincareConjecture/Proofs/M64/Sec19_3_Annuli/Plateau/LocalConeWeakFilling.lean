import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeApproximationEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeWeakDisk
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.DiskGreenWeakLimit











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness



theorem m64Periodic_tendstoUniformly
    {Y : Type*} [UniformSpace Y] {f : ℕ → ℝ → Y} {u : ℝ → Y}
    (hf : ∀ j, Function.Periodic (f j) curvePeriod) (hu : Function.Periodic u curvePeriod)
    (hlim : TendstoUniformlyOn f u atTop (Icc (0 : ℝ) curvePeriod)) :
    TendstoUniformly f u atTop := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  intro V hV
  filter_upwards [hlim V hV] with j hj
  intro x
  let y := toIcoMod hP 0 x
  have hy : y ∈ Icc (0 : ℝ) curvePeriod :=
    Ico_subset_Icc_self (toIcoMod_mem_Ico' hP x)
  have hfy : f j y = f j x := by
    simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
      ((hf j).zsmul (-toIcoDiv hP 0 x)) x
  have huy : u y = u x := by
    simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
      (hu.zsmul (-toIcoDiv hP 0 x)) x
  rw [← hfy, ← huy]
  exact hj y hy

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => ball (0 : LoopPlane) 1
local notation "mu" => volume.restrict S
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)




structure M64ObservedConeDisk (e : M → E) (gamma : ℝ → M) where
  map : LoopPlane → M
  continuous : Continuous map
  boundary : ∀ x, map (angularPoint x) = gamma x
  inner : ∀ z : LoopPlane, ‖z‖ ≤ 1 / 2 → map z = gamma 0
  observed_memLp : MemLp (e ∘ map) 2 mu
  column : Fin 2 → Lp E 2 mu
  tangent : ∀ i, ∀ᵐ p ∂mu, column i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (map p))
  weak_partial : ∀ i a, HasWeakPartialDeriv i
    (fun p => column i p a) (fun p => e (map p) a) S
  green : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
    (∫ p in S, phi p • column i p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (map p)) =
        ∫ t in Icc (-Real.pi) Real.pi,
          angularPoint t i • (phi (angularPoint t) • e (gamma t))
  approximation : ∃ f : ℕ → LoopPlane → E, (∀ j, ContDiff ℝ 1 (f j)) ∧
    TendstoUniformly (fun j t => f j (angularPoint t)) (e ∘ gamma) atTop ∧
    ∃ (hu : ∀ j, MemLp (f j) 2 mu)
      (hD : ∀ j i, MemLp (fun p => fderiv ℝ (f j) p (EuclideanSpace.single i 1)) 2 mu),
      Tendsto (fun j => (hu j).toLp (f j)) atTop (𝓝 (observed_memLp.toLp (e ∘ map))) ∧
      ∀ i, WeakConverges
        (fun j => (hD j i).toLp (fun p => fderiv ℝ (f j) p (EuclideanSpace.single i 1)))
        (column i)

namespace M64ObservedConeDisk

variable {e : M → EuclideanSpace ℝ (Fin m)} {gamma : ℝ → M}



def energy (B : M → E →L[ℝ] E →L[ℝ] ℝ) (A : M64ObservedConeDisk (n := n) e gamma) : ℝ :=
  ∫ p in S, (B (A.map p) (A.column 0 p) (A.column 0 p) +
    B (A.map p) (A.column 1 p) (A.column 1 p)) / 2



theorem column_energy_integrable
    (A : M64ObservedConeDisk (n := n) e gamma)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K) (i : Fin 2) :
    IntegrableOn (fun p => B (A.map p) (A.column i p) (A.column i p)) S volume := by
  have hcoef := (hB.comp A.continuous).aestronglyMeasurable (μ := mu)
  have hc : Continuous (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × E => q.1 q.2 q.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  have hm := hc.comp_aestronglyMeasurable (hcoef.prodMk (Lp.aestronglyMeasurable (A.column i)))
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (A.column i))).mp (Lp.memLp (A.column i))
  apply (hi.const_mul K).mono' hm
  filter_upwards [] with p
  change ‖B (A.map p) (A.column i p) (A.column i p)‖ ≤ K * ‖A.column i p‖ ^ 2
  have hop := (B (A.map p)).le_opNorm₂ (A.column i p) (A.column i p)
  have hmul := mul_le_mul_of_nonneg_right (hb (A.map p)) (sq_nonneg ‖A.column i p‖)
  nlinarith



theorem energy_le_column_bound
    (A : M64ObservedConeDisk (n := n) e gamma)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K C : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hC : ∀ i, ‖A.column i‖ ^ 2 ≤ C) : A.energy B ≤ K * C := by
  have hi (i : Fin 2) : IntegrableOn (fun p => ‖A.column i p‖ ^ 2) S volume :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (A.column i))).mp (Lp.memLp (A.column i))
  have hbcol (i : Fin 2) :
      (∫ p in S, B (A.map p) (A.column i p) (A.column i p)) ≤ K * C := by
    calc
      _ ≤ ∫ p in S, K * ‖A.column i p‖ ^ 2 := by
        apply integral_mono (A.column_energy_integrable B hB hb i) ((hi i).const_mul K)
        intro p
        have hop := (B (A.map p)).le_opNorm₂ (A.column i p) (A.column i p)
        have hmul := mul_le_mul_of_nonneg_right (hb (A.map p)) (sq_nonneg ‖A.column i p‖)
        rw [Real.norm_eq_abs] at hop
        nlinarith [le_abs_self (B (A.map p) (A.column i p) (A.column i p))]
      _ = K * ‖A.column i‖ ^ 2 := by
        rw [integral_const_mul, ← LpFiniteCoordinatesNative.l2_norm_sq]
      _ ≤ K * C := mul_le_mul_of_nonneg_left (hC i) hK
  rw [energy, integral_div,
    integral_add (A.column_energy_integrable B hB hb 0)
      (A.column_energy_integrable B hB hb 1)]
  linarith [hbcol 0, hbcol 1]

end M64ObservedConeDisk

variable [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]



theorem m64ChartReadable_local_H1_cone
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (U : Set M) (C : ℝ), IsOpen U ∧ p ∈ U ∧ 0 ≤ C ∧
      ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
        (∀ x, gamma x ∈ U) → ∀ (w : ℕ → ℝ → E),
          (∀ j, ContDiff ℝ 1 (w j)) → (∀ j, Function.Periodic (w j) curvePeriod) →
          TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
          ∀ v : ℝ → E, MemLp v 2 circleMu →
            Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
              ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0) →
            ∃ A : M64ObservedConeDisk (n := n) e gamma,
              ∀ i, ‖A.column i‖ ^ 2 ≤ C * ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2 := by
  obtain ⟨U, C, hU, hp, hC, hcone⟩ :=
    m64ChartReadable_local_cone_approximation_uniform g isCompact_univ e he hread p
  obtain ⟨Q, hQ, hextract⟩ := m64ContinuousDisk_observed_weak_columns g e he hread
  refine ⟨U, Q * C, hU, hp, mul_nonneg hQ hC, ?_⟩
  intro gamma hgamma hgammaP hgammaU w hw hwP hlim v hv hder
  obtain ⟨k0, F, f, hF, hboundary, hinner, hf, hpoint, htrace, henergy⟩ :=
    hcone gamma hgamma hgammaP hgammaU w hw hwP hlim v hv
  let E0 := ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2
  let b := fun j => C * ((∫ x in Icc (0 : ℝ) curvePeriod,
    ‖deriv (w (j + k0)) x - v x‖ ^ 2) + E0)
  have hb : Tendsto b atTop (𝓝 (C * E0)) := by
    simpa only [b, zero_add, Function.comp_def] using
      (((hder.comp (tendsto_add_atTop_nat k0)).add_const E0).const_mul C)
  obtain ⟨hu, hFlp, hD, k, W, hk, hstrong, hweak, htangent, hpartial, hnorm⟩ :=
    hextract f hf F hF hpoint b (C * E0) hb henergy
  have hangle : Function.Periodic angularPoint curvePeriod := by
    intro x
    ext i
    fin_cases i <;> simp [angularPoint, curvePeriod]
  have htraceall := m64Periodic_tendstoUniformly
    (fun j x => congrArg (fun z => e (f j z)) (hangle x))
    (fun x => congrArg e (hgammaP x)) htrace
  have htracek : TendstoUniformly (fun j x => e (f (k j) (angularPoint x)))
      (e ∘ gamma) atTop := fun V hV => hk.tendsto_atTop.eventually (htraceall V hV)
  let A : M64ObservedConeDisk (n := n) e gamma := {
    map := F
    continuous := hF
    boundary := hboundary
    inner := hinner
    observed_memLp := hFlp
    column := W
    tangent := htangent
    weak_partial := hpartial
    green := by
      intro phi hphi i
      have hgreen := m64Disk_green_of_weak_limits (0 : LoopPlane) (by norm_num : 0 < (1 : ℝ))
        (fun j => e ∘ f (k j)) (fun j => contMDiff_iff_contDiff.mp (he.comp (hf (k j))))
        (fun j => (hu (k j)).toLp (e ∘ f (k j)))
        (fun j => (hD (k j) i).toLp
          (fun p => fderiv ℝ (e ∘ f (k j)) p (EuclideanSpace.single i 1)))
        (hFlp.toLp (e ∘ F)) (W i)
        (fun L => (L.continuous.tendsto _).comp hstrong) (hweak i) i
        (fun j => (hu (k j)).coeFn_toLp) (fun j => (hD (k j) i).coeFn_toLp)
        (e ∘ gamma) (by
          simpa +instances only [one_smul, zero_add, Function.comp_def] using!
            htracek.tendstoUniformlyOn)
        phi hphi
      have hrep : (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) •
          hFlp.toLp (e ∘ F) p) =
          ∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (F p) :=
        integral_congr_ae (hFlp.coeFn_toLp.mono fun p hp => congrArg
          (fun z : E => fderiv ℝ phi p (EuclideanSpace.single i 1) • z) hp)
      simpa only [hrep, one_smul, zero_add, Function.comp_apply] using hgreen
    approximation := ⟨fun j => e ∘ f (k j),
      fun j => contMDiff_iff_contDiff.mp (he.comp (hf (k j))), htracek,
      fun j => hu (k j), fun j i => hD (k j) i, hstrong, hweak⟩ }
  refine ⟨A, fun i => ?_⟩
  exact (hnorm i).trans_eq (by dsimp only [E0]; ring)

end PoincareConjecture
