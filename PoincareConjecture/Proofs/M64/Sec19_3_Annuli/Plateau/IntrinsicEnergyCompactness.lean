import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FixedBoundarySobolevLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedMetric
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MovingQuadraticLiminf
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

private theorem bounded_form_integrable
    (B : LoopPlane → E →L[ℝ] E →L[ℝ] ℝ) (hB : AEStronglyMeasurable B mu)
    {K : ℝ} (hb : ∀ p, ‖B p‖ ≤ K) (u : Lp E 2 mu) :
    Integrable (fun p => B p (u p) (u p)) mu := by
  have hc : Continuous (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × E => q.1 q.2 q.2) :=
    (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
  have hm := hc.comp_aestronglyMeasurable (hB.prodMk (Lp.aestronglyMeasurable u))
  have hi : Integrable (fun p => K * ‖u p‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
      |>.const_mul K
  apply hi.mono' hm
  exact Eventually.of_forall fun p => by
    have hh := (B p).le_opNorm₂ (u p) (u p)
    have hs := mul_le_mul_of_nonneg_right (hb p) (sq_nonneg ‖u p‖)
    nlinarith

omit [T2Space M] in
private theorem intrinsic_energy_le_liminf
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in S, m60EnergyDensity g (f j) p) ≤ C)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    (hgram : ∀ j p i l, B (f j p)
      (fderiv ℝ (e ∘ f j) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (fderiv ℝ (e ∘ f j) p (EuclideanSpace.basisFun (Fin 2) ℝ l)) =
        m60AreaGram g (f j) p i l)
    (v : LoopPlane → M) (V : Fin 2 → Lp E 2 mu)
    (hV : ∀ j i, MemLp (fun p => fderiv ℝ (e ∘ f j) p
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 mu)
    (hweak : ∀ i, WeakConverges (fun j => (hV j i).toLp
      (fun p => fderiv ℝ (e ∘ f j) p (EuclideanSpace.basisFun (Fin 2) ℝ i))) (V i))
    (hlim : ∀ᵐ p ∂mu, Tendsto (fun j => f j p) atTop (𝓝 (v p))) :
    (∫ p in S, (B (v p) (V 0 p) (V 0 p) + B (v p) (V 1 p) (V 1 p)) / 2) ≤
      liminf (fun j => ∫ p in S, m60EnergyDensity g (f j) p) atTop := by
  let d := fun j i p => fderiv ℝ (e ∘ f j) p (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let Q := fun j p => (1 / 2 : ℝ) • B (f j p)
  let Q0 := fun p => (1 / 2 : ℝ) • B (v p)
  let q := fun j i => ∫ p in S, Q j p (d j i p) (d j i p)
  have hscale (p : M) : ‖(1 / 2 : ℝ) • B p‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro w
    change ‖(1 / 2 : ℝ) • B p w‖ ≤ K * ‖w‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
    have hh := (B p).le_opNorm w
    have hs := mul_le_mul_of_nonneg_right (hb p) (norm_nonneg w)
    have hn := mul_nonneg hK (norm_nonneg w)
    linarith
  have hQ (j : ℕ) : AEStronglyMeasurable (Q j) mu :=
    ((continuous_const (y := (1 / 2 : ℝ))).smul (hB.comp (hf j).continuous)).aestronglyMeasurable
  have hQlim : ∀ᵐ p ∂mu, Tendsto (fun j => Q j p) atTop (𝓝 (Q0 p)) := by
    filter_upwards [hlim] with p hp
    exact tendsto_const_nhds.smul ((hB.tendsto (v p)).comp hp)
  have hQ0 : AEStronglyMeasurable Q0 mu := aestronglyMeasurable_of_tendsto_ae atTop hQ hQlim
  have hE (j : ℕ) : IntegrableOn (m60EnergyDensity g (f j)) S :=
    (m60EnergyDensity_continuous g (hf j)).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hdcont (j : ℕ) (i : Fin 2) : Continuous (d j i) :=
    ((contMDiff_iff_contDiff.mp (he.comp (hf j))).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hD (j : ℕ) (i : Fin 2) : IntegrableOn (fun p => ‖d j i p‖ ^ 2) S :=
    ((hdcont j i).norm.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  obtain ⟨A, hA0, hA⟩ := M60.exists_observed_derivative_energy_bound g e he
  have hnorm (j : ℕ) (i : Fin 2) : ‖(hV j i).toLp (d j i)‖ ≤ Real.sqrt (max (A * C) 0) := by
    have hs : ‖(hV j i).toLp (d j i)‖ ^ 2 ≤ A * C := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
      calc
        _ = ∫ p in S, ‖d j i p‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [(hV j i).coeFn_toLp] with p hp
          rw [hp]
        _ ≤ ∫ p in S, A * m60EnergyDensity g (f j) p :=
          integral_mono_ae (hD j i) ((hE j).const_mul A)
            (Eventually.of_forall fun p => hA (f j) (hf j) p i)
        _ = A * ∫ p in S, m60EnergyDensity g (f j) p := integral_const_mul _ _
        _ ≤ A * C := mul_le_mul_of_nonneg_left (hC j) hA0
    have hr := Real.sq_sqrt (le_max_right (A * C) 0)
    have hr0 := Real.sqrt_nonneg (max (A * C) 0)
    have hmax := le_max_left (A * C) 0
    nlinarith [norm_nonneg ((hV j i).toLp (d j i))]
  have hqi (j : ℕ) (i : Fin 2) : IntegrableOn (fun p => Q j p (d j i p) (d j i p)) S :=
    ((((continuous_const (y := (1 / 2 : ℝ))).smul (hB.comp (hf j).continuous)).clm_apply
      (hdcont j i)).clm_apply
      (hdcont j i)).continuousOn.integrableOn_compact m64AnnulusDomain_isCompact
        |>.mono_set interior_subset
  have hq0i (i : Fin 2) : Integrable (fun p => Q0 p (V i p) (V i p)) mu :=
    bounded_form_integrable Q0 hQ0 (fun p => hscale (v p)) (V i)
  have hcol (i : Fin 2) : (∫ p in S, Q0 p (V i p) (V i p)) ≤ liminf (fun j => q j i) atTop := by
    have hh := m64MovingQuadratic_le_liminf Q Q0 hQ hQ0 hK
      (fun j => Eventually.of_forall fun p => hscale (f j p)) hQlim
      (fun j => Eventually.of_forall fun p w => by
        change 0 ≤ (1 / 2 : ℝ) * B (f j p) w w
        exact mul_nonneg (by norm_num) (hpos _ _))
      (fun j => Eventually.of_forall fun p w z => by
        change (1 / 2 : ℝ) * B (f j p) w z = (1 / 2 : ℝ) * B (f j p) z w
        rw [hsymm]) (hweak i) (fun j => hnorm j i)
    have heq (j : ℕ) :
        (∫ p in S, Q j p ((hV j i).toLp (d j i) p) ((hV j i).toLp (d j i) p)) = q j i := by
      apply integral_congr_ae
      filter_upwards [(hV j i).coeFn_toLp] with p hp
      rw [hp]
    change (∫ p in S, Q0 p (V i p) (V i p)) ≤ liminf
      (fun j => ∫ p in S,
        Q j p ((hV j i).toLp (d j i) p) ((hV j i).toLp (d j i) p)) atTop at hh
    simpa only [heq] using hh
  have hqnonneg (j : ℕ) (i : Fin 2) : 0 ≤ q j i := integral_nonneg fun p =>
    mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (hpos _ _)
  have hqsum (j : ℕ) : q j 0 + q j 1 = ∫ p in S, m60EnergyDensity g (f j) p := by
    rw [← integral_add (hqi j 0) (hqi j 1)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      dsimp only [Q, d]
      simp only [smul_apply, smul_eq_mul, hgram, m60EnergyDensity, Matrix.trace_fin_two]
      ring
  have hqbound (j : ℕ) (i : Fin 2) : q j i ≤ C := by
    fin_cases i
    · change q j 0 ≤ C
      linarith [hC j, hqsum j, hqnonneg j 1]
    · change q j 1 ≤ C
      linarith [hC j, hqsum j, hqnonneg j 0]
  have hlow (i : Fin 2) : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop (fun j => q j i) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun j => hqnonneg j i)
  have hupp (i : Fin 2) : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop (fun j => q j i) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun j => hqbound j i)
  calc
    _ = (∫ p in S, Q0 p (V 0 p) (V 0 p)) + ∫ p in S, Q0 p (V 1 p) (V 1 p) := by
      rw [← integral_add (hq0i 0) (hq0i 1)]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp only [Q0]
        simp only [smul_apply, smul_eq_mul]
        ring
    _ ≤ liminf (fun j => q j 0) atTop + liminf (fun j => q j 1) atTop :=
      add_le_add (hcol 0) (hcol 1)
    _ ≤ liminf (fun j => q j 0 + q j 1) atTop :=
      le_liminf_add (hlow 0) (hupp 0) (hlow 1) (hupp 1).isCoboundedUnder_ge
    _ = _ := by simp only [hqsum]

theorem m64Annulus_intrinsic_sobolev_subsequence
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in S, m60EnergyDensity g (f j) p) ≤ C)
    (c0 c1 : ℝ → M)
    (h0 : ∀ j x, f j (annulusPoint x 0) = c0 x)
    (h1 : ∀ j x, f j (annulusPoint x 1) = c1 x) :
    ∃ (B : M → E →L[ℝ] E →L[ℝ] ℝ) (K : ℝ) (k : ℕ → ℕ) (v : LoopPlane → M)
      (u : Lp E 2 mu) (V : Fin 2 → Lp E 2 mu)
      (hU : ∀ j, MemLp (e ∘ f (k j)) 2 mu)
      (hV : ∀ j i, MemLp (fun p => fderiv ℝ (e ∘ f (k j)) p
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 mu),
      Continuous B ∧ 0 ≤ K ∧ (∀ q, ‖B q‖ ≤ K) ∧
      (∀ q w, 0 ≤ B q w w) ∧ (∀ q w z, B q w z = B q z w) ∧
      (∀ (a : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 a → ∀ p i j,
        B (a p) (fderiv ℝ (e ∘ a) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ (e ∘ a) p (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
            m60AreaGram g a p i j) ∧
      StrictMono k ∧ Tendsto (fun j => (hU j).toLp (e ∘ f (k j))) atTop (𝓝 u) ∧
      (∀ i, WeakConverges (fun j => (hV j i).toLp
        (fun p => fderiv ℝ (e ∘ f (k j)) p (EuclideanSpace.basisFun (Fin 2) ℝ i))) (V i)) ∧
      (∀ᵐ p ∂mu, e (v p) = u p ∧ Tendsto (fun j => f (k j) p) atTop (𝓝 (v p))) ∧
      (∀ i (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ S →
        (∫ p in S, phi p • V i p) =
          -(∫ p in S, fderiv ℝ phi p (EuclideanSpace.basisFun (Fin 2) ℝ i) • u p)) ∧
      (∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi →
        (∫ p in S, phi p • V 1 p) +
          (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • u p) =
          ∫ x in Icc (0 : ℝ) curvePeriod,
            phi (annulusPoint x 1) • e (c1 x) - phi (annulusPoint x 0) • e (c0 x)) ∧
      (∫ p in S, (B (v p) (V 0 p) (V 0 p) + B (v p) (V 1 p) (V 1 p)) / 2) ≤
        liminf (fun j => ∫ p in S, m60EnergyDensity g (f (k j)) p) atTop := by
  obtain ⟨B, K, hB, hK, hb, hpos, hsymm, hgram⟩ :=
    m64ChartReadable_observed_metric g e he hread
  obtain ⟨k, v, u, V, hU, hV, hk, hstrong, hweak, hev, htest, htrace, -⟩ :=
    m64Annulus_fixed_boundary_sobolev_subsequence g e he hei f hf hC c0 c1 h0 h1
  refine ⟨B, K, k, v, u, V, hU, hV, hB, hK, hb, hpos, hsymm, hgram,
    hk, hstrong, hweak, hev, htest, htrace, ?_⟩
  exact intrinsic_energy_le_liminf g e he (fun j => f (k j)) (fun j => hf (k j))
    (fun j => hC (k j)) B hB hK hb hpos hsymm
    (fun j p i l => hgram (f (k j)) (hf (k j)) p i l) v V hV hweak
    (hev.mono fun _ hp => hp.2)

end PoincareConjecture
