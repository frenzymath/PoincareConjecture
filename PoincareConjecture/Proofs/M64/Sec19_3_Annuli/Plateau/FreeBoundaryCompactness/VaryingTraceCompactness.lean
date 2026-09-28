import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakClassCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.VaryingGreen

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)

private theorem varying_trace_tangent_closed
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℕ → ℝ → M}
    (A : ∀ j, M64ObservedWeakAnnulus (n := n) e (c0 j) (c1 j))
    (v : LoopPlane → M) (W : Lp E 2 mu) (i : Fin 2)
    (hweak : WeakConverges (fun j => (A j).column i) W)
    (hlim : ∀ᵐ p ∂mu, Tendsto (fun j => (A j).map p) atTop (𝓝 (v p))) :
    ∀ᵐ p ∂mu, W p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (v p)) := by
  obtain ⟨P, K, hP, hK, hb, hfix, hrange⟩ := m64ChartReadable_tangent_projection e he hread
  let R := fun j p => ContinuousLinearMap.id ℝ E - P ((A j).map p)
  let R0 := fun p => ContinuousLinearMap.id ℝ E - P (v p)
  have hR (j : ℕ) : AEStronglyMeasurable (R j) mu :=
    aestronglyMeasurable_const.sub
      (hP.comp_aestronglyMeasurable ((A j).map_aestronglyMeasurable hei))
  have hbound (j : ℕ) : ∀ᵐ p ∂mu, ‖R j p‖ ≤ 1 + K := Eventually.of_forall fun p =>
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (hb _))
  have hRlim : ∀ᵐ p ∂mu, Tendsto (fun j => R j p) atTop (𝓝 (R0 p)) := by
    filter_upwards [hlim] with p hp
    exact tendsto_const_nhds.sub ((hP.tendsto _).comp hp)
  have hzero (j : ℕ) : ∀ᵐ p ∂mu, R j p ((A j).column i p) = 0 := by
    filter_upwards [(A j).tangent i] with p hp
    obtain ⟨w, hw⟩ := hp
    change (A j).column i p - P ((A j).map p) ((A j).column i p) = 0
    have hfixed : P ((A j).map p) ((A j).column i p) = (A j).column i p := by
      rw [← hw]
      exact hfix _ _
    exact sub_eq_zero.mpr hfixed.symm
  have hz := m64MovingKernel_weak_closed R R0 hR (by positivity : 0 ≤ 1 + K)
    hbound hRlim hweak hzero
  filter_upwards [hz] with p hp
  change W p - P (v p) (W p) = 0 at hp
  have heq : P (v p) (W p) = W p := (sub_eq_zero.mp hp).symm
  simpa only [heq] using hrange (v p) (W p)

theorem observedWeakAnnulus_varying_trace_subsequence
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℕ → ℝ → M}
    (hc0 : ∀ j, Continuous (c0 j)) (hc1 : ∀ j, Continuous (c1 j))
    {d0 d1 : ℝ → M}
    (hlim0 : ∀ᵐ x ∂volume, Tendsto (fun j => c0 j x) atTop (𝓝 (d0 x)))
    (hlim1 : ∀ᵐ x ∂volume, Tendsto (fun j => c1 j x) atTop (𝓝 (d1 x)))
    (A : ∀ j, M64ObservedWeakAnnulus (n := n) e (c0 j) (c1 j))
    {C : ℝ} (hC : ∀ j i, ‖(A j).column i‖ ^ 2 ≤ C) :
    ∃ (k : ℕ → ℕ) (L : M64ObservedWeakAnnulus (n := n) e d0 d1),
      StrictMono k ∧ Tendsto (fun j => (A (k j)).value) atTop (𝓝 L.value) ∧
      (∀ i, WeakConverges (fun j => (A (k j)).column i) (L.column i)) ∧
      ∀ᵐ p ∂mu, Tendsto (fun j => (A (k j)).map p) atTop (𝓝 (L.map p)) := by
  classical
  obtain ⟨R, hR⟩ := (isCompact_range he.continuous).isBounded.exists_norm_le
  have hnorm (j : ℕ) (i : Fin 2) : (∫ p in S, ‖(A j).column i p‖ ^ 2) ≤ C := by
    rw [← LpFiniteCoordinatesNative.l2_norm_sq]
    exact hC j i
  obtain ⟨k, U, W, hk, hstrong, hweak, hae⟩ := m64Annulus_weak_sobolev_subsequence
    (fun j => e ∘ (A j).map) (fun j i => (A j).column i)
    (fun j => (A j).observed_memLp) (fun j i => Lp.memLp ((A j).column i))
    (fun j i b => (A j).weak_partial i b) (fun _ _ => hR _ (mem_range_self _)) hnorm
  simp only [Lp.toLp_coeFn] at hweak
  have huweak : WeakConverges (fun j => (A (k j)).value) U :=
    fun T => (T.continuous.tendsto U).comp hstrong
  have htarget : ∀ᵐ p ∂mu, U p ∈ range e := by
    filter_upwards [hae] with p hp
    exact hei.isClosed_range.mem_of_tendsto hp
      (Eventually.of_forall fun j => mem_range_self ((A (k j)).map p))
  let v : LoopPlane → M := fun p =>
    if hp : U p ∈ range e then Classical.choose hp else (A 0).map 0
  have hev : ∀ᵐ p ∂mu, e (v p) = U p := by
    filter_upwards [htarget] with p hp
    simp only [v, dif_pos hp]
    exact Classical.choose_spec hp
  have hlim : ∀ᵐ p ∂mu, Tendsto (fun j => (A (k j)).map p) atTop (𝓝 (v p)) := by
    filter_upwards [hae, hev] with p hp hpv
    apply hei.isEmbedding.tendsto_nhds_iff.mpr
    rw [hpv]
    exact hp
  have hv : MemLp (e ∘ v) 2 mu := (Lp.memLp U).ae_eq (EventuallyEq.symm hev)
  have htangent (i : Fin 2) : ∀ᵐ p ∂mu, W i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (v p)) :=
    varying_trace_tangent_closed e he hei.isEmbedding hread (fun j => A (k j))
      v (W i) i (hweak i) hlim
  have hpartial (i : Fin 2) (b : Fin m) :
      Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i
        (fun p => W i p b) (fun p => e (v p) b) S := by
    apply m64WeakPartialDeriv_ae_congr
      ((EventuallyEq.symm hev).mono fun _ hp => congrArg (fun x : E => x b) hp)
      EventuallyEq.rfl
    apply m64Annulus_weak_partial_closed huweak (hweak i) i b
    intro j
    exact m64WeakPartialDeriv_ae_congr
      ((A (k j)).observed_memLp.coeFn_toLp.symm.mono
        fun _ hp => congrArg (fun x : E => x b) hp) EventuallyEq.rfl ((A (k j)).weak_partial i b)
  have htest (phi : LoopPlane → ℝ) (i : Fin 2)
      (hphi : ContDiff ℝ 1 phi) {c : ℕ → E} {c' : E}
      (hc : Tendsto c atTop (𝓝 c'))
      (hseq : ∀ j, (∫ p in S, phi p • (A (k j)).column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e ((A (k j)).map p)) = c j) :
      (∫ p in S, phi p • W i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (v p)) = c' := by
    have hseq' (j : ℕ) : (∫ p in S, phi p • (A (k j)).column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • (A (k j)).value p) = c j := by
      convert hseq j using 2
      apply integral_congr_ae
      filter_upwards [(A (k j)).observed_memLp.coeFn_toLp] with p hp
      exact congrArg (fun x : E => fderiv ℝ phi p (EuclideanSpace.single i 1) • x) hp
    have hh := annulus_weak_green_of_varying_boundary huweak (hweak i) i phi hphi hc hseq'
    convert hh using 2
    apply integral_congr_ae
    filter_upwards [hev] with p hp
    exact congrArg (fun x : E => fderiv ℝ phi p (EuclideanSpace.single i 1) • x) hp
  have htrace (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) :
      Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) • e (c1 (k j) x) -
          phi (annulusPoint x 0) • e (c0 (k j) x)) atTop
        (𝓝 (∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 1) • e (d1 x) - phi (annulusPoint x 0) • e (d0 x))) := by
    have hp (s : ℝ) : Continuous (fun x => phi (annulusPoint x s)) := by
      apply hphi.continuous.comp
      unfold annulusPoint
      fun_prop
    apply tendsto_integral_of_dominated_convergence
      (fun x => (‖phi (annulusPoint x 1)‖ + ‖phi (annulusPoint x 0)‖) * R)
    · intro j
      exact (((hp 1).smul (he.continuous.comp (hc1 (k j)))).sub
        ((hp 0).smul (he.continuous.comp (hc0 (k j))))).aestronglyMeasurable
    · exact (((hp 1).norm.add (hp 0).norm).mul continuous_const).integrableOn_Icc
    · intro j
      apply Eventually.of_forall
      intro x
      calc
        _ ≤ ‖phi (annulusPoint x 1) • e (c1 (k j) x)‖ +
            ‖phi (annulusPoint x 0) • e (c0 (k j) x)‖ := norm_sub_le _ _
        _ = ‖phi (annulusPoint x 1)‖ * ‖e (c1 (k j) x)‖ +
            ‖phi (annulusPoint x 0)‖ * ‖e (c0 (k j) x)‖ := by rw [norm_smul, norm_smul]
        _ ≤ ‖phi (annulusPoint x 1)‖ * R + ‖phi (annulusPoint x 0)‖ * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hR _ (mem_range_self _)) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hR _ (mem_range_self _)) (norm_nonneg _))
        _ = _ := by ring
    · filter_upwards [ae_restrict_of_ae hlim0, ae_restrict_of_ae hlim1] with x hx0 hx1
      exact (tendsto_const_nhds.smul
        ((he.continuous.tendsto _).comp (hx1.comp hk.tendsto_atTop))).sub
          (tendsto_const_nhds.smul
            ((he.continuous.tendsto _).comp (hx0.comp hk.tendsto_atTop)))
  let L : M64ObservedWeakAnnulus (n := n) e d0 d1 :=
    { map := v
      observed_memLp := hv
      column := W
      tangent := htangent
      weak_partial := hpartial
      boundary := fun phi hphi => htest phi 1 hphi (htrace phi hphi)
        (fun j => (A (k j)).boundary phi hphi)
      seam := fun phi hphi hseam => htest phi 0 hphi tendsto_const_nhds
        (fun j => (A (k j)).seam phi hphi hseam) }
  have hvalue : L.value = U := by
    apply Lp.ext
    exact hv.coeFn_toLp.trans hev
  refine ⟨k, L, hk, ?_, hweak, hlim⟩
  rwa [hvalue]

end PoincareConjecture.M64
