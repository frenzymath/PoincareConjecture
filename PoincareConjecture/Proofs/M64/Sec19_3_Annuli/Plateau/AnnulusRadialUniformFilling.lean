import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialH1Filling
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeH1Radius












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => ball (0 : LoopPlane) 1
local notation "K" => closedBall (0 : LoopPlane) 1
local notation "mu" => volume.restrict S
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)




theorem m64ChartReadable_uniform_radial_H1_filling_radius
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hread : M60.SUChartReadable (n := n) e) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gamma : ℝ → M), Continuous gamma → Function.Periodic gamma curvePeriod →
        (∀ x ∈ Icc (0 : ℝ) curvePeriod, dist (e (gamma x)) (e (gamma 0)) < delta) →
        ∀ b : LoopPlane → M, ContMDiff (𝓡 2) (𝓡 n) 1 b →
          (∀ z ∈ K, dist (e (b z)) (e (gamma 0)) < delta) →
          (∀ z, b (m60PlaneReflection z) = b z) →
          (∀ t, angularPoint t 1 ≤ 0 → gamma t = b (angularPoint t)) →
          ∀ (w : ℕ → ℝ → E), (∀ j, ContDiff ℝ 1 (w j)) →
            (∀ j, Function.Periodic (w j) curvePeriod) →
            TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) →
            ∀ v : ℝ → E, MemLp v 2 circleMu →
              Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
                ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0) →
              ∃ (F : LoopPlane → M) (W : Fin 2 → Lp E 2 mu),
                ContinuousOn F K ∧ (∀ t, F (angularPoint t) = gamma t) ∧
                (∀ z ∈ K, z 1 ≤ 0 → F z = b z) ∧ MemLp (e ∘ F) 2 mu ∧
                (∀ i, ∀ᵐ z ∂mu, W i z ∈ range (mfderiv (𝓡 n) (𝓡 m) e (F z))) ∧
                (∀ i c, HasWeakPartialDeriv i
                  (fun z => W i z c) (fun z => e (F z) c) S) ∧
                ∀ i, ‖W i‖ ^ 2 ≤ C *
                  ((∫ t in Icc (0 : ℝ) curvePeriod, ‖v t‖ ^ 2) +
                    (∫ z in S, ‖fderiv ℝ (e ∘ b) z (EuclideanSpace.single (0 : Fin 2) 1)‖ ^ 2) +
                    ∫ z in S, ‖fderiv ℝ (e ∘ b) z (EuclideanSpace.single (1 : Fin 2) 1)‖ ^ 2) := by
  classical
  choose U C hU hp hC hfill using m64ChartReadable_local_radial_H1_filling g e he hread
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun q _ => mem_iUnion.mpr ⟨q, hp q⟩)
  choose V hV hpre using fun p => hei.isInducing.isOpen_iff.mp (hU p)
  have hcover : range e ⊆ ⋃ p : (↑T : Set M), V p.1 := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨p, hpT, hq⟩ := mem_iUnion₂.mp (hT (mem_univ q))
    refine mem_iUnion.mpr ⟨⟨p, hpT⟩, ?_⟩
    change q ∈ e ⁻¹' V p
    rw [hpre p]
    exact hq
  obtain ⟨delta, hdelta, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_range he.continuous) (fun p : (↑T : Set M) => hV p.1) hcover
  refine ⟨delta, hdelta, ∑ p ∈ T, C p, Finset.sum_nonneg (fun p _ => hC p), ?_⟩
  intro gamma hgamma hgammaP hsmall b hb hbsmall hbsym hmatch w hw hwP hlim v hv hder
  obtain ⟨p, hpball⟩ := hball (e (gamma 0)) (mem_range_self _)
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hgammaU (x : ℝ) : gamma x ∈ U p.1 := by
    let y := toIcoMod hP 0 x
    have hy : y ∈ Icc (0 : ℝ) curvePeriod :=
      Ico_subset_Icc_self (toIcoMod_mem_Ico' hP x)
    have hxy : gamma y = gamma x := by
      simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
        (hgammaP.zsmul (-toIcoDiv hP 0 x)) x
    rw [← hxy, ← hpre p.1]
    exact hpball (hsmall y hy)
  have hbU (z : LoopPlane) (hz : z ∈ K) : b z ∈ U p.1 := by
    rw [← hpre p.1]
    exact hpball (hbsmall z hz)
  obtain ⟨F, W, hc, hcircle, hfixed, hu, ht, hweak, henergy⟩ :=
    hfill p.1 gamma hgamma hgammaP hgammaU b hb hbU hbsym hmatch w hw hwP hlim v hv hder
  refine ⟨F, W, hc, hcircle, hfixed, hu, ht, hweak, fun i => (henergy i).trans ?_⟩
  apply mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => hC q) p.2)
  exact add_nonneg (add_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)) (integral_nonneg fun _ => sq_nonneg _)

end PoincareConjecture
