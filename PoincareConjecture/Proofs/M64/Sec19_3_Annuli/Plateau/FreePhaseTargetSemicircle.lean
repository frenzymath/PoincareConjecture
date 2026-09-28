import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseBoundarySemicircle
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicClosedTrace
import PoincareConjecture.Proofs.M64.Mathlib.CoordinateCurvePrimitive
import PoincareConjecture.Proofs.M64.Mathlib.AbsoluteContinuityCongruence
import PoincareConjecture.Proofs.M64.Mathlib.HalfDiskC1Green

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric Topology
open scoped Topology ContDiff Manifold SchwartzMap

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ
local notation "nu" => volume.restrict (Icc (0 : ℝ) Real.pi)

theorem lower_halfDisk_target_semicircle
    (A : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    {x H epsilon R : ℝ} (hHpos : 0 < H) (hx : H < x)
    (hP : x + H < curvePeriod) (hH : H < 1)
    (hepsilon : 0 < epsilon) (hRH : R ≤ H) :
    let u := fun z => e (A.annulus.map (z + annulusPoint x 0))
    let V := fun i z => A.annulus.column i (z + annulusPoint x 0)
    let b := fun s => e (c0 (A.label0 (s + x)))
    ∀ᵐ r ∂volume.restrict (Icc epsilon R),
      let d := fun theta => (-r * Real.sin theta) • V 0 (r • angularPoint theta) +
        (r * Real.cos theta) • V 1 (r • angularPoint theta)
      MemLp d 2 nu ∧ ∃ gamma : ℝ → M,
        ContinuousOn gamma (Icc (0 : ℝ) Real.pi) ∧
        AbsolutelyContinuousOnInterval (e ∘ gamma) 0 Real.pi ∧
        (gamma =ᵐ[nu] fun theta => A.annulus.map
          (r • angularPoint theta + annulusPoint x 0)) ∧
        gamma 0 = c0 (A.label0 (r + x)) ∧
        gamma Real.pi = c0 (A.label0 (-r + x)) ∧
        (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          e (gamma t) - e (gamma s) = ∫ theta in s..t, d theta) ∧
        (∀ᵐ theta ∂nu, d theta ∈ range (mfderiv (𝓡 n) (𝓡 m) e (gamma theta))) ∧
        ∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ (i : Fin 2) (a : Fin m),
          (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
            V i z a * test z + u z a * fderiv ℝ test z (basis i)) =
            r * (∫ theta in (0 : ℝ)..Real.pi,
              e (gamma theta) a * test (r • angularPoint theta) * angularPoint theta i) -
            (basis 1) i * ∫ s in (-r)..r, b s a * test (s • basis 0) := by
  classical
  let T := fun z : LoopPlane => z + annulusPoint x 0
  have hT : MeasurePreserving T volume volume := measurePreserving_add_right volume _
  have hbase := m64Annulus_halfDisk_ae_mem hx hP hH
  have ht (i : Fin 2) := m64HalfDisk_polar_ae hepsilon hRH
    (m64MeasurePreserving_ae_restrict hT isOpen_interior.measurableSet
      hbase (A.annulus.tangent i))
  have hdata := A.lower_halfDisk_semicircle_data he hA hc0 hc1 hH0 hH1
    hHpos hx hP hH hepsilon hRH
  obtain ⟨hu, hV, hb, _⟩ := A.lower_halfDisk_graph_approximation
    he hA hc0 hc1 hH0 hH1 hHpos hx hP hH
  filter_upwards [hdata, ht 0, ht 1, ae_restrict_mem measurableSet_Icc] with r hr ht0 ht1 hrI
  have hrpos : 0 < r := hepsilon.trans_le hrI.1
  have hrH : r ≤ H := hrI.2.trans hRH
  have hKr : closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1} ⊆
      closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1} :=
    inter_subset_inter (closedBall_subset_closedBall hrH) Subset.rfl
  let : IsFiniteMeasure (volume.restrict
      (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})) := isFiniteMeasure_restrict.mpr
    ((isCompact_closedBall (0 : LoopPlane) r).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)).measure_lt_top.ne
  let u := fun theta => e (A.annulus.map (T (r • angularPoint theta)))
  let d := fun theta => (-r * Real.sin theta) • A.annulus.column 0 (T (r • angularPoint theta)) +
    (r * Real.cos theta) • A.annulus.column 1 (T (r • angularPoint theta))
  have hd : MemLp d 2 nu := MemLp.of_eval_piLp (fun a => (hr a).2.2.1)
  obtain ⟨W, hW, hWu, hW0, hWpi, hWinc⟩ := m64Curve_vector_primitive Real.pi_pos.le u d
    (e (c0 (A.label0 (r + x)))) (e (c0 (A.label0 (-r + x)))) hd (fun a => by
      obtain ⟨v, _, hva, hv0, hvpi, hvinc⟩ := (hr a).2.2.2
      exact ⟨v, hva, hv0, hvpi, fun s hs => hvinc 0 ⟨le_rfl, Real.pi_pos.le⟩ s hs⟩)
  have hWc : ContinuousOn W (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hW.continuousOn
  have hWr : MapsTo W (Icc (0 : ℝ) Real.pi) (range e) :=
    m64Curve_closed_target_of_ae W Real.pi_pos hWc hei.isClosed_range
      ⟨e (A.annulus.map 0), mem_range_self _⟩
      (hWu.mono fun theta htheta => htheta ▸ mem_range_self _)
  let gamma := fun theta => if h : W theta ∈ range e then Classical.choose h else A.annulus.map 0
  have hgamma (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) Real.pi) :
      e (gamma theta) = W theta := by
    simp only [gamma, dif_pos (hWr htheta)]
    exact Classical.choose_spec (hWr htheta)
  have hgammaAE : gamma =ᵐ[nu] fun theta => A.annulus.map (T (r • angularPoint theta)) := by
    filter_upwards [hWu, ae_restrict_mem measurableSet_Icc] with theta htheta hI
    exact hei.isEmbedding.injective ((hgamma theta hI).trans htheta)
  refine ⟨hd, gamma, hei.isEmbedding.continuousOn_iff.mpr (hWc.congr hgamma), ?_, hgammaAE,
    hei.isEmbedding.injective ((hgamma 0 ⟨le_rfl, Real.pi_pos.le⟩).trans hW0),
    hei.isEmbedding.injective ((hgamma Real.pi ⟨Real.pi_pos.le, le_rfl⟩).trans hWpi), ?_, ?_, ?_⟩
  · apply m64AbsolutelyContinuousOnInterval_congr hW
    rw [uIcc_of_le Real.pi_pos.le]
    exact fun theta htheta => (hgamma theta htheta).symm
  · intro s hs t ht'
    rw [hgamma s hs, hgamma t ht']
    exact hWinc s hs t ht'
  · filter_upwards [ht0, ht1, hgammaAE] with theta h0 h1 hga
    obtain ⟨v0, hv0⟩ := h0
    obtain ⟨v1, hv1⟩ := h1
    rw [hga]
    refine ⟨(-r * Real.sin theta) • v0 + (r * Real.cos theta) • v1, ?_⟩
    rw [map_add, map_smul, map_smul, hv0, hv1]
  · intro test htest i a
    have huL := ((hu.eval_piLp a).mono_measure (Measure.restrict_mono hKr le_rfl)).integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
    have hVL (j : Fin 2) := ((hV j |>.eval_piLp a).mono_measure
      (Measure.restrict_mono hKr le_rfl)).integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hbL := ((hb.eval_piLp a).mono_measure (Measure.restrict_mono
      (Icc_subset_Icc (neg_le_neg hrH) hrH) le_rfl)).integrable
        (by norm_num : (1 : ENNReal) ≤ 2)
    have hvL : Integrable (fun theta => e (gamma theta) a) nu := by
      apply ((hr a).1.integrable (by norm_num)).congr
      filter_upwards [hgammaAE] with theta htheta
      rw [htheta]
    apply m64HalfDisk_green_contDiff hrpos _ _ _ _ huL hVL hbL hvL _ test htest i
    intro phi j
    rw [(hr a).2.1 phi j]
    congr 2
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : uIoc (0 : ℝ) Real.pi ⊆ Icc (0 : ℝ) Real.pi := by
      rw [uIoc_of_le Real.pi_pos.le]
      exact Ioc_subset_Icc_self
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hgammaAE] with theta htheta
    rw [htheta]

end PoincareConjecture.M64FreeWeakPhaseAnnulus
