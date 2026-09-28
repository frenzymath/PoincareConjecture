import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityChartEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityReplacement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

set_option maxHeartbeats 1600000 in

theorem M64ObservedWeakAnnulus.affine_chart_energy_minimum
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q)
    (b : M) {u phi : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (hRS : Metric.closedBall a R ⊆ S)
    (hu : ContinuousOn u (Metric.closedBall a R)) (hp : ContDiff ℝ ∞ phi)
    (hps : tsupport phi ⊆ Metric.ball a ((R / 4) * Real.exp (-1)))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (Metric.ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j)
      (Metric.ball a R))
    (hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (Metric.closedBall a R))
    {delta : ℝ} (hdelta : 0 < delta)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 n) b).target)
    (hrange : ∀ t : ℝ, |t| < delta →
      MapsTo (fun p => u p + t • phi p) (Metric.closedBall a R) K) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let F := fun (t : ℝ) (p : LoopPlane) =>
      (G (u p + t • phi p)
          (W 0 p + t • fderiv ℝ phi p (EuclideanSpace.single 0 1))
          (W 0 p + t • fderiv ℝ phi p (EuclideanSpace.single 0 1)) +
        G (u p + t • phi p)
          (W 1 p + t • fderiv ℝ phi p (EuclideanSpace.single 1 1))
          (W 1 p + t • fderiv ℝ phi p (EuclideanSpace.single 1 1))) / 2
    ∀ t : ℝ, |t| < delta → IntegrableOn (F t) (Metric.ball a (R / 2)) ∧
      (∫ p in Metric.ball a (R / 2), F 0 p) ≤ ∫ p in Metric.ball a (R / 2), F t p := by
  classical
  let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
  let c := extChartAt (𝓡 n) b
  let G := g.pullbackCoefficients c.symm
  let U := fun (t : ℝ) (p : LoopPlane) => u p + t • phi p
  let Z := fun (t : ℝ) (i : Fin 2) (p : LoopPlane) =>
    W i p + t • fderiv ℝ phi p (EuclideanSpace.single i 1)
  let f := fun t => c.symm ∘ U t
  let V := fun (t : ℝ) (i : Fin 2) (p : LoopPlane) => fderiv ℝ (e ∘ c.symm) (U t p) (Z t i p)
  let F := fun (t : ℝ) (p : LoopPlane) =>
    (G (U t p) (Z t 0 p) (Z t 0 p) + G (U t p) (Z t 1 p) (Z t 1 p)) / 2
  let H := fun (t : ℝ) (p : LoopPlane) =>
    (Q (f t p) (V t 0 p) (V t 0 p) + Q (f t p) (V t 1 p) (V t 1 p)) / 2
  let old := fun p => (Q (A.map p) (A.column 0 p) (A.column 0 p) +
    Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2
  let D := Metric.ball a (R / 2)
  have hhalf : 0 < R / 2 := half_pos hR
  have hquarter : 0 < R / 4 := div_pos hR (by norm_num)
  have hDR : D ⊆ Metric.closedBall a R :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall
  have hDS : D ⊆ S := hDR.trans hRS
  have hzero : |(0 : ℝ)| < delta := by simpa using hdelta
  have hweak (t : ℝ) (ht : |t| < delta) :
      MemLp (e ∘ f t) 2 (volume.restrict D) ∧
        (∀ i, MemLp (V t i) 2 (volume.restrict D)) ∧
        (∀ i j, HasWeakPartialDeriv i (fun p => V t i p j) (fun p => e (f t p) j) D) ∧
        ∀ i, ∀ᵐ p ∂volume.restrict D,
          V t i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f t p)) := by
    obtain ⟨hU, hZ, hwZ⟩ := m64_affine_weak_coordinates hu hp hW hw t
    exact m64InverseChart_observed_weak_columns e he b hhalf (by linarith)
      hU hZ hwZ hK hKt (hrange t ht)
  have hF (t : ℝ) (ht : |t| < delta) : EqOn (H t) (F t) D := by
    intro p hpD
    have hy := hKt (hrange t ht (hDR hpD))
    dsimp only [H, F, f, Function.comp_apply, V]
    rw [m64InverseChart_observed_metric g e he Q hdiag b hy,
      m64InverseChart_observed_metric g e he Q hdiag b hy]
  have hfm (t : ℝ) (ht : |t| < delta) : AEStronglyMeasurable (f t) (volume.restrict D) :=
    hei.aestronglyMeasurable_comp_iff.mp (hweak t ht).1.aestronglyMeasurable
  have hFae (t : ℝ) (ht : |t| < delta) : H t =ᵐ[volume.restrict D] F t := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with p hpD
    exact hF t ht hpD
  have hHI (t : ℝ) (ht : |t| < delta) : IntegrableOn (H t) D :=
    m64Observed_energyDensity_integrable Q hQ hb (f t) (hfm t ht) (V t) (hweak t ht).2.1
  have hFI (t : ℝ) (ht : |t| < delta) : IntegrableOn (F t) D :=
    (hHI t ht).congr (hFae t ht)
  have hf0 (p : LoopPlane) (hpR : p ∈ Metric.closedBall a R) : f 0 p = A.map p := by
    simpa only [f, U, zero_smul, add_zero] using hmap hpR
  have hV0 : ∀ i, V 0 i =ᵐ[volume.restrict D] (A.column i : LoopPlane → E) := by
    apply m64WeakColumns_ae_eq Metric.isOpen_ball (hweak 0 hzero).2.1
      (fun i => (Lp.memLp (A.column i)).mono_measure (Measure.restrict_mono hDS le_rfl))
      (hweak 0 hzero).2.2.1
      (fun i j => (A.weak_partial i j).restrict Metric.isOpen_ball hDS)
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with p hpD
    exact congrArg e (hf0 p (hDR hpD))
  have hbase : F 0 =ᵐ[volume.restrict D] old := by
    filter_upwards [hFae 0 hzero, hV0 0, hV0 1,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with p hFp h0 h1 hpD
    rw [← hFp]
    dsimp only [H, old]
    rw [hf0 p (hDR hpD), h0, h1]
  change ∀ t : ℝ, |t| < delta → IntegrableOn (F t) D ∧ (∫ p in D, F 0 p) ≤ ∫ p in D, F t p
  intro t ht
  refine ⟨hFI t ht, ?_⟩
  have hmatch (p : LoopPlane) (hl : (R / 4) * Real.exp (-1) ≤ dist p a)
      (hh : dist p a ≤ R / 4) : f t p = A.map p := by
    have hnot : p ∉ tsupport phi := fun h => (not_lt_of_ge hl) (hps h)
    have hphip := image_eq_zero_of_notMem_tsupport hnot
    have hpR : p ∈ Metric.closedBall a R := hh.trans (by linarith)
    simpa only [f, U, Function.comp_apply, hphip, smul_zero, add_zero] using hmap hpR
  have hquarterD : Metric.closedBall a (R / 4) ⊆ D :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨r, hr, hrl, hrh, B, hBm, hBc⟩ :=
    A.exists_replacement_of_outer_agreement Metric.isOpen_ball a hquarter hquarterD
      (hquarterD.trans hDS) (f t) (V t) (hweak t ht).1 (hweak t ht).2.1
      (hweak t ht).2.2.1 (hweak t ht).2.2.2 hmatch
  have hrD : Metric.closedBall a r ⊆ D :=
    (Metric.closedBall_subset_closedBall hrh).trans hquarterD
  have hBD := m64WeakAnnulusReplacement_energy Q hQ hei hb A B
    Metric.isClosed_closedBall.measurableSet (hrD.trans hDS) (f t)
    ((hfm t ht).mono_measure (Measure.restrict_mono hrD le_rfl)) (V t)
    (fun i => ((hweak t ht).2.1 i).mono_measure (Measure.restrict_mono hrD le_rfl)) hBm hBc
  have hloc : (∫ p in Metric.closedBall a r, F 0 p) ≤
      ∫ p in Metric.closedBall a r, F t p := by
    have hb0 : (∫ p in Metric.closedBall a r, F 0 p) =
        ∫ p in Metric.closedBall a r, old p :=
      integral_congr_ae (hbase.filter_mono (ae_mono (Measure.restrict_mono hrD le_rfl)))
    have hbt : (∫ p in Metric.closedBall a r, H t p) =
        ∫ p in Metric.closedBall a r, F t p :=
      integral_congr_ae ((hFae t ht).filter_mono
        (ae_mono (Measure.restrict_mono hrD le_rfl)))
    change B.energy Q = A.energy Q + (∫ p in Metric.closedBall a r, H t p) -
      ∫ p in Metric.closedBall a r, old p at hBD
    rw [← hb0, hbt] at hBD
    linarith [hmin B]
  have hdiff : (∫ p in D, F t p - F 0 p) =
      ∫ p in Metric.closedBall a r, F t p - F 0 p := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hrD
    intro p hpD
    have hnot : p ∉ tsupport phi := by
      intro hpS
      have hlt := hps hpS
      have hdist : r < dist p a := lt_of_not_ge hpD.2
      exact (not_lt_of_ge hrl) (hdist.trans hlt)
    have hphip := image_eq_zero_of_notMem_tsupport hnot
    have hdphi : fderiv ℝ phi p = 0 := fderiv_of_notMem_tsupport ℝ hnot
    simp only [F, U, Z, hphip, hdphi, zero_apply, smul_zero, add_zero, sub_self]
  rw [integral_sub (hFI t ht) (hFI 0 hzero),
    integral_sub ((hFI t ht).mono_set hrD) ((hFI 0 hzero).mono_set hrD)] at hdiff
  linarith

end PoincareConjecture
