import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityLocalMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusReplacement









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane}
  {c0 c1 : ℝ → M} {H0 H1 : ℝ ≃o ℝ} {frequency degree : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "S" => interior m64AnnulusDomain

set_option maxHeartbeats 1600000 in




theorem weighted_coordinate_replacement_minimum
    (A C : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 frequency degree)
    (hC0 : C.label0 = A.label0) (hC1 : C.label1 = A.label1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (hB : Continuous B)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (modulus : ℝ)
    (hminimum : A.annulus.weightedEnergy B modulus ≤ C.annulus.weightedEnergy B modulus)
    (q : M) {u phi : LoopPlane → E} {W : Fin 2 → LoopPlane → E}
    {p0 : LoopPlane} {R r : ℝ} (hR : 0 < R) (hRS : closedBall p0 R ⊆ S)
    (hrl : (R / 4) * Real.exp (-1) ≤ r) (hrh : r ≤ R / 4)
    (hu : ContinuousOn u (closedBall p0 R)) (hp : ContDiff ℝ ∞ phi)
    (hs : tsupport phi ⊆ ball p0 ((R / 4) * Real.exp (-1)))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball p0 R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball p0 R))
    (hmap : EqOn ((extChartAt (𝓡 n) q).symm ∘ u) A.annulus.map (closedBall p0 R))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 n) q).target)
    (hrange : ∀ s : ℝ, |s| < epsilon →
      MapsTo (fun p => u p + s • phi p) (closedBall p0 R) K)
    (t : ℝ) (ht : |t| < epsilon)
    (hCm : C.annulus.map = (closedBall p0 r).piecewise
      (fun p => (extChartAt (𝓡 n) q).symm (u p + t • phi p)) A.annulus.map)
    (hCc : ∀ i, (C.annulus.column i : LoopPlane → EuclideanSpace ℝ (Fin m)) =ᵐ[volume.restrict S]
      (closedBall p0 r).piecewise
        (fun p => fderiv ℝ (e ∘ (extChartAt (𝓡 n) q).symm) (u p + t • phi p)
          (W i p + t • fderiv ℝ phi p (EuclideanSpace.single i 1))) (A.annulus.column i)) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) q).symm
    let J := fun s p =>
      (modulus * G (u p + s • phi p)
          (W 0 p + s • fderiv ℝ phi p (EuclideanSpace.single 0 1))
          (W 0 p + s • fderiv ℝ phi p (EuclideanSpace.single 0 1)) +
        modulus⁻¹ * G (u p + s • phi p)
          (W 1 p + s • fderiv ℝ phi p (EuclideanSpace.single 1 1))
          (W 1 p + s • fderiv ℝ phi p (EuclideanSpace.single 1 1))) / 2
    (∫ p in ball p0 (R / 2), J 0 p) ≤ ∫ p in ball p0 (R / 2), J t p := by
  classical
  let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
  let c := extChartAt (𝓡 n) q
  let G := g.pullbackCoefficients c.symm
  let U := fun (s : ℝ) p => u p + s • phi p
  let Z := fun (s : ℝ) i p => W i p + s • fderiv ℝ phi p (EuclideanSpace.single i 1)
  let f := fun s => c.symm ∘ U s
  let V := fun s i p => fderiv ℝ (e ∘ c.symm) (U s p) (Z s i p)
  let J := fun s p => (modulus * G (U s p) (Z s 0 p) (Z s 0 p) +
    modulus⁻¹ * G (U s p) (Z s 1 p) (Z s 1 p)) / 2
  let H := fun s p => (modulus * B (f s p) (V s 0 p) (V s 0 p) +
    modulus⁻¹ * B (f s p) (V s 1 p) (V s 1 p)) / 2
  let old := fun p => (modulus * B (A.annulus.map p)
      (A.annulus.column 0 p) (A.annulus.column 0 p) +
    modulus⁻¹ * B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2
  let D := ball p0 (R / 2)
  have hDR : D ⊆ closedBall p0 R :=
    (ball_subset_ball (half_le_self hR.le)).trans ball_subset_closedBall
  have hDS : D ⊆ S := hDR.trans hRS
  have hzero : |(0 : ℝ)| < epsilon := by simpa using hepsilon
  have hweak (s : ℝ) (hh : |s| < epsilon) :
      MemLp (e ∘ f s) 2 (volume.restrict D) ∧
        (∀ i, MemLp (V s i) 2 (volume.restrict D)) ∧
        (∀ i j, HasWeakPartialDeriv i (fun p => V s i p j) (fun p => e (f s p) j) D) ∧
        ∀ i, ∀ᵐ p ∂volume.restrict D,
          V s i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f s p)) := by
    obtain ⟨hU, hZ, hwZ⟩ := m64_affine_weak_coordinates hu hp hW hw s
    exact m64InverseChart_observed_weak_columns e he q (half_pos hR) (half_lt_self hR)
      hU hZ hwZ hK hKt (hrange s hh)
  have hJ (s : ℝ) (hh : |s| < epsilon) : EqOn (H s) (J s) D := by
    intro p hpD
    have hy := hKt (hrange s hh (hDR hpD))
    dsimp only [H, J, f, Function.comp_apply, V]
    rw [m64InverseChart_observed_metric g e he B hdiag q hy,
      m64InverseChart_observed_metric g e he B hdiag q hy]
  have hfm (s : ℝ) (hh : |s| < epsilon) : AEStronglyMeasurable (f s) (volume.restrict D) :=
    hei.aestronglyMeasurable_comp_iff.mp (hweak s hh).1.aestronglyMeasurable
  have hJae (s : ℝ) (hh : |s| < epsilon) : H s =ᵐ[volume.restrict D] J s := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hpD
    exact hJ s hh hpD
  have hJI (s : ℝ) (hh : |s| < epsilon) : IntegrableOn (J s) D := by
    have hHI : IntegrableOn (H s) D :=
      (((m64VariableModulus_column_integrable B hB hb (f s) (hfm s hh)
        (V s 0) ((hweak s hh).2.1 0)).const_mul modulus).add
          ((m64VariableModulus_column_integrable B hB hb (f s) (hfm s hh)
            (V s 1) ((hweak s hh).2.1 1)).const_mul modulus⁻¹)).div_const 2
    exact hHI.congr (hJae s hh)
  have hf0 (p : LoopPlane) (hpR : p ∈ closedBall p0 R) : f 0 p = A.annulus.map p := by
    simpa only [f, U, zero_smul, add_zero] using hmap hpR
  have hV0 : ∀ i, V 0 i =ᵐ[volume.restrict D] (A.annulus.column i : LoopPlane → _) := by
    apply m64WeakColumns_ae_eq isOpen_ball (hweak 0 hzero).2.1
      (fun i => (Lp.memLp (A.annulus.column i)).mono_measure (Measure.restrict_mono hDS le_rfl))
      (hweak 0 hzero).2.2.1
      (fun i j => (A.annulus.weak_partial i j).restrict isOpen_ball hDS)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hpD
    exact congrArg e (hf0 p (hDR hpD))
  have hbase : J 0 =ᵐ[volume.restrict D] old := by
    filter_upwards [hJae 0 hzero, hV0 0, hV0 1,
      ae_restrict_mem isOpen_ball.measurableSet] with p hJp h0 h1 hpD
    rw [← hJp]
    dsimp only [H, old]
    rw [hf0 p (hDR hpD), h0, h1]
  let Cobs : M64ObservedWeakAnnulus (n := n) e (c0 ∘ A.label0) (c1 ∘ A.label1) := {
    C.annulus with
    boundary := fun phi hp => by
      simpa only [hC0, hC1] using C.annulus.boundary phi hp }
  have hrD : closedBall p0 r ⊆ D := closedBall_subset_ball (by linarith)
  have hBD := m64VariableModulus_replacement_energy B hB hei hb modulus A.annulus Cobs
    isClosed_closedBall.measurableSet (hrD.trans hDS) (f t)
    ((hfm t ht).mono_measure (Measure.restrict_mono hrD le_rfl)) (V t)
    (fun i => ((hweak t ht).2.1 i).mono_measure (Measure.restrict_mono hrD le_rfl)) hCm hCc
  have hloc : (∫ p in closedBall p0 r, J 0 p) ≤ ∫ p in closedBall p0 r, J t p := by
    have hb0 : (∫ p in closedBall p0 r, J 0 p) = ∫ p in closedBall p0 r, old p :=
      integral_congr_ae (hbase.filter_mono (ae_mono (Measure.restrict_mono hrD le_rfl)))
    have hbt : (∫ p in closedBall p0 r, H t p) = ∫ p in closedBall p0 r, J t p :=
      integral_congr_ae ((hJae t ht).filter_mono (ae_mono (Measure.restrict_mono hrD le_rfl)))
    change C.annulus.weightedEnergy B modulus = A.annulus.weightedEnergy B modulus +
      (∫ p in closedBall p0 r, H t p) - ∫ p in closedBall p0 r, old p at hBD
    rw [← hb0, hbt] at hBD
    linarith
  have hdiff : (∫ p in D, J t p - J 0 p) = ∫ p in closedBall p0 r, J t p - J 0 p := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_ball.measurableSet hrD
    intro p hpD
    have hnot : p ∉ tsupport phi := fun h =>
      (not_lt_of_ge hrl) ((lt_of_not_ge hpD.2).trans (hs h))
    simp only [J, U, Z, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport ℝ hnot, zero_apply, smul_zero, add_zero, sub_self]
  rw [integral_sub (hJI t ht) (hJI 0 hzero),
    integral_sub ((hJI t ht).mono_set hrD) ((hJI 0 hzero).mono_set hrD)] at hdiff
  change (∫ p in D, J 0 p) ≤ ∫ p in D, J t p
  linarith

end PoincareConjecture.M64FreeWeakPhaseAnnulus
