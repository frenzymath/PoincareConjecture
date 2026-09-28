import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityLocalMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedCoordinateVariation













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

set_option maxHeartbeats 1600000 in




theorem weighted_affine_chart_energy_minimum
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (modulus : ℝ)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    (b : M) {u phi : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (hRS : closedBall a R ⊆ S)
    (hu : ContinuousOn u (closedBall a R)) (hp : ContDiff ℝ ∞ phi)
    (hps : tsupport phi ⊆ ball a ((R / 4) * Real.exp (-1)))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R))
    (hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (closedBall a R))
    {delta : ℝ} (hdelta : 0 < delta)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 n) b).target)
    (hrange : ∀ t : ℝ, |t| < delta →
      MapsTo (fun p => u p + t • phi p) (closedBall a R) K) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let J := fun (t : ℝ) (p : LoopPlane) =>
      (modulus * G (u p + t • phi p)
          (W 0 p + t • fderiv ℝ phi p (EuclideanSpace.single 0 1))
          (W 0 p + t • fderiv ℝ phi p (EuclideanSpace.single 0 1)) +
        modulus⁻¹ * G (u p + t • phi p)
          (W 1 p + t • fderiv ℝ phi p (EuclideanSpace.single 1 1))
          (W 1 p + t • fderiv ℝ phi p (EuclideanSpace.single 1 1))) / 2
    ∀ t : ℝ, |t| < delta → IntegrableOn (J t) (ball a (R / 2)) ∧
      (∫ p in ball a (R / 2), J 0 p) ≤ ∫ p in ball a (R / 2), J t p := by
  classical
  let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
  let c := extChartAt (𝓡 n) b
  let G := g.pullbackCoefficients c.symm
  let U := fun (t : ℝ) (p : LoopPlane) => u p + t • phi p
  let Z := fun (t : ℝ) (i : Fin 2) (p : LoopPlane) =>
    W i p + t • fderiv ℝ phi p (EuclideanSpace.single i 1)
  let f := fun t => c.symm ∘ U t
  let V := fun (t : ℝ) (i : Fin 2) (p : LoopPlane) =>
    fderiv ℝ (e ∘ c.symm) (U t p) (Z t i p)
  let J := fun (t : ℝ) (p : LoopPlane) =>
    (modulus * G (U t p) (Z t 0 p) (Z t 0 p) +
      modulus⁻¹ * G (U t p) (Z t 1 p) (Z t 1 p)) / 2
  let H := fun (t : ℝ) (p : LoopPlane) =>
    (modulus * Q (f t p) (V t 0 p) (V t 0 p) +
      modulus⁻¹ * Q (f t p) (V t 1 p) (V t 1 p)) / 2
  let old := fun p =>
    (modulus * Q (A.map p) (A.column 0 p) (A.column 0 p) +
      modulus⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2
  let D := ball a (R / 2)
  have hhalf : 0 < R / 2 := half_pos hR
  have hquarter : 0 < R / 4 := div_pos hR (by norm_num)
  have hDR : D ⊆ closedBall a R :=
    (ball_subset_ball (by linarith)).trans ball_subset_closedBall
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
  have hJ (t : ℝ) (ht : |t| < delta) : EqOn (H t) (J t) D := by
    intro p hpD
    have hy := hKt (hrange t ht (hDR hpD))
    dsimp only [H, J, f, Function.comp_apply, V]
    rw [m64InverseChart_observed_metric g e he Q hdiag b hy,
      m64InverseChart_observed_metric g e he Q hdiag b hy]
  have hfm (t : ℝ) (ht : |t| < delta) : AEStronglyMeasurable (f t) (volume.restrict D) :=
    hei.aestronglyMeasurable_comp_iff.mp (hweak t ht).1.aestronglyMeasurable
  have hJae (t : ℝ) (ht : |t| < delta) : H t =ᵐ[volume.restrict D] J t := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hpD
    exact hJ t ht hpD
  have hHI (t : ℝ) (ht : |t| < delta) : IntegrableOn (H t) D :=
    (((m64VariableModulus_column_integrable Q hQ hb (f t) (hfm t ht)
      (V t 0) ((hweak t ht).2.1 0)).const_mul modulus).add
        ((m64VariableModulus_column_integrable Q hQ hb (f t) (hfm t ht)
          (V t 1) ((hweak t ht).2.1 1)).const_mul modulus⁻¹)).div_const 2
  have hJI (t : ℝ) (ht : |t| < delta) : IntegrableOn (J t) D :=
    (hHI t ht).congr (hJae t ht)
  have hf0 (p : LoopPlane) (hpR : p ∈ closedBall a R) : f 0 p = A.map p := by
    simpa only [f, U, zero_smul, add_zero] using hmap hpR
  have hV0 : ∀ i, V 0 i =ᵐ[volume.restrict D] (A.column i : LoopPlane → E) := by
    apply m64WeakColumns_ae_eq isOpen_ball (hweak 0 hzero).2.1
      (fun i => (Lp.memLp (A.column i)).mono_measure (Measure.restrict_mono hDS le_rfl))
      (hweak 0 hzero).2.2.1 (fun i j => (A.weak_partial i j).restrict isOpen_ball hDS)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with p hpD
    exact congrArg e (hf0 p (hDR hpD))
  have hbase : J 0 =ᵐ[volume.restrict D] old := by
    filter_upwards [hJae 0 hzero, hV0 0, hV0 1,
      ae_restrict_mem isOpen_ball.measurableSet] with p hJp h0 h1 hpD
    rw [← hJp]
    dsimp only [H, old]
    rw [hf0 p (hDR hpD), h0, h1]
  change ∀ t : ℝ, |t| < delta → IntegrableOn (J t) D ∧
    (∫ p in D, J 0 p) ≤ ∫ p in D, J t p
  intro t ht
  refine ⟨hJI t ht, ?_⟩
  have hmatch (p : LoopPlane) (hl : (R / 4) * Real.exp (-1) ≤ dist p a)
      (hh : dist p a ≤ R / 4) : f t p = A.map p := by
    have hnot : p ∉ tsupport phi := fun h => (not_lt_of_ge hl) (hps h)
    have hpR : p ∈ closedBall a R := hh.trans (by linarith)
    simpa only [f, U, Function.comp_apply, image_eq_zero_of_notMem_tsupport hnot,
      smul_zero, add_zero] using hmap hpR
  have hquarterD : closedBall a (R / 4) ⊆ D := closedBall_subset_ball (by linarith)
  obtain ⟨r, hr, hrl, hrh, B, hBm, hBc⟩ :=
    A.exists_replacement_of_outer_agreement isOpen_ball a hquarter hquarterD
      (hquarterD.trans hDS) (f t) (V t) (hweak t ht).1 (hweak t ht).2.1
      (hweak t ht).2.2.1 (hweak t ht).2.2.2 hmatch
  have hrD : closedBall a r ⊆ D :=
    (closedBall_subset_closedBall hrh).trans hquarterD
  have hBD := m64VariableModulus_replacement_energy Q hQ hei hb modulus A B
    isClosed_closedBall.measurableSet (hrD.trans hDS) (f t)
    ((hfm t ht).mono_measure (Measure.restrict_mono hrD le_rfl)) (V t)
    (fun i => ((hweak t ht).2.1 i).mono_measure (Measure.restrict_mono hrD le_rfl)) hBm hBc
  have hloc : (∫ p in closedBall a r, J 0 p) ≤ ∫ p in closedBall a r, J t p := by
    have hb0 : (∫ p in closedBall a r, J 0 p) = ∫ p in closedBall a r, old p :=
      integral_congr_ae (hbase.filter_mono (ae_mono (Measure.restrict_mono hrD le_rfl)))
    have hbt : (∫ p in closedBall a r, H t p) = ∫ p in closedBall a r, J t p :=
      integral_congr_ae ((hJae t ht).filter_mono (ae_mono (Measure.restrict_mono hrD le_rfl)))
    change B.weightedEnergy Q modulus = A.weightedEnergy Q modulus +
      (∫ p in closedBall a r, H t p) - ∫ p in closedBall a r, old p at hBD
    rw [← hb0, hbt] at hBD
    linarith [hmin B]
  have hdiff : (∫ p in D, J t p - J 0 p) =
      ∫ p in closedBall a r, J t p - J 0 p := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_ball.measurableSet hrD
    intro p hpD
    have hnot : p ∉ tsupport phi := by
      intro hpS
      have hdist : r < dist p a := lt_of_not_ge hpD.2
      exact (not_lt_of_ge hrl) (hdist.trans (hps hpS))
    simp only [J, U, Z, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport ℝ hnot, zero_apply, smul_zero, add_zero, sub_self]
  rw [integral_sub (hJI t ht) (hJI 0 hzero),
    integral_sub ((hJI t ht).mono_set hrD) ((hJI 0 hzero).mono_set hrD)] at hdiff
  linarith




theorem weighted_interior_coordinate_variation_eq_zero
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (modulus : ℝ)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    (b : M) {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (hRS : closedBall a R ⊆ S)
    (hu : Continuous u)
    (huT : MapsTo u (closedBall a R) (extChartAt (𝓡 n) b).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R))
    (hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (closedBall a R))
    (phi : LoopPlane → EuclideanSpace ℝ (Fin n)) (hp : ContDiff ℝ ∞ phi)
    (hps : tsupport phi ⊆ ball a ((R / 4) * Real.exp (-1))) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let rate := fun p =>
      (modulus * (fderiv ℝ G (u p) (phi p) (W 0 p) (W 0 p) +
          2 * G (u p) (W 0 p) (fderiv ℝ phi p (EuclideanSpace.single 0 1))) +
        modulus⁻¹ * (fderiv ℝ G (u p) (phi p) (W 1 p) (W 1 p) +
          2 * G (u p) (W 1 p) (fderiv ℝ phi p (EuclideanSpace.single 1 1)))) / 2
    IntegrableOn rate (ball a (R / 2)) ∧ (∫ p in ball a (R / 2), rate p) = 0 := by
  obtain ⟨delta, K, hd, hK, hKt, hrange⟩ := m64_affine_variation_compact_range
    (isCompact_closedBall a R) hu.continuousOn hp.continuous.continuousOn
    (isOpen_extChartAt_target b) huT
  have hlocal := A.weighted_affine_chart_energy_minimum g he hei Q hQ hb hdiag
    modulus hmin b hR hRS hu.continuousOn hp hps hW hw hmap hd hK hKt hrange
  have hhalf : closedBall a (R / 2) ⊆ closedBall a R :=
    closedBall_subset_closedBall (half_le_self hR.le)
  have hWH (i : Fin 2) : MemLp (W i) 2 (volume.restrict (ball a (R / 2))) :=
    (hW i).mono_measure (Measure.restrict_mono (ball_subset_ball (half_le_self hR.le)) le_rfl)
  have hvar := m64WeightedCoordinate_integral_firstVariation g b modulus u phi hu hp W
    a (R / 2) hWH hK hKt hd (fun t ht p hp => hrange t ht (hhalf hp))
  refine ⟨hvar.1, ?_⟩
  apply IsLocalMin.hasDerivAt_eq_zero ?_ hvar.2
  filter_upwards [ball_mem_nhds (0 : ℝ) hd] with t ht
  exact (hlocal t (by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht)).2

end PoincareConjecture.M64ObservedWeakAnnulus
