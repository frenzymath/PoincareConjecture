import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySupportedComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityChartEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

set_option maxHeartbeats 1600000 in

theorem weighted_lower_affine_chart_minimum
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (w : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q w) (mfderiv (𝓡 n) (𝓡 m) e q w) = g.inner q w w)
    (modulus : ℝ)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    (v : LoopPlane → M) (hvae : v =ᵐ[volume.restrict O] A.lowerExtensionMap)
    (hvfixed : ∀ p ∈ O, p 1 < 0 → v p = c0 (p 0))
    (b : M) {u phi : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (hRO : closedBall a R ⊆ O)
    (hu : ContinuousOn u (closedBall a R)) (hp : ContDiff ℝ ∞ phi)
    (hps : tsupport phi ⊆ ball a ((R / 4) * Real.exp (-1)))
    (hpzero : ∀ p : LoopPlane, p 1 ≤ 0 → phi p = 0)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball a R))
    (hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) v (closedBall a R))
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
  let V := fun (t : ℝ) (i : Fin 2) (p : LoopPlane) => fderiv ℝ (e ∘ c.symm) (U t p) (Z t i p)
  let J := fun (t : ℝ) (p : LoopPlane) =>
    (modulus * G (U t p) (Z t 0 p) (Z t 0 p) +
      modulus⁻¹ * G (U t p) (Z t 1 p) (Z t 1 p)) / 2
  let H := fun (t : ℝ) (p : LoopPlane) =>
    (modulus * Q (f t p) (V t 0 p) (V t 0 p) +
      modulus⁻¹ * Q (f t p) (V t 1 p) (V t 1 p)) / 2
  let old := fun p =>
    (modulus * Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 0 p) (A.lowerExtensionColumn 0 p) +
      modulus⁻¹ * Q (A.lowerExtensionMap p)
        (A.lowerExtensionColumn 1 p) (A.lowerExtensionColumn 1 p)) / 2
  let D := ball a (R / 2)
  have hhalf : 0 < R / 2 := half_pos hR
  have hquarter : 0 < R / 4 := div_pos hR (by norm_num)
  have hDR : D ⊆ closedBall a R :=
    (ball_subset_ball (by linarith)).trans ball_subset_closedBall
  have hDO : D ⊆ O := hDR.trans hRO
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
  have hf0 (p : LoopPlane) (hpR : p ∈ closedBall a R) : f 0 p = v p := by
    simpa only [f, U, zero_smul, add_zero] using hmap hpR
  have hbaseMap : (e ∘ f 0) =ᵐ[volume.restrict D] (e ∘ A.lowerExtensionMap) := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      ae_restrict_of_ae_restrict_of_subset hDO hvae] with p hpD hvp
    exact congrArg e ((hf0 p (hDR hpD)).trans hvp)
  have hV0 : ∀ i, V 0 i =ᵐ[volume.restrict D] A.lowerExtensionColumn i := by
    exact m64WeakColumns_ae_eq isOpen_ball (hweak 0 hzero).2.1
      (fun i => ((A.lower_extension_memLp hc0).2 i).mono_measure
        (Measure.restrict_mono hDO le_rfl)) (hweak 0 hzero).2.2.1
      (fun i j => (A.lower_extension_weak_partial hc0 i j).restrict isOpen_ball hDO) hbaseMap
  have hbase : J 0 =ᵐ[volume.restrict D] old := by
    filter_upwards [hJae 0 hzero, hV0 0, hV0 1,
      ae_restrict_mem isOpen_ball.measurableSet,
      ae_restrict_of_ae_restrict_of_subset hDO hvae] with p hJp h0 h1 hpD hvp
    rw [← hJp]
    dsimp only [H, old]
    rw [hf0 p (hDR hpD), hvp, h0, h1]
  change ∀ t : ℝ, |t| < delta → IntegrableOn (J t) D ∧ (∫ p in D, J 0 p) ≤ ∫ p in D, J t p
  intro t ht
  refine ⟨hJI t ht, ?_⟩
  have hmatch (p : LoopPlane) (hl : (R / 4) * Real.exp (-1) ≤ dist p a)
      (hh : dist p a ≤ R / 4) : f t p = v p := by
    have hnot : p ∉ tsupport phi := fun h => (not_lt_of_ge hl) (hps h)
    have hpR : p ∈ closedBall a R := hh.trans (by linarith)
    simpa only [f, U, Function.comp_apply, image_eq_zero_of_notMem_tsupport hnot,
      smul_zero, add_zero] using hmap hpR
  have hfixed (p : LoopPlane) (hpD : p ∈ D) (hp1 : p 1 < 0) : f t p = c0 (p 0) := by
    have heq : f t p = v p := by
      simpa only [f, U, Function.comp_apply, hpzero p hp1.le, smul_zero, add_zero]
        using hmap (hDR hpD)
    exact heq.trans (hvfixed p (hDO hpD) hp1)
  have hquarterD : closedBall a (R / 4) ⊆ D := closedBall_subset_ball (by linarith)
  obtain ⟨r, hr, hrl, hrh, hloc⟩ := A.exists_lower_weighted_comparison_of_outer_agreement
    hc0 Q hQ hei hb modulus hmin isOpen_ball hDO a hquarter hquarterD v (f t) hvae
    (V t) (hweak t ht).1 (hweak t ht).2.1 (hweak t ht).2.2.1
    (hweak t ht).2.2.2 hfixed hmatch
  have hrD : ball a r ⊆ D := (ball_subset_ball hrh).trans (ball_subset_ball (by linarith))
  have hb0 : (∫ p in ball a r, J 0 p) = ∫ p in ball a r, old p :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hrD hbase)
  have hbt : (∫ p in ball a r, H t p) = ∫ p in ball a r, J t p :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hrD (hJae t ht))
  change (∫ p in ball a r, old p) ≤ ∫ p in ball a r, H t p at hloc
  rw [← hb0, hbt] at hloc
  have hdiff : (∫ p in D, J t p - J 0 p) = ∫ p in ball a r, J t p - J 0 p := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_ball.measurableSet hrD
    intro p hpD
    have hnot : p ∉ tsupport phi := by
      intro hpS
      have hdist : r ≤ dist p a := not_lt.mp hpD.2
      exact (not_lt_of_ge (hrl.trans hdist)) (hps hpS)
    simp only [J, U, Z, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport ℝ hnot, zero_apply, smul_zero, add_zero, sub_self]
  rw [integral_sub (hJI t ht) (hJI 0 hzero),
    integral_sub ((hJI t ht).mono_set hrD) ((hJI 0 hzero).mono_set hrD)] at hdiff
  linarith

end PoincareConjecture.M64ObservedWeakAnnulus
