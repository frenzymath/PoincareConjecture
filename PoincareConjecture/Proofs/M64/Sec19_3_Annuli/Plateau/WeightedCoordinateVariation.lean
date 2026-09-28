import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakQuadraticVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityInverseChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64WeightedCoordinateVariation_bilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance m64WeightedCoordinateVariation_bilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem m64ChartQuadratic_integrable
    (g : RiemannianMetric n M) (b : M)
    {U V : LoopPlane → E} {a : LoopPlane} {R : ℝ}
    (hU : ContinuousOn U (ball a R)) (hV : MemLp V 2 (volume.restrict (ball a R)))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 n) b).target)
    (hrange : MapsTo U (ball a R) K) :
    IntegrableOn (fun p => g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (U p) (V p) (V p))
      (ball a R) := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  have hG : ContinuousOn G K := (g.contDiffOn_chartCoefficients b).continuousOn.mono hKt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG
  have hGm := (hG.comp hU hrange).aestronglyMeasurable (μ := volume) measurableSet_ball
  have hm : AEStronglyMeasurable (fun p => G (U p) (V p) (V p)) (volume.restrict (ball a R)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hGm.prodMk hV.aestronglyMeasurable)).prodMk hV.aestronglyMeasurable)
  have hs : IntegrableOn (fun p => ‖V p‖ ^ 2) (ball a R) := by
    simpa only [pow_two, IntegrableOn] using memLp_one_iff_integrable.mp (hV.norm.mul' hV.norm)
  apply (hs.const_mul C).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
  calc
    _ ≤ ‖G (U p)‖ * ‖V p‖ * ‖V p‖ := (G (U p)).le_opNorm₂ _ _
    _ ≤ C * ‖V p‖ * ‖V p‖ := by gcongr; exact hC _ (hrange hp)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in

theorem m64WeightedCoordinate_integral_firstVariation
    (g : RiemannianMetric n M) (b : M) (modulus : ℝ)
    (u phi : LoopPlane → E) (hu : Continuous u) (hphi : ContDiff ℝ ∞ phi)
    (V : Fin 2 → LoopPlane → E) (a : LoopPlane) (R : ℝ)
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a R)))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 n) b).target)
    {delta : ℝ} (hdelta : 0 < delta)
    (hrange : ∀ t : ℝ, |t| < delta → ∀ p ∈ closedBall a R, u p + t • phi p ∈ K) :
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let D := fun (i : Fin 2) (p : LoopPlane) => fderiv ℝ phi p (EuclideanSpace.single i 1)
    let J := fun (t : ℝ) (p : LoopPlane) =>
      (modulus * G (u p + t • phi p) (V 0 p + t • D 0 p) (V 0 p + t • D 0 p) +
        modulus⁻¹ * G (u p + t • phi p) (V 1 p + t • D 1 p) (V 1 p + t • D 1 p)) / 2
    let rate := fun p =>
      (modulus * (fderiv ℝ G (u p) (phi p) (V 0 p) (V 0 p) +
          2 * G (u p) (V 0 p) (D 0 p)) +
        modulus⁻¹ * (fderiv ℝ G (u p) (phi p) (V 1 p) (V 1 p) +
          2 * G (u p) (V 1 p) (D 1 p))) / 2
    IntegrableOn rate (ball a R) ∧
      HasDerivAt (fun t : ℝ => ∫ p in ball a R, J t p) (∫ p in ball a R, rate p) 0 := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let D := fun (i : Fin 2) (p : LoopPlane) => fderiv ℝ phi p (EuclideanSpace.single i 1)
  let J := fun (i : Fin 2) (t : ℝ) (p : LoopPlane) =>
    G (u p + t • phi p) (V i p + t • D i p) (V i p + t • D i p)
  let dJ := fun (i : Fin 2) (p : LoopPlane) =>
    fderiv ℝ G (u p) (phi p) (V i p) (V i p) + 2 * G (u p) (V i p) (D i p)
  have hD (i : Fin 2) : Continuous (D i) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcol (i : Fin 2) : IntegrableOn (dJ i) (ball a R) ∧
      HasDerivAt (fun t : ℝ => ∫ p in ball a R, J i t p) (∫ p in ball a R, dJ i p) 0 := by
    have h := m64WeakQuadratic_integral_firstVariation g b u phi (V i) (D i)
      hu hphi.continuous (hD i) a R (hV i) hK hKt hdelta hrange
    have heq : (fun p => fderiv ℝ G (u p) (phi p) (V i p) (V i p) +
        G (u p) (D i p) (V i p) + G (u p) (V i p) (D i p)) = dJ i := by
      funext p
      have hsymm : G (u p) (D i p) (V i p) = G (u p) (V i p) (D i p) := g.symm _ _ _
      dsimp only [dJ]
      rw [hsymm]
      ring
    change IntegrableOn _ (ball a R) ∧ HasDerivAt _ _ (0 : ℝ) at h
    rw [heq] at h
    exact h
  have hJI (i : Fin 2) (t : ℝ) (ht : |t| < delta) : IntegrableOn (J i t) (ball a R) := by
    have hDM := m64MemLp_on_ball_of_continuous_closedBall (hD i).continuousOn 2 (a := a) (R := R)
    exact m64ChartQuadratic_integrable g b (hu.add (hphi.continuous.const_smul t)).continuousOn
      ((hV i).add (hDM.const_smul t)) hK hKt
      (fun p hp => hrange t ht p (ball_subset_closedBall hp))
  have hrate : IntegrableOn (fun p => (modulus * dJ 0 p + modulus⁻¹ * dJ 1 p) / 2)
      (ball a R) :=
    (((hcol 0).1.const_mul modulus).add ((hcol 1).1.const_mul modulus⁻¹)).div_const 2
  have hh := (((hcol 0).2.const_mul modulus).add ((hcol 1).2.const_mul modulus⁻¹)).div_const 2
  have hr : (modulus * (∫ p in ball a R, dJ 0 p) +
      modulus⁻¹ * (∫ p in ball a R, dJ 1 p)) / 2 =
      ∫ p in ball a R, (modulus * dJ 0 p + modulus⁻¹ * dJ 1 p) / 2 := by
    rw [integral_div, integral_add ((hcol 0).1.const_mul _) ((hcol 1).1.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hr] at hh
  refine ⟨hrate, hh.congr_of_eventuallyEq ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℝ) hdelta] with t ht
  have ht' : |t| < delta := by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht
  change (∫ p in ball a R, (modulus * J 0 t p + modulus⁻¹ * J 1 t p) / 2) = _
  rw [integral_div, integral_add ((hJI 0 t ht').const_mul _) ((hJI 1 t ht').const_mul _),
    integral_const_mul, integral_const_mul]
  rfl

end PoincareConjecture
