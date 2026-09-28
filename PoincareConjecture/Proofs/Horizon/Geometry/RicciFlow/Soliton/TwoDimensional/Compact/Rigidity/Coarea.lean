import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.LevelArea
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Interval
import Mathlib.Topology.UrysohnsLemma

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] {g : RiemannianMetric 2 M}

theorem integral_comp_potential_slab_of_levelArea_ratio (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {a b c : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, f x ∈ Icc a b → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0)
    {q : ℝ → ℝ} (hQ : ∀ x, f x ∈ Icc a b → D.levelQ f x = q (f x))
    (harea : ∀ t ∈ Icc a b, g.regularLevelArea hf t / Real.sqrt (q t) = c)
    {H : ℝ → ℝ} (hH : Continuous H) :
    (∫ x in f ⁻¹' Icc a b, H (f x) ∂g.volumeMeasure) =
      c * ∫ t in Icc a b, H t := by
  let U := g.regularDomain hf
  have hKU : f ⁻¹' Icc a b ⊆ U := fun x hx =>
    (g.mem_regularDomain_iff hf x).mpr (hreg x hx)
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) M
  obtain ⟨χ, hχone, hχcompact, hχsupport, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hcompact U.isOpen hKU
  let s : M → ℝ := fun x => g.tangentNorm x (g.gradient f x)
  have hscont : Continuous s := g.continuous_tangentNorm_gradient hf
  have hsne (x : M) (hx : x ∈ U) : s x ≠ 0 :=
    ((g.tangentNorm_gradient_pos_iff f x).mpr (g.regularDomain_regular hf x hx)).ne'
  let P : M → ℝ := fun x => χ x * (H (f x) / s x)
  have hPs : tsupport P ⊆ U := tsupport_mul_subset_left.trans hχsupport
  have hPc : HasCompactSupport P := (show HasCompactSupport (χ : M → ℝ) from hχcompact).mul_right
  have hP : Continuous P :=
    (χ.continuous.continuousOn.mul
      ((hH.comp hf.continuous).continuousOn.div hscont.continuousOn hsne)).continuous_of_tsupport_subset
        U.isOpen hPs
  have hPA (x : M) (hx : x ∈ f ⁻¹' Icc a b) : P x * s x = H (f x) := by
    dsimp only [P]
    rw [hχone hx, Pi.one_apply, one_mul, div_mul_cancel₀ _ (hsne x (hKU hx))]
  calc
    (∫ x in f ⁻¹' Icc a b, H (f x) ∂g.volumeMeasure) =
        ∫ x in f ⁻¹' Icc a b, P x * s x ∂g.volumeMeasure := by
      apply setIntegral_congr_fun (isClosed_Icc.preimage hf.continuous).measurableSet
      intro x hx
      exact (hPA x hx).symm
    _ = ∫ t in Icc a b, ∫ z, P (openLevelIncl f U t z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t :=
      g.integral_coarea_Icc hf U (g.regularDomain_regular hf) hP hPc hPs a b
    _ = ∫ t in Icc a b, c * H t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      have heq : (fun z : openLevelSet f U t => P (openLevelIncl f U t z)) =
          fun _ => H t / Real.sqrt (q t) := by
        funext z
        have hzt : f (openLevelIncl f U t z) = t := z.2
        have hz : openLevelIncl f U t z ∈ f ⁻¹' Icc a b := by
          change f (openLevelIncl f U t z) ∈ Icc a b
          rwa [hzt]
        dsimp only [P]
        rw [hχone hz, Pi.one_apply, one_mul, hzt]
        change H t / Real.sqrt (D.levelQ f _) = _
        rw [hQ _ hz, hzt]
      dsimp only
      rw [heq, integral_const]
      change g.regularLevelArea hf t * (H t / Real.sqrt (q t)) = c * H t
      rw [show g.regularLevelArea hf t * (H t / Real.sqrt (q t)) =
        (g.regularLevelArea hf t / Real.sqrt (q t)) * H t by ring, harea t ht]
    _ = c * ∫ t in Icc a b, H t := integral_const_mul _ _

end PoincareConjecture.LeviCivitaData
