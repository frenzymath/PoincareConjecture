import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates
import PoincareConjecture.Proofs.M60.Mathlib.CompactSupportIntegralDerivative
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60SphereEnergyDensity_family_contDiffOn (g : RiemannianMetric n M)
    {v : ℝ × UnitTwoSphere → M} {ε : ℝ}
    (hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v
      (Ioo (-ε) ε ×ˢ (univ : Set UnitTwoSphere))) :
    ContDiffOn ℝ ∞ (fun q : ℝ × LoopPlane =>
      m60SphereEnergyDensity g (fun p => v (q.1, p)) q.2)
      (Ioo (-ε) ε ×ˢ (univ : Set LoopPlane)) := by
  have hfst : ContMDiff 𝓘(ℝ, ℝ × LoopPlane) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × LoopPlane → ℝ) := contDiff_fst.contMDiff
  have hsnd : ContMDiff 𝓘(ℝ, ℝ × LoopPlane) (𝓡 2) ∞
      (Prod.snd : ℝ × LoopPlane → LoopPlane) := contDiff_snd.contMDiff
  have hparam := hfst.prodMk (m60SphereParameter_contMDiff.comp hsnd)
  intro q hq
  have hvq : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v
      (q.1, m60SphereParameter q.2) := hv.contMDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hq.1, mem_univ (m60SphereParameter q.2)⟩)
  exact (m60EnergyDensity_family_contDiffAt g (hvq.comp q (hparam q))).contDiffWithinAt

theorem m60SphereEnergy_hasDerivAt_of_supported_variation (g : RiemannianMetric n M)
    {v : ℝ × UnitTwoSphere → M} {ε : ℝ} (hε : 0 < ε)
    (hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v
      (Ioo (-ε) ε ×ˢ (univ : Set UnitTwoSphere)))
    {K : Set LoopPlane} (hK : IsCompact K)
    (hfix : ∀ s ∈ Ioo (-ε) ε, ∀ z ∉ K,
      v (s, m60SphereParameter z) = v (0, m60SphereParameter z)) :
    let E := fun q : ℝ × LoopPlane => m60SphereEnergyDensity g (fun p => v (q.1, p)) q.2
    Integrable (fun z => fderiv ℝ E (0, z) (1, 0)) volume ∧
      HasDerivAt (fun s => m60SphereEnergy g (fun p => v (s, p)))
        (∫ z : LoopPlane, fderiv ℝ E (0, z) (1, 0)) 0 := by
  let E := fun q : ℝ × LoopPlane => m60SphereEnergyDensity g (fun p => v (q.1, p)) q.2
  let G := fun s z => fderiv ℝ E (s, z) (1, 0)
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hO : IsOpen (Ioo (-ε) ε ×ˢ (univ : Set LoopPlane)) := isOpen_Ioo.prod isOpen_univ
  have hE : ContDiffOn ℝ ∞ E (Ioo (-ε) ε ×ˢ (univ : Set LoopPlane)) :=
    m60SphereEnergyDensity_family_contDiffOn g hv
  have hEs (s : ℝ) (hs : s ∈ Ioo (-ε) ε) : Continuous (fun z => E (s, z)) :=
    hE.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hs, mem_univ z⟩)
  have hG : ContinuousOn (Function.uncurry G) (Ioo (-ε) ε ×ˢ (univ : Set LoopPlane)) :=
    ((hE.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hdiff (s : ℝ) (hs : s ∈ Ioo (-ε) ε) (z : LoopPlane) :
      HasDerivAt (fun t => E (t, z) - E (0, z)) (G s z) s := by
    have hEp : ContDiffAt ℝ ∞ E (s, z) := hE.contDiffAt (hO.mem_nhds ⟨hs, mem_univ z⟩)
    have hd := hEp.differentiableAt (by simp)
    have ht : HasDerivAt (fun t : ℝ => (t, z)) (1, 0) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
    exact (hd.hasFDerivAt.comp_hasDerivAt (l := E) (f := fun t : ℝ => (t, z)) s ht).sub_const _
  have hsupp (s : ℝ) (hs : s ∈ Ioo (-ε) ε) (z : LoopPlane) (hz : z ∉ K) :
      E (s, z) - E (0, z) = 0 := by
    apply sub_eq_zero.mpr
    apply m60EnergyDensity_congr_of_eventuallyEq g
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact hfix s hs y hy
  obtain ⟨hGint, hd⟩ := M60.hasDerivAt_integral_of_common_compact_support
    (μ := volume) (F := fun s z => E (s, z) - E (0, z)) (F' := G) hK hε
    (fun s hs => (hEs s hs).sub (hEs 0 hzero)) hG hdiff hsupp
  refine ⟨hGint, ?_⟩
  have hvSlice (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :
      ContMDiff (𝓡 2) (𝓡 n) ∞ (fun p => v (s, p)) := by
    have hi : ContMDiff (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ∞
        (fun p : UnitTwoSphere => (s, p)) := contMDiff_const.prodMk contMDiff_id
    intro p
    have hvp : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v (s, p) := hv.contMDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ p⟩)
    exact hvp.comp p (hi p)
  have hEi (s : ℝ) (hs : s ∈ Ioo (-ε) ε) : Integrable (fun z => E (s, z)) volume := by
    change Integrable (m60SphereEnergyDensity g (fun p : UnitTwoSphere => v (s, p))) volume
    exact m60SphereEnergyDensity_integrable g (fun p : UnitTwoSphere => v (s, p))
      ((hvSlice s hs).of_le (by simp))
  apply (hd.add_const (m60SphereEnergy g (fun p => v (0, p)))).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
  dsimp only [m60SphereEnergy]
  rw [integral_sub (hEi s hs) (hEi 0 hzero)]
  change (∫ z : LoopPlane, E (s, z)) = (∫ z : LoopPlane, E (s, z)) -
    (∫ z : LoopPlane, E (0, z)) + ∫ z : LoopPlane, E (0, z)
  ring

end PoincareConjecture
