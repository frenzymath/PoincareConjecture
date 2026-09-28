import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates
import PoincareConjecture.Proofs.M60.Mathlib.CompactSupportIntegralDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64AnnulusEnergy_hasDerivAt_of_supported_variation
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {O K : Set LoopPlane} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) (hKdomain : K ⊆ m64AnnulusDomain)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O))
    (hfix : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ z ∉ K,
      v (s, z) = v (0, z))
    (hint : ∀ s ∈ Ioo (-epsilon) epsilon,
      IntegrableOn (m60EnergyDensity g (fun z => v (s, z)))
        m64AnnulusDomain volume) :
    let D := fun q : ℝ × LoopPlane =>
      m60EnergyDensity g (fun z => v (q.1, z)) q.2 -
        m60EnergyDensity g (fun z => v (0, z)) q.2
    Integrable (fun z => fderiv ℝ D (0, z) (1, 0)) volume ∧
      HasDerivAt
        (fun s => ∫ z in m64AnnulusDomain,
          m60EnergyDensity g (fun y => v (s, y)) z)
        (∫ z, fderiv ℝ D (0, z) (1, 0)) 0 := by
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun z => v (q.1, z)) q.2
  let D := fun q : ℝ × LoopPlane => E q - E (0, q.2)
  let G := fun s z => fderiv ℝ D (s, z) (1, 0)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hopen : IsOpen (Ioo (-epsilon) epsilon ×ˢ (univ : Set LoopPlane)) :=
    isOpen_Ioo.prod isOpen_univ
  have hDzero (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon)
      (z : LoopPlane) (hz : z ∉ K) : D (s, z) = 0 := by
    apply sub_eq_zero.mpr
    apply m60EnergyDensity_congr_of_eventuallyEq g
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact hfix s hs y hy
  have hD : ContDiffOn ℝ ∞ D (Ioo (-epsilon) epsilon ×ˢ univ) := by
    intro q hq
    by_cases hqO : q.2 ∈ O
    · have hEq : ContDiffAt ℝ ∞ E q := m60EnergyDensity_family_contDiffAt g
        (hv.contMDiffAt ((isOpen_Ioo.prod hO).mem_nhds ⟨hq.1, hqO⟩))
      have hEzero : ContDiffAt ℝ ∞ E (0, q.2) := m60EnergyDensity_family_contDiffAt g
        (hv.contMDiffAt ((isOpen_Ioo.prod hO).mem_nhds ⟨hzero, hqO⟩))
      exact (hEq.sub (hEzero.comp q
        (contDiffAt_const.prodMk contDiffAt_snd))).contDiffWithinAt
    · have hqK : q.2 ∉ K := fun h => hqO (hKO h)
      have hconst : ContDiffAt ℝ ∞ D q :=
        (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (by
          filter_upwards [(isOpen_Ioo.prod hK.isClosed.isOpen_compl).mem_nhds
            ⟨hq.1, hqK⟩] with p hp
          exact hDzero p.1 hp.1 p.2 hp.2)
      exact hconst.contDiffWithinAt
  have hDs (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      Continuous (fun z => D (s, z)) :=
    hD.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hs, mem_univ z⟩)
  have hG : ContinuousOn (Function.uncurry G)
      (Ioo (-epsilon) epsilon ×ˢ univ) :=
    ((hD.fderiv_of_isOpen hopen (m := ∞) (by simp)).clm_apply
      contDiffOn_const).continuousOn
  have hder (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) (z : LoopPlane) :
      HasDerivAt (fun t => D (t, z)) (G s z) s := by
    have hDp : ContDiffAt ℝ ∞ D (s, z) :=
      hD.contDiffAt (hopen.mem_nhds ⟨hs, mem_univ z⟩)
    have hd := hDp.differentiableAt (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))
  obtain ⟨hGint, hderiv⟩ := M60.hasDerivAt_integral_of_common_compact_support
    (μ := volume) (F := fun s z => D (s, z)) (F' := G) hK hepsilon
    hDs hG hder hDzero
  refine ⟨hGint, ?_⟩
  have hfull (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      (∫ z, D (s, z)) =
        (∫ z in m64AnnulusDomain, E (s, z)) -
          ∫ z in m64AnnulusDomain, E (0, z) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_sub (hint s hs) (hint 0 hzero)
    · intro z hz
      exact hDzero s hs z (fun h => hz (hKdomain h))
  apply (hderiv.add_const (∫ z in m64AnnulusDomain, E (0, z))).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
  rw [hfull s hs]
  change (∫ z in m64AnnulusDomain, E (s, z)) =
    (∫ z in m64AnnulusDomain, E (s, z)) -
      (∫ z in m64AnnulusDomain, E (0, z)) +
        ∫ z in m64AnnulusDomain, E (0, z)
  ring

end PoincareConjecture
