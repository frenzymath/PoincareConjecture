import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapLocalFlux
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import PoincareConjecture.Proofs.M60.Mathlib.MetricPullbackForm
import Mathlib.MeasureTheory.Measure.OpenPos











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}





theorem m64AreaGram_entry_contDiffAt
    {f : LoopPlane → M} {p : LoopPlane}
    (hf : ContMDiffAt (𝓡 2) (𝓡 n) ∞ f p) (i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun q => m60AreaGram g f q i j) p := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have he (k : Fin 2) : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun q : LoopPlane => (⟨q, e k⟩ : TangentBundle (𝓡 2) LoopPlane)) p := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := e k)⟩
  have h := (M60.metricPullbackForm_contMDiffAt g hf).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial LoopPlane ℝ) (he i) (he j)
  have hg : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun q => m60AreaGram g f q i j) p := by
    simpa [M60.metricPullbackForm_apply, m60AreaGram, e] using
      (Bundle.contMDiffAt_totalSpace.mp h).2
  exact contMDiffAt_iff_contDiffAt.mp hg




theorem m64EnergyDensity_contDiffOn
    {f : LoopPlane → M} {O : Set LoopPlane} (hO : IsOpen O)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f O) :
    ContDiffOn ℝ ∞ (m60EnergyDensity g f) O := by
  intro p hp
  have hfp := hf.contMDiffAt (hO.mem_nhds hp)
  have h0 := m64AreaGram_entry_contDiffAt (g := g) hfp 0 0
  have h1 := m64AreaGram_entry_contDiffAt (g := g) hfp 1 1
  have h := (contDiffAt_const (c := (1 / 2 : ℝ))).mul (h0.add h1)
  change ContDiffWithinAt ℝ ∞
    (fun q => (1 / 2 : ℝ) * Matrix.trace (m60AreaGram g f q)) O p
  simp_rw [Matrix.trace_fin_two]
  exact h.contDiffWithinAt





theorem m64Annulus_conformal_on_interior_of_ae
    {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    ∀ p ∈ m64AnnulusInterior,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0 := by
  have hcont (i j : Fin 2) :
      ContinuousOn (fun p => m60AreaGram g A.map p i j) m64AnnulusInterior := by
    intro p hp
    exact (m64AreaGram_entry_contDiffAt
      (hf.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)) i j).continuousAt.continuousWithinAt
  rw [Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior] at hconformal
  have hclosure : m64AnnulusInterior ⊆ closure (interior m64AnnulusInterior) := by
    rw [isOpen_m64AnnulusInterior.interior_eq]
    exact subset_closure
  have hdiag := MeasureTheory.Measure.eqOn_of_ae_eq (hconformal.mono fun _ h => h.1)
    (hcont 0 0) (hcont 1 1) hclosure
  have hcross := MeasureTheory.Measure.eqOn_of_ae_eq (hconformal.mono fun _ h => h.2)
    (hcont 0 1) continuousOn_const hclosure
  exact fun p hp => ⟨hdiag hp, hcross hp⟩

end PoincareConjecture
