import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteMotionTangent
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusClosedConformality





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




def m64AnnulusWithinGram (g : RiemannianMetric n M) (f : LoopPlane → M)
    (p : LoopPlane) (i j : Fin 2) : ℝ :=
  g.inner (f p)
    (mfderivWithin (𝓡 2) (𝓡 n) f m64AnnulusDomain p
      (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (mfderivWithin (𝓡 2) (𝓡 n) f m64AnnulusDomain p
      (EuclideanSpace.basisFun (Fin 2) ℝ j))





theorem m64AnnulusWithinGram_continuousOn (g : RiemannianMetric n M)
    {f : LoopPlane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain)
    (i j : Fin 2) :
    ContinuousOn (fun p => m64AnnulusWithinGram g f p i j) m64AnnulusDomain := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (m64AnnulusWithinColumn_continuousOn hf i).inner_bundle
    (m64AnnulusWithinColumn_continuousOn hf j)





theorem m64AnnulusWithinGram_eq_gram (g : RiemannianMetric n M)
    (f : LoopPlane → M) {p : LoopPlane} (hp : p ∈ m64AnnulusInterior) (i j : Fin 2) :
    m64AnnulusWithinGram g f p i j = m60AreaGram g f p i j := by
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hpi := (interior_maximal hsub isOpen_m64AnnulusInterior) hp
  unfold m64AnnulusWithinGram m60AreaGram
  rw [mfderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hpi)]





theorem m64AnnulusWithinGram_modulus_conformal
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) (r : ℝ)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusDomain)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    ∀ p ∈ m64AnnulusDomain,
      r * m64AnnulusWithinGram g A.map p 0 0 =
        r⁻¹ * m64AnnulusWithinGram g A.map p 1 1 ∧
        m64AnnulusWithinGram g A.map p 0 1 = 0 := by
  have hi := m64Annulus_modulus_conformal_on_interior_of_ae A r hAi hconformal
  have hc := m64AnnulusWithinGram_continuousOn g hAc
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hclosure : m64AnnulusDomain ⊆ closure m64AnnulusInterior := by
    rw [m64AnnulusInterior_closure]
  have hdiag : EqOn (fun p => r * m64AnnulusWithinGram g A.map p 0 0)
      (fun p => r⁻¹ * m64AnnulusWithinGram g A.map p 1 1) m64AnnulusInterior := by
    intro p hp
    dsimp only
    rw [m64AnnulusWithinGram_eq_gram g A.map hp 0 0,
      m64AnnulusWithinGram_eq_gram g A.map hp 1 1]
    exact (hi p hp).1
  have hcross : EqOn (fun p => m64AnnulusWithinGram g A.map p 0 1)
      (fun _ => (0 : ℝ)) m64AnnulusInterior := by
    intro p hp
    dsimp only
    rw [m64AnnulusWithinGram_eq_gram g A.map hp 0 1]
    exact (hi p hp).2
  exact fun p hp => ⟨hdiag.of_subset_closure (continuousOn_const.mul (hc 0 0))
    (continuousOn_const.mul (hc 1 1)) hsub hclosure hp,
    hcross.of_subset_closure (hc 0 1) continuousOn_const hsub hclosure hp⟩

end PoincareConjecture
