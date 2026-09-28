import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ClassicalCompletionEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationEnergy

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem m64AreaGram_congr_of_eventuallyEq (g : RiemannianMetric n M)
    {f h : LoopPlane → M} {p : LoopPlane} (hf : f =ᶠ[𝓝 p] h) :
    m60AreaGram g f p = m60AreaGram g h p := by
  have hi (u v : EuclideanSpace ℝ (Fin n)) : g.inner (f p) u v = g.inner (h p) u v :=
    congrArg (fun q : M => g.inner q u v) hf.eq_of_nhds
  simp only [m60AreaGram, hf.mfderiv_eq, hi]
  rfl

theorem m64Annulus_conformal_of_interior_completion
    (g : RiemannianMetric n M) {f h : LoopPlane → M} {r : ℝ}
    (heq : EqOn f h S)
    (hc : ∀ p ∈ S, r * m60AreaGram g h p 0 0 = r⁻¹ * m60AreaGram g h p 1 1 ∧
      m60AreaGram g h p 0 1 = 0) :
    ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g f p 0 0 = r⁻¹ * m60AreaGram g f p 1 1 ∧
        m60AreaGram g f p 0 1 = 0 := by
  rw [m64Annulus_restrict_closed_eq_interior]
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  have hgerm : f =ᶠ[𝓝 p] h := by
    filter_upwards [isOpen_interior.mem_nhds hp] with q hq
    exact heq hq
  rw [m64AreaGram_congr_of_eventuallyEq g hgerm]
  exact hc p hp

theorem M64ObservedWeakAnnulus.area_eq_of_conformal_completion
    {e : M → E} {c0 c1 : ℝ → M}
    (W : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {g : RiemannianMetric n M} (A : M64Annulus g c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (hmap : EqOn A.map W.map S) (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    {r : ℝ} (hr : 0 < r)
    (hc : ∀ p ∈ S,
      r * m60AreaGram g W.map p 0 0 = r⁻¹ * m60AreaGram g W.map p 1 1 ∧
        m60AreaGram g W.map p 0 1 = 0) : A.area = W.weightedEnergy B r := by
  have hae : A.map =ᵐ[volume.restrict S] W.map :=
    (ae_restrict_mem isOpen_interior.measurableSet).mono fun _ hp => hmap hp
  exact (m64_weightedEnergy_eq_area_of_ae_modulus_conformal A hr
    (m64Annulus_conformal_of_interior_completion g hmap hc)).symm.trans
      (W.weightedEnergy_eq_of_classical_completion A he B hdiag hae hA r).symm

end PoincareConjecture
