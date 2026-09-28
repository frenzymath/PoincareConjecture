import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.SphereProjection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.LocalInverse
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem localDiffeomorphAt_projection_chart_on_rim
    {F : E2 → E3} {V : Set E2} (hV : IsOpen V)
    (hcircle : sphere (0 : E2) 1 ⊆ V) (hF : ContDiffOn Real ∞ F V)
    {r : Real} (hr : 1 < r)
    (houter : MapsTo F (closedBall (0 : E2) r \ ball 0 1) (sphere (0 : E3) 1))
    (hinj : ∀ q ∈ sphere (0 : E2) 1, Injective (fderiv Real F q))
    (m : OpenPartialHomeomorph E2 S2)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target)
    (htarget : ∀ q ∈ sphere (0 : E2) 1, sphereProjection (F q) ∈ m.target) :
    ∀ q ∈ sphere (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (m.symm ∘ sphereProjection ∘ F) q := by
  let P : E2 → S2 := sphereProjection ∘ F
  let k : E2 → E2 := m.symm ∘ P
  let V₀ : Set E2 := V ∩ F ⁻¹' ({0}ᶜ : Set E3)
  have hV₀ : IsOpen V₀ := hF.continuousOn.isOpen_inter_preimage hV
    isClosed_singleton.isOpen_compl
  have hFP (q : E2) (hq : q ∈ V₀) : ContMDiffAt (𝓡 2) (𝓡 2) ∞ P q :=
    (contMDiffAt_sphereProjection hq.2).comp q
      ((hF q hq.1).contDiffAt (hV.mem_nhds hq.1)).contMDiffAt
  have hP : ContMDiffOn (𝓡 2) (𝓡 2) ∞ P V₀ :=
    fun q hq => (hFP q hq).contMDiffWithinAt
  let W : Set E2 := V₀ ∩ P ⁻¹' m.target
  have hW : IsOpen W := hP.continuousOn.isOpen_inter_preimage hV₀ m.open_target
  have hcircleW : sphere (0 : E2) 1 ⊆ W := by
    intro q hq
    have hqo : q ∈ closedBall (0 : E2) r \ ball 0 1 := by
      refine ⟨closedBall_subset_closedBall hr.le (sphere_subset_closedBall hq), ?_⟩
      exact fun hx => (ne_of_lt (mem_ball.mp hx)) (mem_sphere.mp hq)
    exact ⟨⟨hcircle hq, ne_zero_of_mem_unit_sphere ⟨F q, houter hqo⟩⟩, htarget q hq⟩
  have hk : ContDiffOn Real ∞ k W := by
    exact (hmi.comp (hP.mono inter_subset_left) (fun q hq => hq.2)).contDiffOn
  let mp : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
    { m with contMDiffOn_toFun := hm, contMDiffOn_invFun := hmi }
  have hkder (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      Injective (fderiv Real k q) := by
    have hPq := hFP q (hcircleW hq).1
    have hmloc := mp.symm.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (htarget q hq)
    have hder : Injective (mfderiv (𝓡 2) (𝓡 2) k q) := by
      change Injective (mfderiv (𝓡 2) (𝓡 2) ((mp.symm : S2 → E2) ∘ P) q)
      rw [mfderiv_comp q (hmloc.contMDiffAt.mdifferentiableAt (by simp))
        (hPq.mdifferentiableAt (by simp))]
      exact (hmloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
        (injective_mfderiv_sphereProjection_comp hr houter hq
          ((hF q (hcircle hq)).contDiffAt (hV.mem_nhds (hcircle hq))) (hinj q hq))
    simpa only [mfderiv_eq_fderiv, TangentSpace] using hder
  obtain ⟨k₀, hk₀, _, hk₀eq⟩ := Poincare.Parabolic.Interior.exists_compact_smooth_extension
    (isCompact_sphere (0 : E2) 1) hW hcircleW hk
  intro q hq
  have hk₀inj : Injective (fderiv Real k₀ q) := by
    rw [(hk₀eq q hq).fderiv_eq]
    exact hkder q hq
  have hlocal := localDiffeomorphAt_of_smooth_bijective_derivative hk₀
    ⟨hk₀inj, LinearMap.injective_iff_surjective.mp hk₀inj⟩
  exact hlocal.congr_of_eventuallyEq (hk₀eq q hq).symm

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
