import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.AnnulusDerivative
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩


def sphereProjection (x : E3) : S2 := by
  classical
  exact if hx : x = 0 then ⟨EuclideanSpace.single 0 1, by simp⟩
    else ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem sphereProjection_coe {x : E3} (hx : x ≠ 0) :
    (sphereProjection x : E3) = ‖x‖⁻¹ • x := by simp [sphereProjection, hx]

@[simp] theorem sphereProjection_sphere (p : S2) : sphereProjection p = p := by
  apply Subtype.ext
  rw [sphereProjection_coe (ne_zero_of_mem_unit_sphere p), norm_eq_of_mem_sphere p]
  simp

theorem contMDiffAt_sphereProjection {x : E3} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) (𝓡 2) ∞ sphereProjection x := by
  let U : Opens E3 := ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩
  have hn : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞ (fun y : U => ‖(y : E3)‖) := by
    intro y
    exact (contDiffAt_norm Real y.property).contMDiffAt.comp y (contMDiff_subtype_val y)
  have hs : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => ‖(y : E3)‖⁻¹ • (y : E3)) :=
    (hn.inv₀ (fun y => norm_ne_zero_iff.mpr y.property)).smul contMDiff_subtype_val
  have hd : ContMDiff (𝓡 3) (𝓡 2) ∞ (fun y : U => sphereProjection y) := by
    have ht := hs.codRestrict_sphere (n := 2) (fun y => by
      rw [← sphereProjection_coe y.property]
      exact (sphereProjection y).property)
    apply ht.congr
    intro y
    exact Subtype.ext (sphereProjection_coe y.property)
  exact (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp (hd ⟨x, hx⟩)



theorem fderiv_sphereProjection_comp_eq
    {F : E2 → E3} {r : Real} (hr : 1 < r)
    (houter : MapsTo F (closedBall (0 : E2) r \ ball 0 1) (sphere (0 : E3) 1))
    {q : E2} (hq : q ∈ sphere (0 : E2) 1) (hF : DifferentiableAt Real F q) :
    fderiv Real (fun x => (sphereProjection (F x) : E3)) q = fderiv Real F q := by
  have hqouter : q ∈ closedBall (0 : E2) r \ ball 0 1 := by
    refine ⟨closedBall_subset_closedBall hr.le (sphere_subset_closedBall hq), ?_⟩
    exact fun h => (ne_of_lt (mem_ball.mp h)) (mem_sphere.mp hq)
  have hFq : F q ≠ 0 := ne_zero_of_mem_unit_sphere ⟨F q, houter hqouter⟩
  have hproj : ContDiffAt Real ∞ (fun y : E3 => (sphereProjection y : E3)) (F q) :=
    ((contMDiff_coe_sphere (n := 2) (m := ∞)).contMDiffAt.comp (F q)
      (contMDiffAt_sphereProjection hFq)).contDiffAt
  have hdiff := (hproj.differentiableAt (by simp)).comp q hF
  have heq : EqOn (fun x => (sphereProjection (F x) : E3)) F
      (closedBall (0 : E2) r \ ball 0 1) := by
    intro x hx
    exact congrArg Subtype.val (sphereProjection_sphere ⟨F x, houter hx⟩)
  exact fderiv_eq_of_eqOn_outer_annulus hr heq hq hdiff hF



theorem injective_mfderiv_sphereProjection_comp
    {F : E2 → E3} {r : Real} (hr : 1 < r)
    (houter : MapsTo F (closedBall (0 : E2) r \ ball 0 1) (sphere (0 : E3) 1))
    {q : E2} (hq : q ∈ sphere (0 : E2) 1) (hF : ContDiffAt Real ∞ F q)
    (hinj : Injective (fderiv Real F q)) :
    Injective (mfderiv (𝓡 2) (𝓡 2) (sphereProjection ∘ F) q) := by
  have hqouter : q ∈ closedBall (0 : E2) r \ ball 0 1 := by
    refine ⟨closedBall_subset_closedBall hr.le (sphere_subset_closedBall hq), ?_⟩
    exact fun h => (ne_of_lt (mem_ball.mp h)) (mem_sphere.mp hq)
  have hFq : F q ≠ 0 := ne_zero_of_mem_unit_sphere ⟨F q, houter hqouter⟩
  have hproj := (contMDiffAt_sphereProjection hFq).comp q hF.contMDiffAt
  have hcoe := contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3)
  have hchain := mfderiv_comp q (hcoe.mdifferentiable (by simp) _)
    (hproj.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hchain
  have hder : fderiv Real (Subtype.val ∘ (sphereProjection ∘ F)) q =
      fderiv Real F q := fderiv_sphereProjection_comp_eq hr houter hq
        (hF.differentiableAt (by simp))
  rw [hder] at hchain
  intro v w hvw
  apply hinj
  rw [hchain]
  exact congrArg (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3)
    ((sphereProjection ∘ F) q)) hvw

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
