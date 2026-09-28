import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.AttachmentGerm.Circle
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleAttachmentGerm

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩



theorem exists_circle_restriction_of_boundary_germ
    (P : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (p : S1) (hp : (p : E2) ∈ P.source)
    (hboundary : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → P x ∈ sphere (0 : E2) 1) :
    ∃ f : S1 → S1, IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f p ∧
      ∀ᶠ q in 𝓝 p, (f q : E2) = P q := by
  classical
  let f : S1 → S1 := fun q => if h : P q ∈ sphere (0 : E2) 1 then ⟨P q, h⟩ else p
  obtain ⟨U, hU, hUopen, hpU⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (P.open_source.mem_nhds hp) hboundary)
  let V : Opens S1 := ⟨Subtype.val ⁻¹' U, hUopen.preimage continuous_subtype_val⟩
  have hVP {q : S1} (hq : q ∈ V) : (q : E2) ∈ P.source := (hU hq).1
  have hVcircle {q : S1} (hq : q ∈ V) : P q ∈ sphere (0 : E2) 1 :=
    (hU hq).2 q.property
  have hfval {q : S1} (hq : q ∈ V) : (f q : E2) = P q := by
    simp only [f, dif_pos (hVcircle hq)]
  have hPdiff : ContMDiff (𝓡 1) (𝓡 2) ∞ (fun q : V => P (q : S1)) := by
    intro q
    exact (P.contMDiffOn.contMDiffAt (P.open_source.mem_nhds (hVP q.property))).comp q
      ((contMDiff_coe_sphere.comp contMDiff_subtype_val) q)
  have hfV : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun q : V => f (q : S1)) := by
    have h := hPdiff.codRestrict_sphere (n := 1) (fun q : V => hVcircle q.property)
    convert! h using 1
    funext q
    exact Subtype.ext (hfval q.property)
  have hfs : ContMDiffOn (𝓡 1) (𝓡 1) ∞ f V := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hfV ⟨q, hq⟩)).contMDiffWithinAt
  have hbij (q : S1) (hq : q ∈ V) : Bijective (mfderiv (𝓡 1) (𝓡 1) f q) := by
    have hqf : ContMDiffAt (𝓡 1) (𝓡 1) ∞ f q :=
      hfs.contMDiffAt (V.isOpen.mem_nhds hq)
    have hqP := P.contMDiffOn.contMDiffAt (P.open_source.mem_nhds (hVP hq))
    have heq : (fun z : S1 => (f z : E2)) =ᶠ[𝓝 q] (fun z : S1 => P z) := by
      filter_upwards [V.isOpen.mem_nhds hq] with z hz
      exact hfval hz
    have hchainf := mfderiv_comp q
      ((contMDiff_coe_sphere (n := 1) (m := ∞) (f q)).mdifferentiableAt (by simp))
      (hqf.mdifferentiableAt (by simp))
    have hchainP := mfderiv_comp q (hqP.mdifferentiableAt (by simp))
      ((contMDiff_coe_sphere (n := 1) (m := ∞) q).mdifferentiableAt (by simp))
    have hsame := heq.mfderiv_eq (I := 𝓡 1) (I' := 𝓡 2)
    change mfderiv (𝓡 1) (𝓡 2) (Subtype.val ∘ f) q =
      mfderiv (𝓡 1) (𝓡 2) (P ∘ Subtype.val) q at hsame
    rw [hchainf, hchainP] at hsame
    have hcoei : Injective (mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 → E2) q) := by
      convert! injective_mvfderiv_subtypeVal_sphere q
    have hloc : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ P (q : E2) :=
      ⟨P, hVP hq, eqOn_refl _ _⟩
    have hPi : Injective (mfderiv (𝓡 2) (𝓡 2) P q) :=
      (hloc.mfderivToContinuousLinearEquiv (by simp)).injective
    have hfi : Injective (mfderiv (𝓡 1) (𝓡 1) f q) := by
      intro x y hxy
      apply hcoei
      apply hPi
      have hh := congrArg
        (mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 → E2) (f q)) hxy
      exact (congrArg (fun L => L x) hsame).symm.trans
        (hh.trans (congrArg (fun L => L y) hsame))
    exact ⟨hfi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := E1) (V₂ := E1) (f := (mfderiv (𝓡 1) (𝓡 1) f q).toLinearMap) rfl).mp hfi⟩
  refine ⟨f, Poincare.isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv V.isOpen hfs hbij
    ⟨p, hpU⟩, ?_⟩
  filter_upwards [V.isOpen.mem_nhds (show p ∈ V from hpU)] with q hq
  exact hfval hq

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
