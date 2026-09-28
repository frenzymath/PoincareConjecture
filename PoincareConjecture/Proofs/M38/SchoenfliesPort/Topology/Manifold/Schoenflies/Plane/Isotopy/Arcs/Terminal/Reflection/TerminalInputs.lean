import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.MorseReduction
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.Paths







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal.Reflection
open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



structure TerminalInputData (f : S2 → E3) (p : S2) where
  reduction : SphereMorseReduction f
  leaf : S2 → E3
  leaf_mem : leaf ∈ reduction.tree.leaves
  path : SphereSurgeryPath (reduction.v : E3) (fun q => reduction.D (f q)) leaf
  protects : path.Protects
    ((fun q => inner Real (reduction.v : E3) (reduction.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (reduction.v : E3) (reduction.D (f y))) q = 0})
  preserves_caps : path.PreservesCaps
  point_interior : p ∈ interior path.core
  critical : mfderiv (𝓡 2) 𝓘(Real, Real)
    (fun q => inner Real (reduction.v : E3) (leaf q)) p = 0
  unique : ∀ q ∈ path.core, mfderiv (𝓡 2) 𝓘(Real, Real)
    (fun y => inner Real (reduction.v : E3) (leaf y)) q = 0 → q = p
  chart : OpenPartialHomeomorph E2 S2
  chart_zero : 0 ∈ chart.source
  chart_center : chart 0 = p
  chart_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ chart chart.source
  chart_inverse_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ chart.symm chart.target
  chart_target : chart.target ⊆ interior path.core
  form : ∀ x ∈ chart.source, inner Real (reduction.v : E3) (leaf (chart x)) =
    inner Real (reduction.v : E3) (leaf p) - x 0 ^ 2 + x 1 ^ 2

namespace TerminalInputData



theorem exists_reflected {f : S2 → E3} {p : S2} (s : TerminalInputData f p) :
    ∃ s' : TerminalInputData s.reduction.reflectedOriginal p,
      s'.reduction.v = s.reduction.v ∧ s'.reduction.D = s.reduction.D ∧
      s'.leaf = heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property) ∘ s.leaf ∧
      s'.path.core = s.path.core ∧ s'.chart = reflectedMorseChart s.chart ∧
      ∀ q, s'.reduction.D (s.reduction.reflectedOriginal q) =
        heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property)
          (s.reduction.D (f q)) := by
  let hv : ‖(s.reduction.v : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp s.reduction.v.property
  let J := heightReflection hv
  obtain ⟨R, hvR, hDR, _, hinit, hleaves⟩ := s.reduction.exists_reflected
  have hpath : ∃ P : SphereSurgeryPath (R.v : E3)
      (fun q => R.D (s.reduction.reflectedOriginal q)) (J ∘ s.leaf),
      P.core = s.path.core ∧
      P.Protects ((fun q => inner Real (R.v : E3) (R.D (s.reduction.reflectedOriginal q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (R.v : E3) (R.D (s.reduction.reflectedOriginal y))) q = 0}) ∧
      P.PreservesCaps := by
    rw [hvR]
    rw [funext hinit]
    refine ⟨s.path.reflected hv, s.path.reflected_core hv, ?_, s.preserves_caps.reflected hv⟩
    have hheight : (fun q => inner Real (s.reduction.v : E3)
        (R.D (s.reduction.reflectedOriginal q))) =
        (fun q => inner Real (s.reduction.v : E3) (J (s.reduction.D (f q)))) := by
      funext q
      rw [hinit]
    rw [hheight]
    have hcritical :
        {q : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (s.reduction.v : E3) (J (s.reduction.D (f y)))) q = 0} =
        {q : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (s.reduction.v : E3) (s.reduction.D (f y))) q = 0} :=
      Set.ext (fun q => reflected_height_critical_iff hv (fun y => s.reduction.D (f y)) q)
    rw [hcritical]
    have hvalues :
        (fun q => inner Real (s.reduction.v : E3) (J (s.reduction.D (f q)))) ''
          {q | mfderiv (𝓡 2) 𝓘(Real, Real)
            (fun y => inner Real (s.reduction.v : E3) (s.reduction.D (f y))) q = 0} =
        Neg.neg '' ((fun q => inner Real (s.reduction.v : E3) (s.reduction.D (f q))) ''
          {q | mfderiv (𝓡 2) 𝓘(Real, Real)
            (fun y => inner Real (s.reduction.v : E3) (s.reduction.D (f y))) q = 0}) := by
      rw [image_image]
      exact image_congr (fun q _ => inner_heightReflection hv _)
    rw [hvalues]
    exact s.protects.reflected hv
  obtain ⟨P, hcore, hprotect, hcaps⟩ := hpath
  have hcritical (q : S2) :
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => inner Real (R.v : E3) ((J ∘ s.leaf) y)) q = 0 ↔
      mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (s.reduction.v : E3) (s.leaf y)) q = 0 := by
    rw [hvR]
    exact reflected_height_critical_iff hv s.leaf q
  obtain ⟨hzero, hcenter⟩ := reflectedMorseChart_center s.chart s.chart_zero
  obtain ⟨hsmooth, hinverse⟩ := reflectedMorseChart_smooth s.chart
    s.chart_smooth s.chart_inverse_smooth
  let s' : TerminalInputData s.reduction.reflectedOriginal p := {
    reduction := R
    leaf := J ∘ s.leaf
    leaf_mem := hleaves _ s.leaf_mem
    path := P
    protects := hprotect
    preserves_caps := hcaps
    point_interior := hcore.symm ▸ s.point_interior
    critical := (hcritical p).mpr s.critical
    unique := fun q hq hc => s.unique q (hcore ▸ hq) ((hcritical q).mp hc)
    chart := reflectedMorseChart s.chart
    chart_zero := hzero
    chart_center := hcenter.trans s.chart_center
    chart_smooth := hsmooth
    chart_inverse_smooth := hinverse
    chart_target := by
      rw [reflectedMorseChart_target, hcore]
      exact s.chart_target
    form := by
      rw [hvR]
      exact reflectedMorseChart_height hv s.chart s.form }
  exact ⟨s', hvR, hDR, rfl, hcore, rfl, hinit⟩

end TerminalInputData

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal.Reflection

end

end M38Schoenflies
