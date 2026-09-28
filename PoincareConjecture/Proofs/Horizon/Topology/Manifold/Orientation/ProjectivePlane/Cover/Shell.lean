import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Cover.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Euclidean.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Topology

namespace Poincare.Topology.Orientation.ProjectivePlane

open PoincareConjecture

abbrev Shell := UnitTwoSphere × NormalInterval

instance shell_locallyCompactSpace : LocallyCompactSpace Shell := by
  let : LocallyCompactSpace NormalInterval := isOpen_Ioo.locallyCompactSpace
  let : CompactSpace UnitTwoSphere :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E3) 1)
  infer_instance

instance shell_preconnectedSpace : PreconnectedSpace Shell := by
  let : PreconnectedSpace UnitTwoSphere := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by
      norm_num [E3])) (0 : E3) 1)
  let : PreconnectedSpace NormalInterval :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  infer_instance

instance shell_nonempty : Nonempty Shell := by
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (x := (0 : E3)).mpr
    (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨(⟨x, hx⟩, ⟨0, by norm_num⟩)⟩

private def radialEmbedding : C(NormalInterval, Set.Ioi (0 : ℝ)) :=
  ⟨fun t => ⟨(t : ℝ) + 2, by
    change (0 : ℝ) < (t : ℝ) + 2
    linarith [t.property.1]⟩, by fun_prop⟩

private theorem radialEmbedding_open :
    _root_.Topology.IsOpenEmbedding radialEmbedding := by
  have hraw : _root_.Topology.IsOpenEmbedding
      ((fun z : Set.Ioi (0 : ℝ) => (z : ℝ)) ∘ radialEmbedding) := by
    let a : ℝ ≃ₜ ℝ := affineHomeomorph 1 2 (by norm_num)
    change _root_.Topology.IsOpenEmbedding
      (fun t : NormalInterval => (t : ℝ) + 2)
    simpa [a, radialEmbedding, Function.comp_def] using
      (a.isOpenEmbedding.comp isOpen_Ioo.isOpenEmbedding_subtypeVal)
  exact _root_.Topology.IsOpenEmbedding.of_comp radialEmbedding
    isOpen_Ioi.isOpenEmbedding_subtypeVal hraw

private def radialProduct : C(Shell,
    UnitTwoSphere × Set.Ioi (0 : ℝ)) :=
  ⟨fun z => (z.1, radialEmbedding z.2), by fun_prop⟩

private def punctureInclusion : C(({0}ᶜ : Set E3), E3) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def shellEmbedding : C(Shell, E3) := by
  let H := homeomorphSphereProd E3 1 one_pos
  let hrad : C(Shell, ({0}ᶜ : Set E3)) :=
    ⟨fun z => H.symm (radialProduct z), by fun_prop⟩
  exact punctureInclusion.comp hrad

theorem shellEmbedding_open :
    _root_.Topology.IsOpenEmbedding shellEmbedding := by
  let H := homeomorphSphereProd E3 1 one_pos
  let hprod : _root_.Topology.IsOpenEmbedding radialProduct :=
    (Homeomorph.refl UnitTwoSphere).isOpenEmbedding.prodMap radialEmbedding_open
  let hrad : C(Shell, ({0}ᶜ : Set E3)) :=
    ⟨fun z => H.symm (radialProduct z), by fun_prop⟩
  have hrad_open : _root_.Topology.IsOpenEmbedding hrad := by
    exact H.symm.isOpenEmbedding.comp hprod
  exact isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp hrad_open

def shellAntipodal : Shell ≃ₜ Shell :=
  sphereAntipodeHomeomorph.prodCongr (Homeomorph.refl NormalInterval)

theorem shellEmbedding_antipodal (z : Shell) :
    shellEmbedding (shellAntipodal z) = -shellEmbedding z := by
  change ((homeomorphSphereProd E3 1 one_pos).symm
      (radialProduct (shellAntipodal z)) : E3) =
    -((homeomorphSphereProd E3 1 one_pos).symm (radialProduct z) : E3)
  simp [radialProduct, shellAntipodal, radialEmbedding,
    sphereAntipodeHomeomorph, homeomorphSphereProd_symm_apply_coe]

end Poincare.Topology.Orientation.ProjectivePlane
