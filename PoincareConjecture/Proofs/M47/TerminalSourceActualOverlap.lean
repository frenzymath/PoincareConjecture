import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoherence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem terminalSource_actual_coordinate_readout
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin Q : ℝ} {I : Set ℝ} (U : Opens C.carrier)
    (e : SurgeryFlowCylinder F C origin Q I U) (s : ℝ) (hs : s ∈ I)
    (gU : RiemannianMetric 3 U)
    (hmetric : ∀ (y : U) (v w : TangentSpace (𝓡 3) y),
      gU.inner y v w = e.pullbackInner s hs y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) y v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) y w))
    {W : Set E} (hW : IsOpen W) (p : E → U)
    (hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p W)
    {x : E} (hx : x ∈ W) (v w : E) :
    gU.pullbackCoefficients p x v w =
      Q * (F.metric (origin + s / Q)).pullbackCoefficients
        (fun y => e.forward s hs (p y).val) x v w := by
  have hp' := hp.contMDiffAt (hW.mem_nhds hx)
  have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (Subtype.val : U → C.carrier) (p x) := contMDiff_subtype_val.contMDiffAt
  have he := (e.forward_smooth s hs).contMDiffAt (U.isOpen.mem_nhds (p x).property)
  have hdU := mfderiv_comp x (hi.mdifferentiableAt (by simp))
    (hp'.mdifferentiableAt (by simp))
  have hdE := mfderiv_comp x (he.mdifferentiableAt (by simp))
    ((hi.comp x hp').mdifferentiableAt (by simp))
  change gU.inner (p x) (mfderiv (𝓡 3) (𝓡 3) p x v)
      (mfderiv (𝓡 3) (𝓡 3) p x w) =
    Q * (F.metric (origin + s / Q)).inner (e.forward s hs (p x).val)
      (mfderiv (𝓡 3) (𝓡 3)
        (e.forward s hs ∘ ((Subtype.val : U → C.carrier) ∘ p)) x v)
      (mfderiv (𝓡 3) (𝓡 3)
        (e.forward s hs ∘ ((Subtype.val : U → C.carrier) ∘ p)) x w)
  rw [hdE, hdU, hmetric]
  rfl



theorem terminalSource_actual_overlap_coefficients
    {F : SurgeryFlowData.{u}} {C D : GeneralizedSliceCarrier.{u}}
    {origin Q a : ℝ} {I J : Set ℝ} (U : Opens C.carrier) (V : Opens D.carrier)
    (e : SurgeryFlowCylinder F C origin Q I U)
    (f : SurgeryFlowCylinder F D origin Q J V)
    (ha : a ≤ 0) (hI : Icc a 0 ⊆ I) (hJ : Icc a 0 ⊆ J)
    (gU : RiemannianMetric 3 U) (gV : RiemannianMetric 3 V)
    (hemetric : ∀ (y : U) (v w : TangentSpace (𝓡 3) y),
      gU.inner y v w = e.pullbackInner a (hI ⟨le_rfl, ha⟩) y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) y v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) y w))
    (hfmetric : ∀ (y : V) (v w : TangentSpace (𝓡 3) y),
      gV.inner y v w = f.pullbackInner a (hJ ⟨le_rfl, ha⟩) y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → D.carrier) y v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → D.carrier) y w))
    {W Z : Set E} (hW : IsOpen W) (hZ : IsOpen Z)
    (p : E → U) (q : E → V) (T : E → E)
    (hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p W)
    (hq : ContMDiffOn (𝓡 3) (𝓡 3) ∞ q Z)
    (hT : ContDiffOn ℝ ∞ T W) (hTZ : MapsTo T W Z)
    (hterminal : ∀ x ∈ W,
      e.forward 0 (hI ⟨ha, le_rfl⟩) (p x).val =
        f.forward 0 (hJ ⟨ha, le_rfl⟩) (q (T x)).val)
    {x : E} (hx : x ∈ W) (v w : E) :
    gV.pullbackCoefficients q (T x) (fderiv ℝ T x v) (fderiv ℝ T x w) =
      gU.pullbackCoefficients p x v w := by
  let P : E → (F.slice (origin + a / Q)).carrier :=
    fun y => e.forward a (hI ⟨le_rfl, ha⟩) (p y).val
  let R : E → (F.slice (origin + a / Q)).carrier :=
    fun y => f.forward a (hJ ⟨le_rfl, ha⟩) (q y).val
  have hq' := hq.contMDiffAt (hZ.mem_nhds (hTZ hx))
  have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (Subtype.val : V → D.carrier) (q (T x)) := contMDiff_subtype_val.contMDiffAt
  have hf := (f.forward_smooth a (hJ ⟨le_rfl, ha⟩)).contMDiffAt
    (V.isOpen.mem_nhds (q (T x)).property)
  have hR : ContMDiffAt (𝓡 3) (𝓡 3) ∞ R (T x) :=
    hf.comp (T x) (hi.comp (T x) hq')
  have hTx := (hT x hx).contDiffAt (hW.mem_nhds hx)
  have heq : R ∘ T =ᶠ[𝓝 x] P := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact (terminalCommonInterval_physical_eq e f ha hI hJ
      (p y).val (p y).property (q (T y)).val (q (T y)).property (hterminal y hy)).symm
  rw [terminalSource_actual_coordinate_readout V f a (hJ ⟨le_rfl, ha⟩)
      gV hfmetric hZ q hq (hTZ hx),
    terminalSource_actual_coordinate_readout U e a (hI ⟨le_rfl, ha⟩)
      gU hemetric hW p hp hx]
  exact congrArg (fun z : ℝ => Q * z)
    ((F.metric (origin + a / Q)).pullbackCoefficients_comp_of_eventuallyEq
      (hR.mdifferentiableAt (by simp)) (hTx.differentiableAt (by simp)) heq v w)

end PoincareConjecture.M47
