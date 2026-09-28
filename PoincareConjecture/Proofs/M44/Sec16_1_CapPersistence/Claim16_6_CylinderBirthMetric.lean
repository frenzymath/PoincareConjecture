import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderRicciFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_PhysicalBirthChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {origin scale : ℝ} {I : Set ℝ}
  {U : Set (F.slice origin).carrier}
  {e : SurgeryFlowCylinder F (F.slice origin) origin scale I U}
  {f : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice origin).carrier ∞}

theorem CylinderRicciFlow.initial_metric_link
    (G : CylinderRicciFlow e f) (hzero : (0 : ℝ) ∈ I) (hmap : f.target ⊆ U)
    (hinitial : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (y : (⟨f.target, f.open_target⟩ : Opens (F.slice origin).carrier))
    (v w : TangentSpace (𝓡 3) y) :
    (G.flow.metric 0).inner y v w = scale * (F.metric origin).inner y.1
      (mfderiv (𝓡 3) (𝓡 3) Subtype.val y v)
      (mfderiv (𝓡 3) (𝓡 3) Subtype.val y w) := by
  have hm := G.metric_link 0 hzero
  have hf : ∀ z : (⟨f.target, f.open_target⟩ : Opens (F.slice origin).carrier),
      HEq (cylinderTargetTransport e f 0 hzero z) z.1 :=
    fun z => hinitial hzero z.1 (hmap z.2)
  have htransport (t : ℝ) (ht : t = origin)
      (k : (⟨f.target, f.open_target⟩ : Opens (F.slice origin).carrier) →
        (F.slice t).carrier)
      (hk : ∀ z, HEq (k z) z.1)
      (hm : ∀ z a b, (G.flow.metric 0).inner z a b = scale * (F.metric t).inner (k z)
        (mfderiv (𝓡 3) (𝓡 3) k z a) (mfderiv (𝓡 3) (𝓡 3) k z b)) :
      (G.flow.metric 0).inner y v w = scale * (F.metric origin).inner y.1
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val y v)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val y w) := by
    subst t
    have heq : k = Subtype.val := funext (fun z => eq_of_heq (hk z))
    subst k
    exact hm y v w
  exact htransport _ (by simp) _ hf hm

theorem CylinderRicciFlow.initial_pullback_eq
    (G : CylinderRicciFlow e f) (hzero : (0 : ℝ) ∈ I) (hmap : f.target ⊆ U)
    (hinitial : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (g : RiemannianMetric 3 (F.slice origin).carrier)
    (hg : ∀ y v w, g.inner y v w = scale * (F.metric origin).inner y v w)
    (p : (⟨f.target, f.open_target⟩ : Opens (F.slice origin).carrier)) :
    EqOn ((G.flow.metric 0).pullbackCoefficients (targetChart f p))
      (g.pullbackCoefficients f) f.source := by
  intro x hx
  symm
  apply pullbackCoefficients_eq_of_metric_germ (G.flow.metric 0) g
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) _)
    (((contMDiffOn_targetChart f p).contMDiffAt
      (f.open_source.mem_nhds hx)).mdifferentiableAt (by simp))
  · exact eventually_of_mem (f.open_source.mem_nhds hx)
      (fun z hz => (targetChart_val f p hz).symm)
  · intro v w
    rw [G.initial_metric_link hzero hmap hinitial, hg]

end PoincareConjecture.M44
