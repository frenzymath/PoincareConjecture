import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.Geometry
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularTimeReference

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem spacetime_forward_eq (R : SingularTimeReference F T M)
    (t : Set.Ico R.tMinus T) (y : M) :
    R.spacetime_forward (t, y) = (⟨t, R.forward t t.property y⟩ : F.point) := by
  exact Sigma.ext (R.spacetime_time (t, y)) (R.spacetime_spatial (t, y))

theorem forward_eq_of_eq (R : SingularTimeReference F T M)
    (b : F.box_index) (x : (F.box b).carrier.carrier) (y : M)
    {t : ℝ} (ht : t ∈ Set.Ico R.tMinus T) (hbt : t ∈ (F.box b).interval)
    (heq : R.forward t ht y = (F.box b).forward t hbt x)
    {s : ℝ} (hs : s ∈ Set.Ico R.tMinus T) (hbs : s ∈ (F.box b).interval) :
    R.forward s hs y = (F.box b).forward s hbs x := by
  let I : Set ℝ := (F.box b).interval ∩ Set.Ico R.tMinus T
  let : T2Space F.point := F.space_t2
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp
    ((F.box b).flow.interval.inter Set.ordConnected_Ico).isPreconnected
  let r : I → F.point := fun a => R.spacetime_forward (⟨a, a.property.2⟩, y)
  let c : I → F.point := fun a =>
    ⟨a, (F.box b).forward a a.property.1 x⟩
  have hr : Continuous r := R.spacetime_embedding.continuous.comp
    ((continuous_subtype_val.subtype_mk (fun a => a.property.2)).prodMk continuous_const)
  have hc : Continuous c := (F.box_openEmbedding b).continuous.comp
    ((continuous_subtype_val.subtype_mk (fun a => a.property.1)).prodMk continuous_const)
  have hclosed : IsClosed {a : I | r a = c a} := isClosed_eq hr hc
  have hopen : IsOpen {a : I | r a = c a} := by
    rw [Metric.isOpen_iff]
    intro a ha
    obtain ⟨d, z, δ, hδ, hloc⟩ := R.vertical_compatibility a a.property.2 y
    obtain ⟨hda, hda_eq⟩ := hloc a a.property.2 (by simpa using hδ)
    have hbase : R.forward a a.property.2 y = (F.box b).forward a a.property.1 x := by
      have hsig := ha
      change R.spacetime_forward (⟨a, a.property.2⟩, y) = _ at hsig
      rw [R.spacetime_forward_eq] at hsig
      exact eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
    refine ⟨δ, hδ, ?_⟩
    intro v hv
    have hvδ : |(v : ℝ) - (a : ℝ)| < δ := by
      simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using hv
    obtain ⟨hdv, hdv_eq⟩ := hloc v v.property.2 hvδ
    change R.spacetime_forward (⟨v, v.property.2⟩, y) = _
    rw [R.spacetime_forward_eq]
    apply congrArg (Sigma.mk (v : ℝ))
    exact hdv_eq.trans
      (F.vertical_compatibility d b a hda a.property.1 z x
        (hda_eq.symm.trans hbase) v hdv v.property.1)
  have hall : {a : I | r a = c a} = Set.univ :=
    (show IsClopen {a : I | r a = c a} from ⟨hclosed, hopen⟩).eq_univ
      ⟨⟨t, hbt, ht⟩, by
        change R.spacetime_forward (⟨t, ht⟩, y) = _
        rw [R.spacetime_forward_eq]
        exact congrArg (Sigma.mk t) heq⟩
  have hsig : r ⟨s, hbs, hs⟩ = c ⟨s, hbs, hs⟩ := by
    exact Set.eq_univ_iff_forall.mp hall ⟨s, hbs, hs⟩
  change R.spacetime_forward (⟨s, hs⟩, y) = _ at hsig
  rw [R.spacetime_forward_eq] at hsig
  exact eq_of_heq (Sigma.mk.inj_iff.mp hsig).2

end PoincareConjecture.SingularTimeReference
