import PoincareConjecture.Proofs.M30.Generalized.Restriction
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30.Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C D : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set D.carrier}

theorem pointMap_eq_on_interval
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (e' : GeneralizedFlowCylinder F D origin scale I V)
    (hI : I.OrdConnected) {x : C.carrier} (hx : x ∈ U)
    {y : D.carrier} (hy : y ∈ V) {s : ℝ} (hs : s ∈ I)
    (hmeet : e.pointMap s hs x = e'.pointMap s hs y) :
    ∀ t (ht : t ∈ I), e.pointMap t ht x = e'.pointMap t ht y := by
  let f : I → F.point := fun t => e.pointMap t.1 t.2 x
  let g : I → F.point := fun t => e'.pointMap t.1 t.2 y
  have hf : Continuous f := e.embedding.continuous.comp
    (continuous_id.prodMk (continuous_const (y := (⟨x, hx⟩ : U))))
  have hg : Continuous g := e'.embedding.continuous.comp
    (continuous_id.prodMk (continuous_const (y := (⟨y, hy⟩ : V))))
  have hopen : IsOpen {t : I | f t = g t} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨b, z, delta, hdelta, hb⟩ := e.vertical_compatibility t.1 t.2 x hx
    obtain ⟨c, w, eta, heta, hc⟩ := e'.vertical_compatibility t.1 t.2 y hy
    obtain ⟨htb, heq⟩ := hb t.1 t.2 (by simpa using hdelta)
    obtain ⟨htc, heq'⟩ := hc t.1 t.2 (by simpa using heta)
    have hvalue : e.forward t.1 t.2 x = e'.forward t.1 t.2 y :=
      eq_of_heq (Sigma.mk.inj_iff.mp ht).2
    have hbox : (F.box b).forward _ htb z = (F.box c).forward _ htc w :=
      heq.symm.trans (hvalue.trans heq')
    have hnear : {v : I | |v.1 - t.1| < min delta eta} ∈ 𝓝 t := by
      apply (isOpen_lt (continuous_subtype_val.sub continuous_const).abs
        continuous_const).mem_nhds
      simpa using lt_min hdelta heta
    filter_upwards [hnear] with v hv
    obtain ⟨hvb, hvb_eq⟩ := hb v.1 v.2 (lt_min_iff.mp hv).1
    obtain ⟨hvc, hvc_eq⟩ := hc v.1 v.2 (lt_min_iff.mp hv).2
    exact congrArg (fun z => (⟨origin + v.1 / scale, z⟩ : F.point))
      (hvb_eq.trans ((F.vertical_compatibility b c _ htb htc z w hbox
        _ hvb hvc).trans hvc_eq.symm))
  let : PreconnectedSpace I := Subtype.preconnectedSpace hI.isPreconnected
  let : T2Space F.point := F.space_t2
  have hall : {t : I | f t = g t} = univ :=
    (show IsClopen {t : I | f t = g t} from ⟨isClosed_eq hf hg, hopen⟩).eq_univ
      ⟨⟨s, hs⟩, hmeet⟩
  intro t ht
  have hmem : (⟨t, ht⟩ : I) ∈ {t : I | f t = g t} := by
    rw [hall]
    exact mem_univ _
  exact hmem

theorem pointMap_eq_on_overlap
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (e' : GeneralizedFlowCylinder F D origin scale J V)
    (hI : I.OrdConnected) (hJ : J.OrdConnected)
    {x : C.carrier} (hx : x ∈ U) {y : D.carrier} (hy : y ∈ V)
    {s : ℝ} (hs : s ∈ I) (hs' : s ∈ J)
    (hmeet : e.pointMap s hs x = e'.pointMap s hs' y) :
    ∀ t (ht : t ∈ I) (ht' : t ∈ J), e.pointMap t ht x = e'.pointMap t ht' y := by
  have h := pointMap_eq_on_interval
    (restrict e inter_subset_left Subset.rfl)
    (restrict e' inter_subset_right Subset.rfl)
    (hI.inter hJ) hx hy (s := s) ⟨hs, hs'⟩ hmeet
  intro t ht ht'
  exact h t ⟨ht, ht'⟩

end PoincareConjecture.M30.Cylinder
