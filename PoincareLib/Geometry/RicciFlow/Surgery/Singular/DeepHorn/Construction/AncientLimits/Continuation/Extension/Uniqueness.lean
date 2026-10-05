import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderRestriction
import Mathlib.Topology.Connected.Clopen

/-!
# Uniqueness for the actual compatible cylinder trajectories

Morgan--Tian Definitions 3.36-3.40, printed pp. 60-61, and Claim 11.35,
pp. 289-291. The original flow-box transition rule makes equality of
two trajectories both relatively open and relatively closed.

Re-derived from read-only DeepHorn/Blowup/Worldlines/Uniqueness:
`GeneralizedFlowCylinder.pointMap_eq_on_interval` and
`GeneralizedFlowCylinder.pointMap_eq_on_overlap`. Only frozen records,
M12 `GeneralizedFlowCylinder.restrict`, and Mathlib `IsClopen.eq_univ`
are imported. Reviewed derivation: `claim11_35-neck-cylinder-gluing.md`,
section 3. Both intervals retain their order-connected hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M32

variable {F : GeneralizedRicciFlowData.{u}} {C D : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set D.carrier}

/-- Actual compatible trajectories sharing a clock and meeting once
agree throughout a connected interval. Source: Claim 11.35, printed
pp. 289-291, and Definitions 3.36-3.40, pp. 60-61. -/
theorem cylinder_pointMap_eq_on_interval
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (e' : GeneralizedFlowCylinder F D origin scale I V)
    (hI : I.OrdConnected) {x : C.carrier} (hx : x ∈ U) {y : D.carrier} (hy : y ∈ V)
    {s : ℝ} (hs : s ∈ I) (heq : e.pointMap s hs x = e'.pointMap s hs y) :
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
    obtain ⟨b', z', delta', hdelta', hb'⟩ := e'.vertical_compatibility t.1 t.2 y hy
    obtain ⟨htb, htbvalue⟩ := hb t.1 t.2 (by simpa using hdelta)
    obtain ⟨htb', htbvalue'⟩ := hb' t.1 t.2 (by simpa using hdelta')
    have hforward : e.forward t.1 t.2 x = e'.forward t.1 t.2 y :=
      eq_of_heq (Sigma.mk.inj_iff.mp ht).2
    have hsame : (F.box b).forward _ htb z = (F.box b').forward _ htb' z' :=
      htbvalue.symm.trans (hforward.trans htbvalue')
    have hnear : {v : I | |v.1 - t.1| < min delta delta'} ∈ 𝓝 t := by
      apply (isOpen_lt (continuous_subtype_val.sub continuous_const).abs continuous_const).mem_nhds
      simpa using lt_min hdelta hdelta'
    apply mem_of_superset hnear
    intro v hv
    obtain ⟨hvb, hvvalue⟩ := hb v.1 v.2 ((lt_min_iff.mp hv).1)
    obtain ⟨hvb', hvvalue'⟩ := hb' v.1 v.2 ((lt_min_iff.mp hv).2)
    have hvforward := hvvalue.trans
      ((F.vertical_compatibility b b' _ htb htb' z z' hsame _ hvb hvb').trans hvvalue'.symm)
    exact congrArg (fun a => (⟨origin + v.1 / scale, a⟩ : F.point)) hvforward
  have : PreconnectedSpace I := Subtype.preconnectedSpace hI.convex.isPreconnected
  have : T2Space F.point := F.space_t2
  have huniv : {t : I | f t = g t} = univ :=
    (show IsClopen {t : I | f t = g t} from ⟨isClosed_eq hf hg, hopen⟩).eq_univ
      ⟨⟨s, hs⟩, heq⟩
  intro t ht
  have hmem : (⟨t, ht⟩ : I) ∈ {t : I | f t = g t} := by
    rw [huniv]
    exact mem_univ _
  exact hmem

/-- Meeting trajectories agree on the intersection of their original
order-connected intervals. Source: Claim 11.35, printed pp. 289-291. -/
theorem cylinder_pointMap_eq_on_overlap
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (e' : GeneralizedFlowCylinder F D origin scale J V)
    (hI : I.OrdConnected) (hJ : J.OrdConnected)
    {x : C.carrier} (hx : x ∈ U) {y : D.carrier} (hy : y ∈ V)
    {s : ℝ} (hs : s ∈ I) (hs' : s ∈ J)
    (heq : e.pointMap s hs x = e'.pointMap s hs' y) :
    ∀ t (ht : t ∈ I) (ht' : t ∈ J), e.pointMap t ht x = e'.pointMap t ht' y := by
  have h := cylinder_pointMap_eq_on_interval (e.restrict inter_subset_left Subset.rfl)
    (e'.restrict inter_subset_right Subset.rfl) (hI.inter hJ) hx hy
    (s := s) ⟨hs, hs'⟩ heq
  intro t ht ht'
  exact h t ⟨ht, ht'⟩

end PoincareMT.M32
