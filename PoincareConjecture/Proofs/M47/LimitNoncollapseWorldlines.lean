import PoincareConjecture.Proofs.M47.LimitNoncollapseCylinders
import PoincareConjecture.Proofs.M12.GeneralizedWorldlines
import PoincareConjecture.Proofs.M36.MetricComparison
import PoincareConjecture.Definitions.M30ControlledBlowupLimits

set_option autoImplicit false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open PoincareConjecture.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}} {C B : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {I J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier} {V : TopologicalSpace.Opens B.carrier}

theorem limitNoncollapse_worldline_unique
    (hM11 : GeneralizedSpacetimeGeometryTheory.{u} 3)
    (e : GeneralizedFlowCylinder F C a q I.domain U)
    (d : GeneralizedFlowCylinder F B a q J.domain V)
    (x : U) (y : V) (s0 : ℝ) (hi0 : s0 ∈ I.domain) (hj0 : s0 ∈ J.domain)
    (hstart : e.pointMap s0 hi0 x.val = d.pointMap s0 hj0 y.val)
    (s : ℝ) (hi : s ∈ I.domain) (hj : s ∈ J.domain) :
    e.pointMap s hi x.val = d.pointMap s hj y.val := by
  obtain ⟨R⟩ := flowBoxAtlas_realize F hM11
  let K := cylinderPhysicalInterval a q e.scale_pos I
  let L := cylinderPhysicalInterval a q d.scale_pos J
  have hK : K.domain ⊆ F.interval := by
    rintro _ ⟨v, hv, rfl⟩
    exact (F.slice_nonempty_iff _).mp ⟨e.forward v hv x.val⟩
  have hL : L.domain ⊆ F.interval := by
    rintro _ ⟨v, hv, rfl⟩
    exact (F.slice_nonempty_iff _).mp ⟨d.forward v hv y.val⟩
  let gamma := rawCylinderWorldline R e hK x
  let eta := rawCylinderWorldline R d hL y
  have hki0 : a + s0 / q ∈ K.domain := ⟨s0, hi0, rfl⟩
  have hlj0 : a + s0 / q ∈ L.domain := ⟨s0, hj0, rfl⟩
  have hki : a + s / q ∈ K.domain := ⟨s, hi, rfl⟩
  have hlj : a + s / q ∈ L.domain := ⟨s, hj, rfl⟩
  have hgamma0 : gamma.curve ⟨a + s0 / q, hki0⟩ = e.pointMap s0 hi0 x.val :=
    rawCylinderMap_at_parameter R e ⟨s0, hi0⟩ x
  have heta0 : eta.curve ⟨a + s0 / q, hlj0⟩ = d.pointMap s0 hj0 y.val :=
    rawCylinderMap_at_parameter R d ⟨s0, hj0⟩ y
  have hgamma : gamma.curve ⟨a + s / q, hki⟩ = e.pointMap s hi x.val :=
    rawCylinderMap_at_parameter R e ⟨s, hi⟩ x
  have heta : eta.curve ⟨a + s / q, hlj⟩ = d.pointMap s hj y.val :=
    rawCylinderMap_at_parameter R d ⟨s, hj⟩ y
  exact hgamma.symm.trans
    ((R.compatible.worldline_unique K L gamma eta (a + s0 / q) hki0 hlj0
      (hgamma0.trans (hstart.trans heta0.symm)) (a + s / q) hki hlj).trans heta)

theorem limitNoncollapse_baseBall_isOpen (S : GeneralizedBlowupSequence.{u})
    (k : ℕ) (A : ℝ) : IsOpen (S.baseBall k A) :=
  isOpen_Iio.preimage ((M36.metric_edist_continuous ((S.flow k).metric (S.base k).1)).comp
    (continuous_const.prodMk continuous_id))

theorem limitNoncollapse_at_of_slab
    (hM11 : GeneralizedSpacetimeGeometryTheory.{u} 3)
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T kappa r0 tau : ℝ}
    (hT : 0 < T) (htau : 0 < tau)
    (D : M30FiniteHorizonSlab S k A T kappa r0)
    {C : GeneralizedSliceCarrier.{u}} {U : Set C.carrier} (hU : IsOpen U)
    (e : GeneralizedFlowCylinder (S.flow k) C (S.base k).1 (S.scale k)
      (Icc (-tau) 0) U)
    (x : C.carrier) (hx : x ∈ U)
    (y : ((S.flow k).slice (S.base k).1).carrier) (hy : y ∈ S.baseBall k A)
    (hzero : e.pointMap 0 ⟨by linarith, le_rfl⟩ x =
      (⟨(S.base k).1, y⟩ : (S.flow k).point))
    (s : ℝ) (hs : s ∈ Icc (-tau) 0) (hslab : s ∈ Ioc (-T) 0) :
    GeneralizedKappaNoncollapsedAt (S.flow k) (e.pointMap s hs x) kappa r0 := by
  let I : SpacetimeInterval :=
    ⟨Icc (-tau) 0, ordConnected_Icc,
      ⟨-tau, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩⟩
  let J : SpacetimeInterval :=
    ⟨Ioc (-T) 0, ordConnected_Ioc,
      ⟨-T / 2, ⟨by linarith, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩⟩
  let Uo : TopologicalSpace.Opens C.carrier := ⟨U, hU⟩
  let Vo : TopologicalSpace.Opens ((S.flow k).slice (S.base k).1).carrier :=
    ⟨S.baseBall k A, limitNoncollapse_baseBall_isOpen S k A⟩
  have hi0 : 0 ∈ I.domain := ⟨by linarith, le_rfl⟩
  have hj0 : 0 ∈ J.domain := ⟨by linarith, le_rfl⟩
  have heq := limitNoncollapse_worldline_unique hM11 (I := I) (J := J)
    (U := Uo) (V := Vo) e D.embedding ⟨x, hx⟩ ⟨y, hy⟩ 0 hi0 hj0
    (hzero.trans (D.zero_identity hj0 y hy).symm) s hs hslab
  rw [heq]
  exact D.noncollapsed s hslab y hy

end PoincareConjecture.M47
