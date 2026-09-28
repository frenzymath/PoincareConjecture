import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.InwardMotion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem homotopyEquiv_interior_of_inward_motion
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (D : C(unitInterval × X, X)) (hzero : ∀ x, D (0, x) = x)
    (hpres : ∀ t, MapsTo (fun x => D (t, x)) S S)
    (hpresint : ∀ t, MapsTo (fun x => D (t, x)) (interior S) (interior S))
    (hend : MapsTo (fun x => D (1, x)) S (interior S)) :
    Nonempty (ContinuousMap.HomotopyEquiv S (interior S)) := by
  let r : C(S, interior S) :=
    ⟨fun x => ⟨D (1, x), hend x.property⟩,
      (D.continuous.comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩
  let inc : C(interior S, S) :=
    ⟨Set.inclusion interior_subset, continuous_inclusion _⟩
  let H : (ContinuousMap.id S).Homotopy (inc.comp r) := {
    toFun := fun z => ⟨D (z.1, z.2), hpres z.1 z.2.property⟩
    continuous_toFun := (D.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun x => Subtype.ext (hzero x)
    map_one_left := fun _ => rfl }
  let H' : (ContinuousMap.id (interior S)).Homotopy (r.comp inc) := {
    toFun := fun z => ⟨D (z.1, z.2), hpresint z.1 z.2.property⟩
    continuous_toFun := (D.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun x => Subtype.ext (hzero x)
    map_one_left := fun _ => rfl }
  exact ⟨{
    toFun := r
    invFun := inc
    left_inv := ⟨H.symm⟩
    right_inv := ⟨H'.symm⟩ }⟩

theorem homotopyEquiv_interior_of_signed_rim_charts
    {X : Type*} [MetricSpace X] {S O : Set X}
    (hS : IsClosed S) (hO : IsClosed O) (hcover : S ∪ O = univ)
    (hcompact : IsCompact (S ∩ O)) (hne : (S ∩ O).Nonempty)
    (hlocal : ∀ x : ↥(S ∩ O),
      ∃ T : OpenPartialHomeomorph X (ℝ × ℝ), (x : X) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0) :
    Nonempty (ContinuousMap.HomotopyEquiv S (interior S)) := by
  obtain ⟨hfront, hother, U, hU, _, H, hbase, hpos, hneg, _⟩ :=
    HamiltonIntervalTorus.exists_bicollar_of_signed_rim_charts
      hS hO hcover hcompact hne hlocal
  have hneg' : ∀ z, (H z : X) ∈ (interior S)ᶜ ↔ (z.2 : ℝ) ≤ 0 := by
    simpa only [hother] using hneg
  obtain ⟨D, hzero, hpres, hpresint, hend⟩ :=
    HamiltonIntervalTorus.exists_inward_motion_of_open_bicollar hS
      (hfront.symm ▸ hcompact) hU H hbase hpos hneg'
  exact homotopyEquiv_interior_of_inward_motion D hzero hpres hpresint hend

theorem isSimplyConnected_closed_side_of_signed_rim_charts
    {X : Type*} [MetricSpace X] {S O : Set X}
    (hS : IsClosed S) (hO : IsClosed O) (hcover : S ∪ O = univ)
    (hcompact : IsCompact (S ∩ O)) (hne : (S ∩ O).Nonempty)
    (hlocal : ∀ x : ↥(S ∩ O),
      ∃ T : OpenPartialHomeomorph X (ℝ × ℝ), (x : X) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ S ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ O ↔ (T y).2 ≤ 0)
    (hsc : IsSimplyConnected (interior S)) : IsSimplyConnected S := by
  obtain ⟨H⟩ := homotopyEquiv_interior_of_signed_rim_charts
    hS hO hcover hcompact hne hlocal
  let : SimplyConnectedSpace (interior S) := hsc
  exact H.simplyConnectedSpace

theorem isSimplyConnected_closure_of_signed_frontier_charts
    {X : Type*} [MetricSpace X] {U : Set X}
    (hU : IsOpen U) (hcompact : IsCompact (frontier U))
    (hne : (frontier U).Nonempty)
    (hfront : frontier (closure U) = frontier U)
    (hlocal : ∀ x : ↥(frontier U),
      ∃ T : OpenPartialHomeomorph X (ℝ × ℝ), (x : X) ∈ T.source ∧
        (∀ y ∈ T.source, y ∈ closure U ↔ 0 ≤ (T y).2) ∧
        ∀ y ∈ T.source, y ∈ Uᶜ ↔ (T y).2 ≤ 0)
    (hsc : IsSimplyConnected U) : IsSimplyConnected (closure U) := by
  have hint : interior (closure U) = U := by
    rw [← self_sdiff_frontier, hfront, closure_sdiff_frontier, hU.interior_eq]
  have hrim : closure U ∩ Uᶜ = frontier U := by
    rw [hU.frontier_eq]
    rfl
  have hcover : closure U ∪ Uᶜ = univ := by
    exact eq_univ_of_subset (union_subset_union_left _ subset_closure)
      (union_compl_self U)
  apply isSimplyConnected_closed_side_of_signed_rim_charts
    isClosed_closure hU.isClosed_compl hcover (hrim.symm ▸ hcompact)
    (hrim.symm ▸ hne) ?_ (hint.symm ▸ hsc)
  intro x
  exact hlocal ⟨x, hrim.subset x.property⟩

end PoincareConjecture.M76
