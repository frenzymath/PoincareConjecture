import PoincareConjecture.Proofs.M25.AppA_20_Fibration.RetainedReturnCover
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.Cyclic










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem NeckOnlyCover.exists_compact_whole_union_of_retained_return :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      H.X = Set.univ →
      ∀ (C : BalancedNeckChain g H.epsilon),
      ∀ a b : ℤ, C.shape = ChainShape.finite a b →
        let L := H.epsilon⁻¹
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        let q0 := ((C.neck a).coordinate_inverse (C.neck a).center).1
        ∀ (R : EpsilonNeck g), R.epsilon = H.epsilon →
          R.center ∈ closure ((C.neck b).region 0 L) →
          R.center ∉ U →
          (∀ c ∈ Set.Ioo (-L) 0,
            ¬ Disjoint R.carrier ((C.neck a).region (-L) c)) →
          ∃ (P Q : EpsilonNeck g),
            P ∈ H.necks ∧ (Q = P ∨ Q = P.reverse) ∧
            Q.epsilon = H.epsilon ∧
            Q.center = (C.neck a).coordinate_map (q0, -(17 * L / 20)) ∧
            (U ∪ R.carrier) ∪ Q.carrier = Set.univ ∧
            IsCompact (Set.univ : Set M) := by
  obtain ⟨epsilon0, hpos, hcap, hreturnCover⟩ :=
    NeckOnlyCover.exists_retained_return_cover.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H hepsilon hX C a b hshape
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L : ℝ := H.epsilon⁻¹
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  dsimp only
  intro R hRepsilon hfrontier hout hreturn
  obtain ⟨P, Q, lo, rlo, rhi, hP, hQP, hQepsilon, hQcenter,
    hlo, _, hrlo, _, hrhi, hcover⟩ :=
    hreturnCover H hepsilon hX C a b hshape R hRepsilon hfrontier hout hreturn
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  have hfinite : C.shape.active.Finite := by
    rw [hshape]
    exact Set.finite_Icc a b
  have hold : IsCompact (⋃ i ∈ C.shape.active,
      (C.neck i).coordinate_map '' (univ ×ˢ Icc (lo i) (3 * L / 4))) := by
    apply hfinite.isCompact_biUnion
    intro i hi
    apply (C.neck i).isCompact_coordinate_image_Icc
    · simpa only [C.epsilon_eq i hi] using (hlo i hi).1
    · rw [C.epsilon_eq i hi]
      change 3 * L / 4 < L
      linarith
  have hR : IsCompact (R.coordinate_map '' (univ ×ˢ Icc rlo rhi)) := by
    apply R.isCompact_coordinate_image_Icc
    · simpa only [hRepsilon] using hrlo
    · simpa only [hRepsilon] using hrhi
  have hQ : IsCompact (Q.coordinate_map ''
      (univ ×ˢ Icc (-L / 2) (19 * L / 20))) := by
    apply Q.isCompact_coordinate_image_Icc
    · rw [hQepsilon]
      change -L < -L / 2
      linarith
    · rw [hQepsilon]
      change 19 * L / 20 < L
      linarith
  have hcompact : IsCompact ((U ∪ R.carrier) ∪ Q.carrier) := by
    rw [hcover]
    exact (hold.union hR).union hQ
  have hopen : IsOpen ((U ∪ R.carrier) ∪ Q.carrier) := by
    have hU : IsOpen U :=
      isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
    exact (hU.union R.carrier_open).union Q.carrier_open
  have hmeet : (H.X ∩ ((U ∪ R.carrier) ∪ Q.carrier)).Nonempty := by
    refine ⟨R.center, ?_, Or.inl (Or.inr ?_)⟩
    · rw [hX]
      exact mem_univ _
    · exact R.central_sphere_subset R.center_on_central_sphere
  have hXsubset : H.X ⊆ (U ∪ R.carrier) ∪ Q.carrier :=
    H.connected_X.isPreconnected.subset_isClopen ⟨hcompact.isClosed, hopen⟩ hmeet
  have hwhole : (U ∪ R.carrier) ∪ Q.carrier = univ := by
    refine Set.Subset.antisymm (Set.subset_univ _) ?_
    simpa only [hX] using hXsubset
  refine ⟨P, Q, hP, hQP, hQepsilon, hQcenter, hwhole, ?_⟩
  simpa only [hwhole] using hcompact

end PoincareConjecture
