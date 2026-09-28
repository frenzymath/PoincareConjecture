import PoincareConjecture.Proofs.M25.AppA_20_Fibration.CompactPathReturn
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ComplementaryPath
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.RetainedReturnCompact









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem NeckOnlyCover.exists_compact_whole_union_of_nonseparating :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      H.X = Set.univ →
      ∀ (N : EpsilonNeck g), N ∈ H.necks → N.IsNonseparating →
        let L := H.epsilon⁻¹
        let q0 := (N.coordinate_inverse N.center).1
        ∃ (b : ℕ) (C : BalancedNeckChain g H.epsilon)
          (R P Q : EpsilonNeck g),
          let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
          C.shape = ChainShape.finite 0 (b : ℤ) ∧
          C.source_necks = H.necks ∧ C.neck 0 = N ∧
          (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
            closure ((C.neck i).region (L / 2) L) ⊆
                (C.neck (i + 1)).carrier ∧
              closure ((C.neck (i + 1)).region (-L) (-L / 2)) ⊆
                (C.neck i).carrier) ∧
          (∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active,
            i < j → (C.neck j).center ∉ (C.neck i).carrier) ∧
          (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
            (C.neck (i + 1)).center ∈
              closure ((C.neck i).region 0 L)) ∧
          R ∈ H.necks ∧ R.epsilon = H.epsilon ∧
          R.center ∈ frontier U ∧ R.center ∉ U ∧
          R.center ∈ closure ((C.neck (b : ℤ)).region 0 L) ∧
          (∀ c ∈ Set.Ioo (-L) 0,
            ¬ Disjoint R.carrier (N.region (-L) c)) ∧
          P ∈ H.necks ∧ (Q = P ∨ Q = P.reverse) ∧
          Q.epsilon = H.epsilon ∧
          Q.center = N.coordinate_map (q0, -(17 * L / 20)) ∧
          (U ∪ R.carrier) ∪ Q.carrier = Set.univ ∧
          IsCompact (Set.univ : Set M) := by
  obtain ⟨ep, hppos, hpcap, hpathReturn⟩ :=
    NeckOnlyCover.exists_finite_deep_return_on_complementary_path.{u}
  obtain ⟨er, hrpos, _, hreturnCompact⟩ :=
    NeckOnlyCover.exists_compact_whole_union_of_retained_return.{u}
  refine ⟨min ep er, lt_min hppos hrpos, (min_le_left _ _).trans hpcap, ?_⟩
  intro M _ _ _ _ _ _ g H hsmall hwhole N hN hnonsep
  classical
  dsimp only
  let L : ℝ := H.epsilon⁻¹
  let q0 : UnitTwoSphere := (N.coordinate_inverse N.center).1
  have hNepsilon : N.epsilon = H.epsilon := H.neck_epsilon N hN
  obtain ⟨γ, _F, _hFfinite, _hFsource, hγ, _hFcover⟩ :=
    H.exists_complementary_path_finite_middle_cover hwhole N hN hnonsep q0
  let γH : Path (N.coordinate_map (q0, -L / 2))
      (N.coordinate_map (q0, L / 2)) :=
    γ.cast (by rw [hNepsilon]) (by rw [hNepsilon])
  have hγH : ∀ t, γH t ∉ N.central_sphere := by
    intro t
    change γ t ∉ N.central_sphere
    exact (hγ t).2
  obtain ⟨b, C, R, hshape, hsource, hstart, hquarters, _hcenters,
    hhistory, hincidence, hRsource, hRepsilon, _hRpath, hRfrontier,
    hRout, hRpositive, hRreturn⟩ :=
    hpathReturn H (hsmall.trans (min_le_left _ _)) hwhole N hN q0 γH hγH
  have hreturn : ∀ c ∈ Ioo (-L) 0,
      ¬ Disjoint R.carrier ((C.neck 0).region (-L) c) := by
    simpa only [hstart] using hRreturn
  obtain ⟨P, Q, hP, hQP, hQepsilon, hQcenter, hwholeUnion, hcompact⟩ :=
    hreturnCompact H (hsmall.trans (min_le_right _ _)) hwhole C 0 (b : ℤ)
      hshape R hRepsilon hRpositive hRout hreturn
  refine ⟨b, C, R, P, Q, hshape, hsource, hstart, hquarters,
    hhistory, hincidence, hRsource, hRepsilon, hRfrontier, hRout,
    hRpositive, hRreturn, hP, hQP, hQepsilon, ?_, hwholeUnion, hcompact⟩
  simpa only [hstart] using hQcenter

end PoincareConjecture
