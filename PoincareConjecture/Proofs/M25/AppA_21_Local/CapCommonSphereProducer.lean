import PoincareConjecture.Proofs.M25.AppA_21_Local.CapBoundaryFrontier
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapBoundaryOrientation
import PoincareConjecture.Proofs.M25.AppA_1_Necks.FrontierSphereGraph
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapMixedBoundarySide
import PoincareConjecture.Proofs.M25.AppA_21_Local.FiniteCappedChainDiffeomorph










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem CapCertificate.exists_common_outward_graph_of_finite_core_frontier :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C0 C1 : CapCertificate g) (D : BalancedNeckChain g C0.epsilon)
        {b : ℤ},
      C0.epsilon ≤ epsilon0 →
      C1.epsilon = C0.epsilon →
      D.shape = ChainShape.finite 0 b →
      D.neck 0 = C0.end_neck →
      (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) →
      (∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∉ C0.carrier) →
      (∀ i ∈ D.shape.active, i + 1 ∈ D.shape.active →
        closure ((D.neck i).region (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹) ⊆
            (D.neck (i + 1)).carrier ∧
          closure ((D.neck (i + 1)).region
              (-C0.epsilon⁻¹) (-C0.epsilon⁻¹ / 2)) ⊆ (D.neck i).carrier) →
      (¬ (C0.carrier \ C0.end_neck.region
        (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹ ⊆ C1.core)) →
      ∀ y : M, y ∈ C1.core →
      y ∈ closure ((D.neck b).region 0 C0.epsilon⁻¹) →
      y ∉ C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) →
      ((C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)) ∩
        C1.boundary_sphere).Nonempty →
      let V : TopologicalSpace.Opens M :=
        ⟨C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier),
          C0.carrier_open.union
            (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)⟩
      let V0 : TopologicalSpace.Opens M := ⟨C0.carrier, C0.carrier_open⟩
      ∃ d : Diffeomorph (𝓡 3) (𝓡 3) V V0 ∞,
        (∀ x : V, x.val ∈ C0.closed_core ∪
            C0.end_neck.region (-C0.epsilon⁻¹) 0 → (d x).val = x.val) ∧
        (∀ x : V0, x.val ∈ C0.closed_core ∪
            C0.end_neck.region (-C0.epsilon⁻¹) 0 → (d.symm x).val = x.val) ∧
        y ∈ closure (V : Set M) ∧
        ∃ (R : EpsilonNeck g) (f : UnitTwoSphere → ℝ)
          (N : EpsilonNeck g) (s : ℝ),
          (R = C1.boundary_neck ∨ R = C1.boundary_neck.reverse) ∧
          R.epsilon = C1.epsilon ∧ R.carrier = C1.boundary_neck.carrier ∧
          R.central_sphere = C1.boundary_sphere ∧
          R.carrier ∩ C1.core = R.region (-C1.epsilon⁻¹) 0 ∧
          R.carrier ∩ C1.end_neck.carrier = R.region 0 C1.epsilon⁻¹ ∧
          ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
          (∀ q, f q ∈ Ico (0 : ℝ) C1.epsilon⁻¹) ∧
          s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
          range (fun q : UnitTwoSphere => R.coordinate_map (q, f q)) =
            range (fun q : UnitTwoSphere => N.coordinate_map (q, s)) ∧
          range (fun q : UnitTwoSphere =>
            R.coordinate_map (q, f q)) ⊆ (V : Set M) ∧
          ((C1.boundary_sphere ⊆ (V : Set M) ∧
              N = R ∧ s = 0 ∧ f = fun _ => 0) ∨
            ∃ z : M,
              z ∈ C1.boundary_sphere ∧ z ∈ frontier (V : Set M) ∧
              z ∉ (V : Set M) ∧
              z ∈ closure ((D.neck b).region 0 C0.epsilon⁻¹) ∧
              z ∉ (D.neck b).carrier ∧ y ≠ z ∧
              N = D.neck b ∧ s = 3 * C0.epsilon⁻¹ / 4 ∧
              (∀ q, C0.epsilon⁻¹ / 5 < f q ∧
                f q < 3 * C0.epsilon⁻¹ / 10) ∧
              range (fun q : UnitTwoSphere =>
                R.coordinate_map (q, f q)) ⊆ C1.end_neck.carrier) := by
  obtain ⟨epsilonG, hG, hGcap, hgraph⟩ :=
    EpsilonNeck.exists_oriented_positive_frontier_graph_at_sphere.{u}
  obtain ⟨epsilonF, hF, _, hdiffeo⟩ :=
    CapCertificate.exists_finite_chain_carrier_diffeomorph.{u}
  refine ⟨min epsilonG epsilonF, lt_min hG hF,
    (min_le_left _ _).trans hGcap, ?_⟩
  intro M _ _ _ _ _ _ g C0 C1 D b hepsilon heq hshape hstart hsep hout hquarters hno
    y hycore hyclosure hyout hmeet
  classical
  let V : Set M := C0.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)
  have hsmallG : C0.epsilon ≤ epsilonG := hepsilon.trans (min_le_left _ _)
  have hsmallF : C0.epsilon ≤ epsilonF := hepsilon.trans (min_le_right _ _)
  have hL : 0 < C0.epsilon⁻¹ := inv_pos.mpr C0.epsilon_pos
  have hL1 : 0 < C1.epsilon⁻¹ := inv_pos.mpr C1.epsilon_pos
  have hnonneg : (0 : ℤ) ≤ b := by
    obtain ⟨i, hi⟩ := D.active_nonempty
    rw [hshape] at hi
    exact hi.1.trans hi.2
  have hb : b ∈ D.shape.active := by
    rw [hshape]
    exact ⟨hnonneg, le_rfl⟩
  have heLast : (D.neck b).epsilon = C0.epsilon := D.epsilon_eq b hb
  have hlast : (D.neck b).carrier ⊆ V := by
    intro x hx
    exact Or.inr (mem_iUnion₂.mpr ⟨b, hb, hx⟩)
  have hpositive : (D.neck b).region 0 C0.epsilon⁻¹ ⊆ V := fun _ hx => hlast hx.1
  have hyV : y ∈ closure V := closure_mono hpositive hyclosure
  obtain ⟨d, hd, hdi⟩ := hdiffeo C0 D hshape hsmallF hstart hsep hout
  obtain ⟨R, hR, heR, hRc, hRs, hRcore, hRend⟩ := C1.exists_outward_boundary_neck
  refine ⟨d, hd, hdi, hyV, ?_⟩
  rcases C0.boundary_subset_or_positive_chain_frontier C1 D hshape hstart hquarters
      hmeet with hcontained | ⟨z, hzcentral, hzfront, hzV, hzclosure, hzlast⟩
  · refine ⟨R, fun _ => 0, R, 0, hR, heR, hRc, hRs, hRcore, hRend,
      contMDiff_const, ?_, ?_, rfl, ?_, Or.inl ⟨hcontained, rfl, rfl, rfl⟩⟩
    · intro q
      exact ⟨le_rfl, hL1⟩
    · simpa only [heR] using
        (show (0 : ℝ) ∈ Ioo (-C1.epsilon⁻¹) C1.epsilon⁻¹ from
          ⟨neg_lt_zero.mpr hL1, hL1⟩)
    · rw [R.coordinate_zero_range, hRs]
      exact hcontained
  · have hzboundary : z ∈ C1.boundary_sphere := by
      simpa only [C1.boundary_eq_neck_sphere] using hzcentral
    have heBoundary : C1.boundary_neck.epsilon = (D.neck b).epsilon :=
      C1.boundary_neck_epsilon.trans (heq.trans heLast.symm)
    have hlastSmall : (D.neck b).epsilon ≤ epsilonG := by
      simpa only [heLast] using hsmallG
    have hzLastClosure : z ∈ closure ((D.neck b).region 0 (D.neck b).epsilon⁻¹) := by
      simpa only [heLast] using hzclosure
    obtain ⟨Rsg, fsg, hRsg, hfsg, hfsgdom, hfsgbounds, hsg⟩ :=
      hgraph (D.neck b) C1.boundary_neck hlastSmall heBoundary z hzcentral
        hzLastClosure hzlast
    have heRsg : Rsg.epsilon = C1.epsilon := by
      rcases hRsg with rfl | rfl <;> exact C1.boundary_neck_epsilon
    have hbounds (q : UnitTwoSphere) :
        -(3 * C0.epsilon⁻¹ / 10) < fsg q ∧ fsg q < -(C0.epsilon⁻¹ / 5) := by
      simpa only [heLast] using hfsgbounds q
    have hfnegative (q : UnitTwoSphere) : fsg q < 0 := by
      linarith only [hL, (hbounds q).2]
    have hsg' :
        range (fun q : UnitTwoSphere =>
          (D.neck b).coordinate_map (q, 3 * C0.epsilon⁻¹ / 4)) =
        range (fun q : UnitTwoSphere => Rsg.coordinate_map (q, fsg q)) := by
      simpa only [heLast] using hsg
    obtain ⟨_, _, _, hyne, hside⟩ :=
      C0.finite_chain_mixed_boundary_side_alternative C1 D hshape hstart hsep
        Rsg fsg hRsg hfsgdom hfnegative hsg' y z hycore hyclosure hyout hzboundary
        hzclosure hzlast
    have hSend : range (fun q : UnitTwoSphere =>
        (D.neck b).coordinate_map (q, 3 * C0.epsilon⁻¹ / 4)) ⊆
          C1.end_neck.carrier := by
      rcases hside with hgood | hbad
      · exact hgood
      · exact (hno hbad.2).elim

    have hne : Rsg ≠ R := by
      intro he
      let q := (Rsg.coordinate_inverse Rsg.center).1
      have hdom : (q, fsg q) ∈ Rsg.cylinderDomain := ⟨mem_univ _, hfsgdom q⟩
      have hxneg : Rsg.coordinate_map (q, fsg q) ∈ Rsg.region (-C1.epsilon⁻¹) 0 := by
        refine ⟨Rsg.coordinate_map_mem hdom, ?_⟩
        rw [Rsg.coordinate_inverse_coordinate_map hdom]
        exact ⟨by simpa only [heRsg] using (hfsgdom q).1, hfnegative q⟩
      have hRsgcore : Rsg.carrier ∩ C1.core = Rsg.region (-C1.epsilon⁻¹) 0 := by
        simpa only [he] using hRcore
      have hxcore : Rsg.coordinate_map (q, fsg q) ∈ C1.core :=
        (show Rsg.coordinate_map (q, fsg q) ∈ Rsg.carrier ∩ C1.core from
          hRsgcore.symm ▸ hxneg).2
      have hxend : Rsg.coordinate_map (q, fsg q) ∈ C1.end_neck.carrier := by
        apply hSend
        rw [hsg']
        exact ⟨q, rfl⟩
      have hxclosed : Rsg.coordinate_map (q, fsg q) ∈ C1.closed_core := by
        rw [C1.core_eq_interior_closed_core] at hxcore
        exact interior_subset hxcore
      rw [C1.closed_core_eq_complement_end] at hxclosed
      exact hxclosed.2 hxend
    have hflip (q : UnitTwoSphere) :
        R.coordinate_map (q, -fsg q) = Rsg.coordinate_map (q, fsg q) := by
      rcases hR with hR0 | hR0 <;> rcases hRsg with hS0 | hS0
      · exact (hne (hS0.trans hR0.symm)).elim
      · rw [hR0, hS0]
        rfl
      · rw [hR0, hS0]
        change C1.boundary_neck.coordinate_map (q, -(-fsg q)) =
          C1.boundary_neck.coordinate_map (q, fsg q)
        rw [neg_neg]
      · exact (hne (hS0.trans hR0.symm)).elim
    have hfpos (q : UnitTwoSphere) :
        C0.epsilon⁻¹ / 5 < -fsg q ∧ -fsg q < 3 * C0.epsilon⁻¹ / 10 := by
      constructor <;> linarith only [(hbounds q).1, (hbounds q).2]
    have hfdom (q : UnitTwoSphere) : -fsg q ∈ Ico (0 : ℝ) C1.epsilon⁻¹ := by
      change 0 ≤ -fsg q ∧ -fsg q < C1.epsilon⁻¹
      rw [heq]
      constructor <;> linarith only [hL, (hfpos q).1, (hfpos q).2]
    have hs : 3 * C0.epsilon⁻¹ / 4 ∈
        Ioo (-(D.neck b).epsilon⁻¹) (D.neck b).epsilon⁻¹ := by
      rw [heLast]
      constructor <;> linarith only [hL]
    have hlevel : range (fun q : UnitTwoSphere => R.coordinate_map (q, -fsg q)) =
        range (fun q : UnitTwoSphere =>
          (D.neck b).coordinate_map (q, 3 * C0.epsilon⁻¹ / 4)) := by
      calc
        _ = range (fun q : UnitTwoSphere => Rsg.coordinate_map (q, fsg q)) := by
          congr 1
          funext q
          exact hflip q
        _ = _ := hsg'.symm
    have hgraphV : range (fun q : UnitTwoSphere =>
        R.coordinate_map (q, -fsg q)) ⊆ V := by
      rw [hlevel]
      rintro x ⟨q, rfl⟩
      exact hlast ((D.neck b).coordinate_map_mem ⟨mem_univ _, hs⟩)
    have hgraphEnd : range (fun q : UnitTwoSphere =>
        R.coordinate_map (q, -fsg q)) ⊆ C1.end_neck.carrier := by
      rw [hlevel]
      exact hSend
    refine ⟨R, fun q => -fsg q, D.neck b, 3 * C0.epsilon⁻¹ / 4,
      hR, heR, hRc, hRs, hRcore, hRend, contDiff_neg.contMDiff.comp hfsg,
      hfdom, hs, hlevel, hgraphV, Or.inr ?_⟩
    exact ⟨z, hzboundary, hzfront, hzV, hzclosure, hzlast, hyne,
      rfl, rfl, hfpos, hgraphEnd⟩

end PoincareConjecture
