import PoincareConjecture.Proofs.M47.SeedComponentBirth
import PoincareConjecture.Proofs.M47.SeedSearchAncestors
import PoincareConjecture.Proofs.M47.SeedM15Cylinder
import PoincareConjecture.Proofs.M47.PositiveHistoryOrdinary
import PoincareConjecture.Proofs.M47.PositiveHistoryComponent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_component_history_of_positive_test_line
    (hC : RicciFlowCurvatureTheory.{u}) {F : SurgeryFlowData.{u}} {J : Set ℝ}
    (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T a : ℝ} {I : Set ℝ} {V : Set (F.slice T).carrier}
    (ha : a < 0) (hI : Icc a 0 ⊆ I) (hJ : Icc (T + a) T ⊆ J)
    (test : SurgeryFlowCylinder F (F.slice T) T 1 I V)
    (hbased : ∀ hs y, y ∈ V → HEq (test.forward 0 hs y) y)
    (x : (F.slice T).carrier) (hx : x ∈ V)
    (hpositive : SurgeryPositiveComponentAt F (T + a / 1)
      (test.forward a (hI ⟨le_rfl, ha.le⟩) x)) :
    ∃ U : TopologicalSpace.Opens (F.slice T).carrier,
      (U : Set (F.slice T).carrier) = connectedComponent x ∧
      IsCompact (U : Set (F.slice T).carrier) ∧
      IsConnected (U : Set (F.slice T).carrier) ∧ x ∈ U ∧
      ∃ e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc a 0) U,
        (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) ∧
        (∀ s hs ht, e.forward s hs x = test.forward s ht x) ∧
        ∀ s hs, SurgeryPositiveComponentAt F (T + s / 1) (e.forward s hs x) := by
  have hT : T ∈ F.time_domain := by
    simpa only [zero_div, add_zero] using
      test.time_subset (mem_image_of_mem _ (hI ⟨ha.le, le_rfl⟩))
  have htime : Icc (T + a) T ⊆ F.time_domain := by
    intro t ht
    have hs : t - T ∈ Icc a 0 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [div_one, add_sub_cancel] using
      test.time_subset (mem_image_of_mem _ (hI hs))
  let : CompactSpace (F.slice T).carrier := isCompact_univ_iff.mp (F.slices_compact T hT)
  let : LocallyConnectedSpace (F.slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  let U : TopologicalSpace.Opens (F.slice T).carrier :=
    ⟨connectedComponent x, isOpen_connectedComponent⟩
  have hcompact : IsCompact (U : Set (F.slice T).carrier) := isClosed_connectedComponent.isCompact
  have hconnected : IsConnected (U : Set (F.slice T).carrier) := isConnected_connectedComponent
  have hxU : x ∈ U := mem_connectedComponent
  obtain ⟨b, hb, e, hebased, hstop⟩ := M47Positive.exists_component_birth_cylinder
    F ha.le htime U U.isOpen hcompact hconnected
  have hagree (s : ℝ) (hs : s ∈ Icc b 0) (ht : s ∈ I) :
      e.forward s hs x = test.forward s ht x := by
    have hsmall : Icc s 0 ⊆ Icc b 0 := Icc_subset_Icc hs.1 le_rfl
    have htest : Icc s 0 ⊆ I := (Icc_subset_Icc (hb.1.trans hs.1) le_rfl).trans hI
    exact PoincareConjecture.M47.seedM15_cylinder_eq_of_terminal e test hs.2 hsmall htest x hxU x hx
      (eq_of_heq ((hebased _ x hxU).trans (hbased _ x hx).symm))
  have hba : b = a := by
    rcases hstop with hba | ⟨hbirth, hcap⟩
    · exact hba
    · by_contra hne
      have hab : a < b := lt_of_le_of_ne hb.1 (Ne.symm hne)
      have hbtest : b ∈ I := hI hb
      let : Nonempty (F.slice (T + b / 1)).carrier := ⟨e.forward b ⟨le_rfl, hb.2⟩ x⟩
      obtain ⟨i, hi⟩ := hcap
      have himage := PoincareConjecture.M47.component_cylinder_image_eq e U.isOpen hcompact
        hconnected b ⟨le_rfl, hb.2⟩ hxU
      rw [himage, hagree b ⟨le_rfl, hb.2⟩ hbtest] at hi
      have hbJ : T + b / 1 ∈ J := hJ (by
        simp only [div_one]
        constructor <;> linarith [hb.1, hb.2])
      exact seed_search_nonpositive_of_cap_endpoint hC hpolicy test hx
        (hI ⟨le_rfl, ha.le⟩) hbtest hab hbJ hbirth hi hpositive
  subst b
  refine ⟨U, rfl, hcompact, hconnected, hxU, e, hebased, hagree, ?_⟩
  intro s hs
  apply M46.positive_component_cylinder_line e hxU ⟨le_rfl, ha.le⟩ hs hs.1
  rwa [hagree a ⟨le_rfl, ha.le⟩ (hI ⟨le_rfl, ha.le⟩)]

theorem exists_ordinary_history_of_positive_test_line
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {J : Set ℝ}
    (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T a : ℝ} {I : Set ℝ} {V : Set (F.slice T).carrier}
    (ha : a < 0) (hI : Icc a 0 ⊆ I) (hJ : Icc (T + a) T ⊆ J)
    (test : SurgeryFlowCylinder F (F.slice T) T 1 I V)
    (hbased : ∀ hs y, y ∈ V → HEq (test.forward 0 hs y) y)
    (x : (F.slice T).carrier) (hx : x ∈ V)
    (hpositive : SurgeryPositiveComponentAt F (T + a / 1)
      (test.forward a (hI ⟨le_rfl, ha.le⟩) x)) :
    ∃ U : TopologicalSpace.Opens (F.slice T).carrier,
      (U : Set (F.slice T).carrier) = connectedComponent x ∧
      IsCompact (U : Set (F.slice T).carrier) ∧
      IsConnected (U : Set (F.slice T).carrier) ∧ x ∈ U ∧
      ∃ e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc a 0) U,
        (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) ∧
        (∀ s hs ht, e.forward s hs x = test.forward s ht x) ∧
        ∃ G : RicciFlow 3 U (Icc (T + a) T),
          ∀ s hs, (∀ y : U,
            (∀ v w : TangentSpace (𝓡 3) y,
              (F.metric (T + s / 1)).inner (e.forward s hs y.val)
                (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
                (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) =
                  (G.metric (T + s / 1)).inner y v w) ∧
            (G.connection (T + s / 1)).scalarCurvature y =
              (F.connection (T + s / 1)).scalarCurvature (e.forward s hs y.val) ∧
            (G.connection (T + s / 1)).curvatureTensorNorm y =
              (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs y.val)) ∧
            (∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
              LeviCivitaData.IsOrthonormalPair (G.metric (T + s / 1)) y v w →
                0 < (G.connection (T + s / 1)).sectionalCurvature y v w) := by
  obtain ⟨U, hU, hcompact, hconnected, hxU, e, hebased, hagree, hpos⟩ :=
    exists_component_history_of_positive_test_line P.m04 hpolicy ha hI hJ test hbased x hx
      hpositive
  obtain ⟨G, hread⟩ := M47Positive.exists_component_closed_ordinary_history P ha U
    ⟨x, hxU⟩ e
  refine ⟨U, hU, hcompact, hconnected, hxU, e, hebased, hagree, G, ?_⟩
  intro s hs
  exact ⟨hread s hs, (M47Positive.component_cylinder_positive_iff U e hcompact hconnected
    s hs (G.metric (T + s / 1)) (G.connection (T + s / 1))
    (fun y v w => ((hread s hs y).1 v w).symm) ⟨x, hxU⟩).mpr (hpos s hs)⟩

end PoincareConjecture.Proofs.M47
