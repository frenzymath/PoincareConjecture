import PoincareConjecture.Proofs.M47.PositiveHistoryComponent
import PoincareConjecture.Proofs.M47.PositiveHistoryOrdinary
import PoincareConjecture.Proofs.M47.PositiveHistoryOnset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

theorem exists_positive_component_history
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {origin b : ℝ}
    (hb : b < 0) (U : TopologicalSpace.Opens (F.slice origin).carrier)
    (hcompact : IsCompact (U : Set (F.slice origin).carrier))
    (hconnected : IsConnected (U : Set (F.slice origin).carrier)) (x0 : U)
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc b 0) U)
    (hbased : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hpositive : SurgeryPositiveComponentAt F origin x0.val) :
    ∃ (a : ℝ) (ha : a ∈ Ico (origin + b) origin),
      ∃ G : RicciFlow 3 U (Icc a origin),
        ∃ d : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc (a - origin) 0) U,
          (∀ s hs hse x, d.forward s hs x = e.forward s hse x) ∧
          (∀ h x, x ∈ U → HEq (d.forward 0 h x) x) ∧
          (∀ (s : ℝ) (hs : s ∈ Icc (a - origin) 0) (x : U),
            (∀ v w : TangentSpace (𝓡 3) x,
              (F.metric (origin + s / 1)).inner (d.forward s hs x.val)
                (mfderiv (𝓡 3) (𝓡 3) (fun y : U => d.forward s hs y.val) x v)
                (mfderiv (𝓡 3) (𝓡 3) (fun y : U => d.forward s hs y.val) x w) =
                  (G.metric (origin + s / 1)).inner x v w) ∧
            (G.connection (origin + s / 1)).scalarCurvature x =
              (F.connection (origin + s / 1)).scalarCurvature (d.forward s hs x.val) ∧
            (G.connection (origin + s / 1)).curvatureTensorNorm x =
              (F.connection (origin + s / 1)).curvatureTensorNorm (d.forward s hs x.val)) ∧
          (∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
            0 ≤ (G.connection a).curvatureTensor x v w v w) ∧
          (∀ t ∈ Ioc a origin, ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
            LeviCivitaData.IsOrthonormalPair (G.metric t) x v w →
              0 < (G.connection t).sectionalCurvature x v w) ∧
          (∀ s ∈ Ico b (a - origin), ∀ (hse : s ∈ Icc b 0) (x : U),
            ¬ SurgeryPositiveComponentAt F (origin + s / 1) (e.forward s hse x.val)) ∧
          (a = origin + b ∨ ∀ x : U,
            ¬ SurgeryPositiveComponentAt F (origin + (a - origin) / 1)
              (d.forward (a - origin) ⟨le_rfl, sub_nonpos.mpr ha.2.le⟩ x.val)) := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  obtain ⟨G0, hread⟩ := exists_component_closed_ordinary_history P hb U hconnected.nonempty e
  have h0 : 0 ∈ Icc b 0 := ⟨hb.le, le_rfl⟩
  have hphysical : SurgeryPositiveComponentAt F (origin + 0 / 1) (e.forward 0 h0 x0.val) := by
    have htransfer (r : ℝ) (hr : r = origin) (y : (F.slice r).carrier)
        (hy : HEq y x0.val) : SurgeryPositiveComponentAt F r y := by
      cases hr
      rw [eq_of_heq hy]
      exact hpositive
    exact htransfer _ (by simp) _ (hbased h0 x0.val x0.property)
  have hterminal := (component_cylinder_positive_iff U e hcompact hconnected 0 h0
    (G0.metric (origin + 0 / 1)) (G0.connection (origin + 0 / 1))
    (fun x v w => ((hread 0 h0 x).1 v w).symm) x0).mpr hphysical
  have hterminal' : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (G0.metric origin) x v w →
        0 < (G0.connection origin).sectionalCurvature x v w := by
    exact (congrArg (fun t => ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (G0.metric t) x v w →
        0 < (G0.connection t).sectionalCurvature x v w)
      (show origin + 0 / 1 = origin by simp)).mp hterminal
  obtain ⟨a, ha, hnonnegative, hafter, hbefore, honset⟩ :=
    exists_positive_history_onset (by linarith : origin + b < origin) G0 hterminal'
  have hI : Icc a origin ⊆ Icc (origin + b) origin := Icc_subset_Icc ha.1 le_rfl
  let G : RicciFlow 3 U (Icc a origin) := {
    metric := G0.metric
    connection := G0.connection
    interval := ordConnected_Icc
    nontrivial := ⟨a, ⟨le_rfl, ha.2.le⟩, origin, ⟨ha.2.le, le_rfl⟩, ha.2.ne⟩
    smooth := G0.smooth.mono (prod_mono hI Subset.rfl)
    equation := fun t ht x v w => (G0.equation t (hI ht) x v w).mono hI }
  have hparam : Icc (a - origin) 0 ⊆ Icc b 0 :=
    Icc_subset_Icc (by linarith [ha.1]) le_rfl
  let d := e.restrict hparam ordConnected_Icc (Subset.refl (U : Set (F.slice origin).carrier))
  refine ⟨a, ha, G, d, ?_, ?_, ?_, hnonnegative, hafter, ?_, ?_⟩
  · intro s hs hse x
    rfl
  · intro h x hx
    exact hbased (hparam h) x hx
  · intro s hs x
    exact hread s (hparam hs) x
  · intro s hs hse x hpos
    have ht : origin + s / 1 ∈ Ico (origin + b) a := by
      simp only [div_one]
      constructor <;> linarith [hs.1, hs.2]
    apply hbefore _ ht
    exact (component_cylinder_positive_iff U e hcompact hconnected s hse
      (G0.metric (origin + s / 1)) (G0.connection (origin + s / 1))
      (fun y v w => ((hread s hse y).1 v w).symm) x).mpr hpos
  · rcases honset with heq | hnot
    · exact Or.inl heq
    · right
      intro x hpos
      have hs : a - origin ∈ Icc (a - origin) 0 := ⟨le_rfl, sub_nonpos.mpr ha.2.le⟩
      have hp := (component_cylinder_positive_iff U e hcompact hconnected (a - origin)
        (hparam hs) (G0.metric (origin + (a - origin) / 1))
        (G0.connection (origin + (a - origin) / 1))
        (fun y v w => ((hread (a - origin) (hparam hs) y).1 v w).symm) x).mpr hpos
      apply hnot
      exact (congrArg (fun t => ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair (G0.metric t) y v w →
          0 < (G0.connection t).sectionalCurvature y v w)
        (show origin + (a - origin) / 1 = a by simp)).mp hp

end PoincareConjecture.M47Positive
