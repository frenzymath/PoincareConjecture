import PoincareConjecture.Proofs.M47.PositiveHistoryRestriction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_positive_onset
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {T b : ℝ}
    (hb : b < 0) (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hcompact : IsCompact (U : Set (F.slice T).carrier))
    (hconnected : IsConnected (U : Set (F.slice T).carrier)) (x : U)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U)
    (based : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hpositive : SurgeryPositiveComponentAt F T x.val) :
    ∃ a ∈ Ico b 0, ∃ G : RicciFlow 3 U (Icc (T + a) T),
      ∃ d : SurgeryFlowCylinder F (F.slice T) T 1 (Icc a 0) U,
        (∀ s hs hse y, d.forward s hs y = e.forward s hse y) ∧
        (∀ hs y, y ∈ U → HEq (d.forward 0 hs y) y) ∧
        (∀ s (hs : s ∈ Icc a 0) (y : U),
          (∀ v w : TangentSpace (𝓡 3) y,
            (F.metric (T + s / 1)).inner (d.forward s hs y.val)
              (mfderiv (𝓡 3) (𝓡 3) (fun z : U => d.forward s hs z.val) y v)
              (mfderiv (𝓡 3) (𝓡 3) (fun z : U => d.forward s hs z.val) y w) =
                (G.metric (T + s / 1)).inner y v w) ∧
          (G.connection (T + s / 1)).scalarCurvature y =
            (F.connection (T + s / 1)).scalarCurvature (d.forward s hs y.val) ∧
          (G.connection (T + s / 1)).curvatureTensorNorm y =
            (F.connection (T + s / 1)).curvatureTensorNorm (d.forward s hs y.val)) ∧
        (∀ t ∈ Icc (T + a) T, ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
          0 ≤ (G.connection t).curvatureTensor y v w v w) ∧
        (∀ s ∈ Ico b a, ∀ (hs : s ∈ Icc b 0) (y : U),
          ¬ SurgeryPositiveComponentAt F (T + s / 1) (e.forward s hs y.val)) ∧
        (a = b ∨ ∀ (ha : a ∈ Icc a 0) (y : U),
          ¬ SurgeryPositiveComponentAt F (T + a / 1) (d.forward a ha y.val)) := by
  obtain ⟨a, ha, G0, d, hagree, hbased, hread, hstart, hafter, hbefore, honset⟩ :=
    M47Positive.exists_positive_component_history P hb U hcompact hconnected x e based hpositive
  have hI : Icc (T + (a - T)) T ⊆ Icc a T := by
    simpa only [add_sub_cancel] using (Subset.refl (Icc a T))
  let G : RicciFlow 3 U (Icc (T + (a - T)) T) := {
    metric := G0.metric
    connection := G0.connection
    interval := ordConnected_Icc
    nontrivial := ⟨a, by simpa only [add_sub_cancel] using
      (show a ∈ Icc a T from ⟨le_rfl, ha.2.le⟩), T,
      by simpa only [add_sub_cancel] using (show T ∈ Icc a T from ⟨ha.2.le, le_rfl⟩), ha.2.ne⟩
    smooth := G0.smooth.mono (prod_mono hI Subset.rfl)
    equation := fun t ht y v w => (G0.equation t (hI ht) y v w).mono hI }
  refine ⟨a - T, ⟨by linarith only [ha.1], sub_neg.mpr ha.2⟩,
    G, d, hagree, hbased, hread, ?_, hbefore, ?_⟩
  · intro t ht y v w
    have ht' : t ∈ Icc a T := hI ht
    rcases eq_or_lt_of_le ht'.1 with hta | hta
    · subst t
      exact hstart y v w
    · exact (G0.connection t).curvatureTensor_diagonal_nonneg_of_orthonormal y
        (fun v w hv hw hvw => (hafter t ⟨hta, ht'.2⟩ y v w ⟨hv, hw, hvw⟩).le) v w
  · rcases honset with hbirth | hnonpositive
    · exact Or.inl (by linarith only [hbirth])
    · exact Or.inr (fun _ y => hnonpositive y)

theorem seed_onset_birth_alternative
    {F : SurgeryFlowData.{u}} {T a b : ℝ}
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hcompact : IsCompact (U : Set (F.slice T).carrier))
    (hconnected : IsConnected (U : Set (F.slice T).carrier))
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U)
    (d : SurgeryFlowCylinder F (F.slice T) T 1 (Icc a 0) U)
    (hb : b ≤ 0)
    (hagree : ∀ s hs hse y, d.forward s hs y = e.forward s hse y)
    (honset : a = b ∨ ∀ (ha : a ∈ Icc a 0) (y : U),
      ¬ SurgeryPositiveComponentAt F (T + a / 1) (d.forward a ha y.val))
    (hbirth : T + b / 1 = 0 ∨ ∃ hT : T + b / 1 ∈ F.surgery_times,
      ∀ [Nonempty (F.slice (T + b / 1)).carrier],
        ∃ i : Fin (F.event (T + b / 1) hT).cap_count,
          (e.forward b ⟨le_rfl, hb⟩ '' (U : Set (F.slice T).carrier) ∩
            ((F.event (T + b / 1) hT).caps i).carrier).Nonempty) :
    ∀ (ha : a ∈ Icc a 0) (y : U), T + a / 1 = 0 ∨
      ¬ SurgeryPositiveComponentAt F (T + a / 1) (d.forward a ha y.val) ∨
      ∃ hT : T + a / 1 ∈ F.surgery_times,
        ∀ [Nonempty (F.slice (T + a / 1)).carrier],
          ∃ i : Fin (F.event (T + a / 1) hT).cap_count,
            (connectedComponent (d.forward a ha y.val) ∩
              ((F.event (T + a / 1) hT).caps i).carrier).Nonempty := by
  intro ha y
  rcases honset with hab | hnonpositive
  · subst a
    rcases hbirth with hzero | ⟨hT, hcontact⟩
    · exact Or.inl hzero
    · refine Or.inr (Or.inr ⟨hT, ?_⟩)
      intro hn
      obtain ⟨i, hi⟩ := hcontact
      refine ⟨i, ?_⟩
      rw [hagree b ha ⟨le_rfl, hb⟩ y.val,
        ← M47.component_cylinder_image_eq e U.isOpen hcompact hconnected
          b ⟨le_rfl, hb⟩ y.property]
      exact hi
  · exact Or.inr (Or.inl (hnonpositive ha y))

end PoincareConjecture.Proofs.M47
