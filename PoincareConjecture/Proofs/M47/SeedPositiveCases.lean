import PoincareConjecture.Proofs.M47.SeedComponentBirth
import PoincareConjecture.Proofs.M47.SeedPositiveOnset










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47




theorem exists_positive_seed_cases
    (P : M47Predecessors.{u}) (F : SurgeryFlowData.{u}) {T : ℝ}
    (hT : 0 < T) (hTF : T ∈ F.time_domain) (x : (F.slice T).carrier)
    (hpositive : SurgeryPositiveComponentAt F T x) :
    ∃ U : TopologicalSpace.Opens (F.slice T).carrier,
      (U : Set (F.slice T).carrier) = connectedComponent x ∧
      IsCompact (U : Set (F.slice T).carrier) ∧
      IsConnected (U : Set (F.slice T).carrier) ∧ x ∈ U ∧
      ((∃ hbirth : T ∈ F.surgery_times,
          ∀ [Nonempty (F.slice T).carrier],
            ∃ i : Fin (F.event T hbirth).cap_count,
              ((U : Set (F.slice T).carrier) ∩ ((F.event T hbirth).caps i).carrier).Nonempty) ∨
        ∃ (b : ℝ) (hb : b ∈ Ico (-T) 0),
          ∃ e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U,
            (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) ∧
            (T + b / 1 = 0 ∨ ∃ hbirth : T + b / 1 ∈ F.surgery_times,
              ∀ [Nonempty (F.slice (T + b / 1)).carrier],
                ∃ i : Fin (F.event (T + b / 1) hbirth).cap_count,
                  (e.forward b ⟨le_rfl, hb.2.le⟩ '' (U : Set (F.slice T).carrier) ∩
                    ((F.event (T + b / 1) hbirth).caps i).carrier).Nonempty) ∧
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
                  ¬ SurgeryPositiveComponentAt F (T + a / 1) (d.forward a ha y.val)) ∧
                (∀ (ha : a ∈ Icc a 0) (y : U), T + a / 1 = 0 ∨
                  ¬ SurgeryPositiveComponentAt F (T + a / 1) (d.forward a ha y.val) ∨
                  ∃ hbirth : T + a / 1 ∈ F.surgery_times,
                    ∀ [Nonempty (F.slice (T + a / 1)).carrier],
                      ∃ i : Fin (F.event (T + a / 1) hbirth).cap_count,
                        (connectedComponent (d.forward a ha y.val) ∩
                          ((F.event (T + a / 1) hbirth).caps i).carrier).Nonempty)) := by
  obtain ⟨U, hU, hcompact, hconnected, hx, b, hb, e, hbased, hbirth⟩ :=
    exists_seed_component_birth F hTF x
  refine ⟨U, hU, hcompact, hconnected, hx, ?_⟩
  rcases lt_or_eq_of_le hb.2 with hbneg | hbzero
  · obtain ⟨a, ha, G, d, hagree, hdbased, hread, hnonnegative, hbefore, honset⟩ :=
      exists_seed_positive_onset P hbneg U hcompact hconnected ⟨x, hx⟩ e hbased hpositive
    exact Or.inr ⟨b, ⟨hb.1, hbneg⟩, e, hbased, hbirth,
      a, ha, G, d, hagree, hdbased, hread, hnonnegative, hbefore, honset,
      seed_onset_birth_alternative U hcompact hconnected e d hb.2 hagree honset hbirth⟩
  · subst b
    exact Or.inl (seed_singleton_component_birth_meets_cap hT U e hbased hbirth)

end PoincareConjecture.Proofs.M47
