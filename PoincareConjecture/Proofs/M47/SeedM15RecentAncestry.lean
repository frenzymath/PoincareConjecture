import PoincareConjecture.Proofs.M47.SeedM15BirthCap
import PoincareConjecture.Proofs.M47.SeedM15TerminalCap
import PoincareConjecture.Proofs.M47.SeedM15OnsetPath
import PoincareConjecture.Proofs.M47.SeedM15TestHistory
import PoincareConjecture.Proofs.M47.SeedComponentBirth









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M46



theorem seedM15_recent_path_nonpositive
    (hC : RicciFlowCurvatureTheory.{u})
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (hpolicy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain} {x : (F.slice T).carrier}
    (H : SeedM15TestHistory T hT hTF x r) (hTO : T ∈ surgeryObservationInterval O)
    {a b : ℝ} (hb : b ∈ Icc (-T) 0) (ha : a ∈ Icc b 0)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hU : (U : Set (F.slice T).carrier) = connectedComponent x)
    (hcompact : IsCompact (U : Set (F.slice T).carrier))
    (hconnected : IsConnected (U : Set (F.slice T).carrier))
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U)
    (hbased : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hbirth : T + b / 1 = 0 ∨ ∃ hsurgery : T + b / 1 ∈ F.surgery_times,
      ∀ [Nonempty (F.slice (T + b / 1)).carrier],
        ∃ i : Fin (F.event (T + b / 1) hsurgery).cap_count,
          (e.forward b ⟨le_rfl, hb.2⟩ '' (U : Set (F.slice T).carrier) ∩
            ((F.event (T + b / 1) hsurgery).caps i).carrier).Nonempty)
    (honset : a = b ∨ ∀ z : U,
      ¬ SurgeryPositiveComponentAt F (T + a / 1) (e.forward a ha z.val))
    {S : ℝ} {endpoint : H.spacetime.geometry.toLGeometry.Point}
    (path : M14BackwardPath H.spacetime.geometry.toLGeometry T 0 S
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val endpoint)
    {tau : ℝ} (htau : tau ∈ Ioc 0 S)
    (hpoint0 : 0 ≤ T - tau) (hbefore : T - tau < T + a / 1) :
    ¬ HistoryPositive H.spacetime.history.history (path.curve tau) := by
  have hx : x ∈ U := by
    change x ∈ (U : Set (F.slice T).carrier)
    rw [hU]
    exact mem_connectedComponent
  let x0 : U := ⟨x, hx⟩
  have hinterval : Icc (T + b) T ⊆ H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    intro s hs
    exact ⟨by linarith [hb.1, hs.1], hs.2⟩
  by_cases hab : a = b
  · subst a
    by_cases hbzero : b = 0
    · subst b
      obtain ⟨hsurgery, hcontact⟩ := Proofs.M47.seed_singleton_component_birth_meets_cap
        hT U e hbased hbirth
      let : Nonempty (F.slice T).carrier := ⟨x⟩
      obtain ⟨i, hi⟩ := hcontact
      have hcontact' : (connectedComponent
          (H.spacetime.history.history.forward T H.time_mem H.center) ∩
          ((F.event T hsurgery).caps i).carrier).Nonempty := by
        rw [H.center_eq, ← hU]
        exact hi
      exact seedM15_terminal_cap_path_nonpositive hC H.spacetime hpolicy hTO hsurgery
        H.time_mem H.center hcontact' path htau
    · have hblt : b < 0 := lt_of_le_of_ne hb.2 hbzero
      have hnotzero : T + b / 1 ≠ 0 := by
        intro hzero
        rw [hzero] at hbefore
        exact (not_lt_of_ge hpoint0) hbefore
      obtain ⟨hsurgery, hcontact⟩ := hbirth.resolve_left hnotzero
      let : Nonempty (F.slice (T + b / 1)).carrier :=
        ⟨e.forward b ⟨le_rfl, hb.2⟩ x⟩
      obtain ⟨i, hi⟩ := hcontact
      have hcontact' : (connectedComponent (e.forward b ⟨le_rfl, hb.2⟩ x0.val) ∩
          ((F.event (T + b / 1) hsurgery).caps i).carrier).Nonempty := by
        rw [← component_cylinder_image_eq e U.isOpen hcompact hconnected
          b ⟨le_rfl, hb.2⟩ x0.property]
        exact hi
      have hbirthO : T + b / 1 ∈ surgeryObservationInterval O := by
        simp only [surgeryObservationInterval, mem_Ico, div_one]
        exact ⟨by linarith [hb.1], by linarith [hTO.2]⟩
      exact seedM15_birth_cap_path_nonpositive hC H.spacetime hpolicy hblt
        U hcompact hconnected x0 e hinterval hbased H.time_mem H.center H.center_eq
        hbirthO hsurgery hcontact' path htau hbefore
  · have hba : b < a := lt_of_le_of_ne ha.1 (Ne.symm hab)
    have hnot := honset.resolve_left hab
    exact seedM15_onset_path_nonpositive H.spacetime U hcompact e hinterval hbased
      H.time_mem H.center x0 H.center_eq ⟨hba, ha.2⟩ hnot path htau hbefore

end PoincareConjecture.M47
