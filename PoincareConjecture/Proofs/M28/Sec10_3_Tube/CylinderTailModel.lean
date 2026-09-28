import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderIntervalModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderEndRegions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

theorem exists_reflected_model (T : OpenCylinderModel U) :
    ∃ T' : OpenCylinderModel U,
      T'.coordinate = (fun z => T.coordinate (z.1, 1 - z.2)) ∧
      T'.inverse = (fun x => ((T.inverse x).1, 1 - (T.inverse x).2)) ∧
      T'.middleSphere = T.middleSphere := by
  have hmem : MapsTo (fun s : ℝ => 1 - s) (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hinv : LeftInvOn (fun s : ℝ => 1 - s) (fun s : ℝ => 1 - s)
      (Ioo (0 : ℝ) 1) := by intro s _hs; dsimp; ring
  obtain ⟨T', hc, hv⟩ := T.exists_model_of_interval_reparametrization subset_rfl
    (V := U) (fun x => ⟨fun hx => ⟨hx, (T.inverse_mem x hx).2⟩, fun hx => hx.1⟩)
    (fun s => 1 - s) (fun s => 1 - s)
    (contDiff_const.sub contDiff_id).contDiffOn
    (contDiff_const.sub contDiff_id).contDiffOn hmem hmem hinv hinv
  refine ⟨T', hc, hv, ?_⟩
  have hmiddle (q : UnitTwoSphere) :
      T'.coordinate (q, 1 / 2) = T.coordinate (q, 1 / 2) := by
    rw [hc]
    norm_num
  ext x
  constructor
  · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hs' : s = 1 / 2 := hs
    subst s
    exact ⟨(q, 1 / 2), ⟨mem_univ _, rfl⟩, (hmiddle q).symm⟩
  · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hs' : s = 1 / 2 := hs
    subst s
    exact ⟨(q, 1 / 2), ⟨mem_univ _, rfl⟩, hmiddle q⟩

theorem exists_positive_tail_model (T : OpenCylinderModel U) {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    ∃ T' : OpenCylinderModel (T.tail true a),
      T'.coordinate = (fun z => T.coordinate (z.1, a + (1 - a) * z.2)) ∧
      T'.inverse =
        (fun x => ((T.inverse x).1, ((T.inverse x).2 - a) / (1 - a))) := by
  have hpos : 0 < 1 - a := sub_pos.mpr ha'
  have hV (x : M) : x ∈ T.tail true a ↔ x ∈ U ∧ (T.inverse x).2 ∈ Ioo a 1 := by
    rw [T.mem_tail_iff_m28 true ha ha']
    constructor
    · intro hx
      exact ⟨hx.1, hx.2, (T.inverse_mem x hx.1).2.2⟩
    · intro hx
      exact ⟨hx.1, hx.2.1⟩
  apply T.exists_model_of_interval_reparametrization
    (fun _ hs => ⟨ha.trans hs.1, hs.2⟩) hV
    (fun s => a + (1 - a) * s) (fun s => (s - a) / (1 - a))
  · exact (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn
  · exact ((contDiff_id.sub contDiff_const).div_const (1 - a)).contDiffOn
  · intro s hs
    change a < a + (1 - a) * s ∧ a + (1 - a) * s < 1
    constructor
    · linarith [mul_pos hpos hs.1]
    · nlinarith [mul_pos hpos (sub_pos.mpr hs.2)]
  · intro s hs
    exact ⟨div_pos (sub_pos.mpr hs.1) hpos,
      (div_lt_one hpos).mpr (sub_lt_sub_right hs.2 a)⟩
  · intro s _hs
    dsimp
    field_simp [hpos.ne']
    ring
  · intro s _hs
    dsimp
    field_simp [hpos.ne']
    ring

end PoincareConjecture.OpenCylinderModel
