import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEventRegions
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.RetainedCapPlacement











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem RegularSurgeryEvent.children_middle_band
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) :
    let c := E.data.width / 2 * (1 - E.radius)
    let W := {y : E3 | |⟪(u : E3), y⟫_ℝ - E.cutHeight| < c / 2}
    let A := E.data.tube '' (sphere (0 : E2) 1 ×ˢ
      Ioo (E.cutHeight - c / 2) (E.cutHeight + c / 2))
    ((E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
      (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))) ∩ W =
      ((parent '' (univ ×ˢ ({0} : Set ℝ))) \ A) ∩ W := by
  let c := E.data.width / 2 * (1 - E.radius)
  let W := {y : E3 | |⟪(u : E3), y⟫_ℝ - E.cutHeight| < c / 2}
  let A := E.data.tube '' (sphere (0 : E2) 1 ×ˢ
    Ioo (E.cutHeight - c / 2) (E.cutHeight + c / 2))
  let oldA := E.data.tube '' (sphere (0 : E2) 1 ×ˢ
    Ioo (E.cutHeight - c) (E.cutHeight + c))
  let core : Fin 2 → Set E3 := fun i =>
    (fun p : UnitTwoSphere => parent (p, 0)) ''
      ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
        closedBall (0 : E2) E.radius)
  change ((E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
    (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))) ∩ W =
      ((parent '' (univ ×ˢ ({0} : Set ℝ))) \ A) ∩ W
  obtain ⟨_hd, hc, _hck, _hkw, _hl, _hlM⟩ := E.parameter_bounds
  change 0 < c at hc
  obtain ⟨hparent, hcore, _hpair, hchild, _hseam, _hchildren⟩ := E.region_identities
  change parent '' (univ ×ˢ ({0} : Set ℝ)) = core 0 ∪ core 1 ∪ oldA at hparent
  change ∀ i : Fin 2, Disjoint (core i) oldA at hcore
  change ∀ i : Fin 2, E.child i '' (univ ×ˢ ({0} : Set ℝ)) =
    core i ∪ (E.newCap i).cap at hchild
  have hAsub : A ⊆ oldA := by
    rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, heq⟩
    exact ⟨(x, z), ⟨hx, by constructor <;> linarith [hz.1, hz.2]⟩, heq⟩
  have hrestrict (y : E3) (hyW : y ∈ W) (hyA : y ∈ oldA) : y ∈ A := by
    obtain ⟨⟨x, z⟩, ⟨hx, _hz⟩, rfl⟩ := hyA
    change |⟪(u : E3), E.data.tube (x, z)⟫_ℝ - E.cutHeight| < c / 2 at hyW
    rw [E.data.tube_height] at hyW
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hyW
    exact ⟨(x, z), ⟨hx, by constructor <;> linarith⟩, rfl⟩
  have hcap (i : Fin 2) (y : E3) (hyW : y ∈ W) : y ∉ (E.newCap i).cap := by
    intro hyC
    have hb := (E.newCap i).cap_abs_height_bounds y hyC
    obtain ⟨_hp, _hT, ht, hr, _hl, _hs⟩ := E.newCap_spec i
    rw [ht, hr] at hb
    change 3 * c / 4 < |⟪(u : E3), y⟫_ℝ - E.cutHeight| ∧
      |⟪(u : E3), y⟫_ℝ - E.cutHeight| ≤ c at hb
    change |⟪(u : E3), y⟫_ℝ - E.cutHeight| < c / 2 at hyW
    linarith [hb.1]
  have hchildren (y : E3) (hyW : y ∈ W) :
      y ∈ (E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
          (E.child 1 '' (univ ×ˢ ({0} : Set ℝ))) ↔ y ∈ core 0 ∪ core 1 := by
    rw [hchild 0, hchild 1]
    simp only [mem_union, hcap 0 y hyW, hcap 1 y hyW, or_false]
  ext y
  constructor
  · rintro ⟨hyQ, hyW⟩
    have hyK := (hchildren y hyW).mp hyQ
    refine ⟨⟨?_, ?_⟩, hyW⟩
    · rw [hparent]
      exact Or.inl hyK
    · intro hyA
      rcases hyK with hy0 | hy1
      · exact disjoint_left.mp (hcore 0) hy0 (hAsub hyA)
      · exact disjoint_left.mp (hcore 1) hy1 (hAsub hyA)
  · rintro ⟨⟨hyP, hyA⟩, hyW⟩
    refine ⟨(hchildren y hyW).mpr ?_, hyW⟩
    rw [hparent] at hyP
    rcases hyP with hyK | hyOld
    · exact hyK
    · exact False.elim (hyA (hrestrict y hyW hyOld))


theorem RegularSurgeryEvent.children_middle_level
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (z : ℝ)
    (hz : |z - E.cutHeight| < E.data.width / 2 * (1 - E.radius) / 2) :
    ((E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
      (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))) ∩
        {y : E3 | ⟪(u : E3), y⟫_ℝ = z} =
      ((parent '' (univ ×ˢ ({0} : Set ℝ))) ∩
        {y : E3 | ⟪(u : E3), y⟫_ℝ = z}) \
        E.data.tube '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
  let c := E.data.width / 2 * (1 - E.radius)
  change |z - E.cutHeight| < c / 2 at hz
  let W := {y : E3 | |⟪(u : E3), y⟫_ℝ - E.cutHeight| < c / 2}
  let A := E.data.tube '' (sphere (0 : E2) 1 ×ˢ
    Ioo (E.cutHeight - c / 2) (E.cutHeight + c / 2))
  let Az := E.data.tube '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))
  have hband := E.children_middle_band
  change ((E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
    (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))) ∩ W =
      ((parent '' (univ ×ˢ ({0} : Set ℝ))) \ A) ∩ W at hband
  have hW (y : E3) (hy : ⟪(u : E3), y⟫_ℝ = z) : y ∈ W := by
    change |⟪(u : E3), y⟫_ℝ - E.cutHeight| < c / 2
    rw [hy]
    exact hz
  have hA (y : E3) (hy : ⟪(u : E3), y⟫_ℝ = z) : y ∈ A ↔ y ∈ Az := by
    constructor
    · rintro ⟨⟨x, w⟩, ⟨hx, _hw⟩, heq⟩
      have hwz : w = z := by
        calc
          w = ⟪(u : E3), E.data.tube (x, w)⟫_ℝ := (E.data.tube_height (x, w)).symm
          _ = ⟪(u : E3), y⟫_ℝ := congrArg (fun v => ⟪(u : E3), v⟫_ℝ) heq
          _ = z := hy
      subst w
      exact ⟨(x, z), ⟨hx, rfl⟩, heq⟩
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, heq⟩
      have hwz : w = z := hw
      subst w
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hz
      exact ⟨(x, z), ⟨hx, by constructor <;> linarith⟩, heq⟩
  ext y
  constructor
  · rintro ⟨hyQ, hyz⟩
    have hy := (Set.ext_iff.mp hband y).mp ⟨hyQ, hW y hyz⟩
    exact ⟨⟨hy.1.1, hyz⟩, fun hyAz => hy.1.2 ((hA y hyz).mpr hyAz)⟩
  · rintro ⟨⟨hyP, hyz⟩, hyAz⟩
    have hy := (Set.ext_iff.mp hband y).mpr
      ⟨⟨hyP, fun hyA => hyAz ((hA y hyz).mp hyA)⟩, hW y hyz⟩
    exact ⟨hy.1, hyz⟩


theorem RegularSurgeryEvent.children_outside_band
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) :
    let W := {y : E3 | E.data.width ≤
      |⟪(u : E3), y⟫_ℝ - E.cutHeight|}
    ((E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
      (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))) ∩ W =
      (parent '' (univ ×ˢ ({0} : Set ℝ))) ∩ W := by
  let c := E.data.width / 2 * (1 - E.radius)
  let W := {y : E3 | E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight|}
  let oldA := E.data.tube '' (sphere (0 : E2) 1 ×ˢ
    Ioo (E.cutHeight - c) (E.cutHeight + c))
  let core : Fin 2 → Set E3 := fun i =>
    (fun p : UnitTwoSphere => parent (p, 0)) ''
      ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
        closedBall (0 : E2) E.radius)
  change ((E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
    (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))) ∩ W =
      (parent '' (univ ×ˢ ({0} : Set ℝ))) ∩ W
  obtain ⟨_hd, _hc, hck, hkw, _hl, _hlM⟩ := E.parameter_bounds
  have hcw : c < E.data.width := hck.trans hkw
  obtain ⟨hparent, _hcore, _hpair, hchild, _hseam, _hchildren⟩ := E.region_identities
  change parent '' (univ ×ˢ ({0} : Set ℝ)) = core 0 ∪ core 1 ∪ oldA at hparent
  change ∀ i : Fin 2, E.child i '' (univ ×ˢ ({0} : Set ℝ)) =
    core i ∪ (E.newCap i).cap at hchild
  have hcap (i : Fin 2) (y : E3) (hyW : y ∈ W) : y ∉ (E.newCap i).cap := by
    intro hyC
    have hb := (E.newCap i).cap_abs_height_bounds y hyC
    obtain ⟨_hp, _hT, ht, hr, _hl, _hs⟩ := E.newCap_spec i
    rw [ht, hr] at hb
    exact (not_le_of_gt hcw) (hyW.trans hb.2)
  have hannulus (y : E3) (hyW : y ∈ W) : y ∉ oldA := by
    rintro ⟨⟨x, z⟩, ⟨_hx, hz⟩, rfl⟩
    change E.data.width ≤ |⟪(u : E3), E.data.tube (x, z)⟫_ℝ - E.cutHeight| at hyW
    rw [E.data.tube_height] at hyW
    have hzabs : |z - E.cutHeight| < c :=
      abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    exact (not_le_of_gt (hzabs.trans hcw)) hyW
  rw [hchild 0, hchild 1, hparent]
  ext y
  by_cases hyW : y ∈ W
  · simp only [mem_inter_iff, mem_union, hyW, hcap 0 y hyW,
      hcap 1 y hyW, hannulus y hyW, or_false, and_true]
  · simp only [mem_inter_iff, hyW, and_false]

end PoincareConjecture.M25.Topology3D
