import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Bases

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace

universe u

namespace PoincareConjecture.Proofs.M02.Topology

def euclideanThreeOpenBox (a b : Fin 3 → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∀ i, a i < x i ∧ x i < b i}

theorem euclideanThreeOpenBox_isOpen (a b : Fin 3 → ℝ) :
    IsOpen (euclideanThreeOpenBox a b) := by
  have heq : euclideanThreeOpenBox a b =
      ⋂ i : Fin 3, (fun x : EuclideanSpace ℝ (Fin 3) => x i) ⁻¹'
        Ioo (a i) (b i) := by
    ext x
    simp [euclideanThreeOpenBox]
  rw [heq]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ i)

theorem euclideanThreeOpenBox_nonempty_iff (a b : Fin 3 → ℝ) :
    (euclideanThreeOpenBox a b).Nonempty ↔ ∀ i, a i < b i := by
  constructor
  · rintro ⟨x, hx⟩ i
    exact (hx i).1.trans (hx i).2
  · intro h
    refine ⟨WithLp.toLp 2 (fun i => (a i + b i) / 2), ?_⟩
    intro i
    change a i < (a i + b i) / 2 ∧ (a i + b i) / 2 < b i
    constructor <;> linarith [h i]

private def intervalHomeomorphReal (a b : ℝ) (hab : a < b) : Ioo a b ≃ₜ ℝ := by
  have hp : 0 < (b - a) / 2 := by linarith
  let e := affineHomeomorph ((b - a) / 2) ((a + b) / 2) hp.ne'
  have he : e '' Ioo (-1 : ℝ) 1 = Ioo a b := by
    convert affineHomeomorph_image_Ioo ((b - a) / 2) ((a + b) / 2) (-1) 1 hp using 1
    congr 1 <;> ring
  exact ((e.image (Ioo (-1 : ℝ) 1)).trans (Homeomorph.setCongr he)).symm.trans
    (orderIsoIooNegOneOne ℝ).toHomeomorph.symm

private def boxCoordinatesHomeomorph (a b : Fin 3 → ℝ) :
    euclideanThreeOpenBox a b ≃ₜ (∀ i : Fin 3, Ioo (a i) (b i)) where
  toFun x i := ⟨x.val i, x.property i⟩
  invFun y := ⟨WithLp.toLp 2 (fun i => (y i : ℝ)), fun i => (y i).property⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    funext i
    rfl
  continuous_toFun := continuous_pi fun i =>
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.continuous.comp
      (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))).subtype_mk _

def euclideanThreeOpenBoxHomeomorph (a b : Fin 3 → ℝ)
    (h : (euclideanThreeOpenBox a b).Nonempty) :
    euclideanThreeOpenBox a b ≃ₜ EuclideanSpace ℝ (Fin 3) :=
  (boxCoordinatesHomeomorph a b).trans
    ((Homeomorph.piCongrRight fun i => intervalHomeomorphReal (a i) (b i)
      ((euclideanThreeOpenBox_nonempty_iff a b).mp h i)).trans
      (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm)

theorem euclideanThreeOpenBox_inter (a b c d : Fin 3 → ℝ) :
    euclideanThreeOpenBox a b ∩ euclideanThreeOpenBox c d =
      euclideanThreeOpenBox (fun i => max (a i) (c i)) (fun i => min (b i) (d i)) := by
  ext x
  simp only [euclideanThreeOpenBox, mem_inter_iff, mem_ofPred_eq, max_lt_iff, lt_min_iff]
  constructor
  · rintro ⟨hab, hcd⟩ i
    exact ⟨⟨(hab i).1, (hcd i).1⟩, ⟨(hab i).2, (hcd i).2⟩⟩
  · intro h
    exact ⟨fun i => ⟨(h i).1.1, (h i).2.1⟩, fun i => ⟨(h i).1.2, (h i).2.2⟩⟩

theorem euclideanThreeOpenBox_finite_intersection {I : Type u}
    (s : Finset I) (hs : s.Nonempty) (a b : I → Fin 3 → ℝ) :
    ∃ c d : Fin 3 → ℝ, (⋂ i ∈ s, euclideanThreeOpenBox (a i) (b i)) =
      euclideanThreeOpenBox c d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s hi ih =>
    by_cases hs' : s.Nonempty
    · obtain ⟨c, d, hcd⟩ := ih hs'
      refine ⟨fun j => max (a i j) (c j), fun j => min (b i j) (d j), ?_⟩
      rw [Finset.set_biInter_insert, hcd, euclideanThreeOpenBox_inter]
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      exact ⟨a i, b i, by simp⟩

theorem euclideanThreeOpenBox_finite_intersection_empty_or_homeomorph {I : Type u}
    (s : Finset I) (a b : I → Fin 3 → ℝ) :
    (⋂ i ∈ s, euclideanThreeOpenBox (a i) (b i)) = ∅ ∨
      Nonempty ((⋂ i ∈ s, euclideanThreeOpenBox (a i) (b i)) ≃ₜ
        EuclideanSpace ℝ (Fin 3)) := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨c, d, hcd⟩ := euclideanThreeOpenBox_finite_intersection s hs a b
    rw [hcd]
    rcases (euclideanThreeOpenBox c d).eq_empty_or_nonempty with h | h
    · exact Or.inl h
    · exact Or.inr ⟨euclideanThreeOpenBoxHomeomorph c d h⟩
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    have hset : (⋂ i ∈ (∅ : Finset I), euclideanThreeOpenBox (a i) (b i)) =
        (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) := by simp
    rw [hset]
    exact Or.inr ⟨Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 3))⟩

theorem exists_euclideanThreeOpenBox_subset {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U) :
    ∃ a b : Fin 3 → ℝ, x ∈ euclideanThreeOpenBox a b ∧
      euclideanThreeOpenBox a b ⊆ U := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have hn : e '' U ∈ nhds (e x) := (e.isOpenMap U hU).mem_nhds ⟨x, hx, rfl⟩
  rw [nhds_pi, Filter.mem_pi'] at hn
  obtain ⟨s, t, ht, hsub⟩ := hn
  have hinterval : ∀ i : Fin 3, ∃ l r : ℝ, e x i ∈ Ioo l r ∧ Ioo l r ⊆ t i :=
    fun i => mem_nhds_iff_exists_Ioo_subset.mp (ht i)
  choose a b hab hsmall using hinterval
  refine ⟨a, b, hab, ?_⟩
  intro y hy
  have hy' : e y ∈ e '' U := hsub fun i _ => hsmall i (hy i)
  exact e.injective.mem_set_image.mp hy'

def euclideanThreeOpenBoxBasis : Set (Set (EuclideanSpace ℝ (Fin 3))) :=
  {U | ∃ a b : Fin 3 → ℝ, (∀ i, a i < b i) ∧ U = euclideanThreeOpenBox a b}

theorem euclideanThreeOpenBox_isTopologicalBasis :
    IsTopologicalBasis euclideanThreeOpenBoxBasis := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨a, b, -, rfl⟩
    exact euclideanThreeOpenBox_isOpen a b
  · intro x U hx hU
    obtain ⟨a, b, hxab, habU⟩ := exists_euclideanThreeOpenBox_subset hU hx
    exact ⟨euclideanThreeOpenBox a b,
      ⟨a, b, fun i => (hxab i).1.trans (hxab i).2, rfl⟩, hxab, habU⟩

theorem euclideanThreeOpen_eq_union_boxes {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : IsOpen U) :
    U = ⋃₀ {B ∈ euclideanThreeOpenBoxBasis | B ⊆ U} :=
  euclideanThreeOpenBox_isTopologicalBasis.open_eq_sUnion' hU

end PoincareConjecture.Proofs.M02.Topology
