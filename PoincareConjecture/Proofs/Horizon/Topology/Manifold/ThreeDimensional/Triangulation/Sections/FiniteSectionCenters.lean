import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Sections.FiniteSectionCoordinates
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators

universe u

namespace Poincare.Topology

def sectionFacePoint
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (S : Set E) (t : Finset E) : E := by
  classical
  exact if h : ∃ x ∈ convexHull Real (t : Set E), x ∈ S then h.choose else 0

theorem sectionFacePoint_mem
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (S : Set E) (t : Finset E) (ht : ∃ x ∈ convexHull Real (t : Set E), x ∈ S) :
    sectionFacePoint S t ∈ convexHull Real (t : Set E) ∧ sectionFacePoint S t ∈ S := by
  rw [sectionFacePoint, dif_pos ht]
  exact ht.choose_spec

def minimalSectionFaces
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (S : Set E) (k : Nat) (s : Finset E) : Finset (Finset E) := by
  classical
  exact s.powerset.filter (fun t =>
    t.card = k ∧ ∃ x ∈ convexHull Real (t : Set E), x ∈ S)

theorem mem_minimalSectionFaces
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (S : Set E) (k : Nat) (s t : Finset E) :
    t ∈ minimalSectionFaces S k s ↔
      t ⊆ s ∧ t.card = k ∧ ∃ x ∈ convexHull Real (t : Set E), x ∈ S := by
  simp only [minimalSectionFaces, Finset.mem_filter, Finset.mem_powerset]

def finiteSectionCenter
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (S : Set E) (k : Nat) (s : Finset E) : E :=
  (minimalSectionFaces S k s).centerMass (fun _ => (1 : Real)) (sectionFacePoint S)

theorem finiteSectionCenter_coordinates
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (S : Set E) (k : Nat) (hk : 2 ≤ k) (s : Finset E) (hs : s.Nonempty)
    (a D : Real) (ha : 0 < a) (hD : 0 < D)
    (hdiam : diam (convexHull Real (s : Set E)) ≤ D)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card < k →
      ∀ y ∈ convexHull Real (t : Set E), a ≤ infDist y S)
    (hinc : ∀ v ∈ s, ∃ t : Finset E, t ⊆ s ∧ v ∈ t ∧ t.card = k ∧
      ∃ x ∈ convexHull Real (t : Set E), x ∈ S) :
    ∃ w : E → Real, (∀ v ∈ s, 0 ≤ w v) ∧ (∑ v ∈ s, w v) = 1 ∧
      (∑ v ∈ s, w v • v) = finiteSectionCenter S k s ∧
      ∀ v ∈ s, a / (D * (2 : Real) ^ s.card) ≤ w v := by
  classical
  let F := minimalSectionFaces S k s
  have hmem (t : F) := (mem_minimalSectionFaces S k s t).mp t.property
  have hFne : F.Nonempty := by
    obtain ⟨v, hv⟩ := hs
    obtain ⟨t, hts, hvt, htc, hmeet⟩ := hinc v hv
    exact ⟨t, (mem_minimalSectionFaces S k s t).mpr ⟨hts, htc, hmeet⟩⟩
  have hcard : (0 : Real) < F.card := by exact_mod_cast hFne.card_pos
  have hcardle : (F.card : Real) ≤ (2 : Real) ^ s.card := by
    have h := Finset.card_le_card (Finset.filter_subset
      (fun t : Finset E => t.card = k ∧ ∃ x ∈ convexHull Real (t : Set E), x ∈ S) s.powerset)
    rw [Finset.card_powerset] at h
    exact_mod_cast h
  have hcoords (t : F) : ∃ w : E → Real, (∀ v ∈ t.val, 0 ≤ w v) ∧
      (∑ v ∈ t.val, w v) = 1 ∧ (∑ v ∈ t.val, w v • v) = sectionFacePoint S t.val ∧
      ∀ v ∈ t.val, a / D ≤ w v := by
    obtain ⟨hpoint, hpointS⟩ := sectionFacePoint_mem S t (hmem t).2.2
    apply exists_barycentric_coordinates_of_opposite_face_gap t.val (by
      rw [(hmem t).2.1]
      exact hk) S _ hpoint hpointS a D hD
    · exact (diam_mono (convexHull_mono (hmem t).1)
        (s.finite_toSet.isCompact_convexHull Real).isBounded).trans hdiam
    · intro v hv y hy
      apply hgap (t.val.erase v) ((Finset.erase_subset _ _).trans (hmem t).1) _ y hy
      have h := Finset.card_erase_add_one hv
      have htcard := (hmem t).2.1
      omega
  choose w0 hw0 hsum0 hpoint0 hbound0 using hcoords
  let w1 (t : F) (v : E) : Real := if v ∈ t.val then w0 t v else 0
  have hnonneg (t : F) (v : E) : 0 ≤ w1 t v := by
    dsimp [w1]
    split_ifs with hv
    · exact hw0 t v hv
    · exact le_rfl
  have hextsum (t : F) : ∑ v ∈ s, w1 t v = 1 := by
    calc
      ∑ v ∈ s, w1 t v = ∑ v ∈ t.val, w1 t v :=
        (Finset.sum_subset (hmem t).1 (fun v _ hv => by simp [w1, hv])).symm
      _ = ∑ v ∈ t.val, w0 t v :=
        Finset.sum_congr rfl (fun v hv => if_pos hv)
      _ = 1 := hsum0 t
  have hextpoint (t : F) : ∑ v ∈ s, w1 t v • v = sectionFacePoint S t.val := by
    calc
      ∑ v ∈ s, w1 t v • v = ∑ v ∈ t.val, w1 t v • v :=
        (Finset.sum_subset (hmem t).1 (fun v _ hv => by simp [w1, hv])).symm
      _ = ∑ v ∈ t.val, w0 t v • v :=
        Finset.sum_congr rfl (fun v hv => by rw [show w1 t v = w0 t v from if_pos hv])
      _ = sectionFacePoint S t.val := hpoint0 t
  let w (v : E) : Real := (F.card : Real)⁻¹ * ∑ t : F, w1 t v
  have hw (v : E) : 0 ≤ w v :=
    mul_nonneg (inv_nonneg.mpr hcard.le) (Finset.sum_nonneg (fun t _ => hnonneg t v))
  have hwsum : ∑ v ∈ s, w v = 1 := by
    change (∑ v ∈ s, (F.card : Real)⁻¹ * ∑ t : F, w1 t v) = 1
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [hextsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_coe]
    exact inv_mul_cancel₀ hcard.ne'
  have hwpoint : ∑ v ∈ s, w v • v = finiteSectionCenter S k s := by
    change (∑ v ∈ s, ((F.card : Real)⁻¹ * ∑ t : F, w1 t v) • v) = _
    simp only [mul_smul, Finset.sum_smul]
    rw [← Finset.smul_sum, Finset.sum_comm]
    simp only [hextpoint]
    change (F.card : Real)⁻¹ • ∑ t : F, sectionFacePoint S t.val =
      F.centerMass (fun _ => (1 : Real)) (sectionFacePoint S)
    rw [Finset.centerMass]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_smul]
    rw [Finset.sum_coe_sort]
  refine ⟨w, fun v _ => hw v, hwsum, hwpoint, ?_⟩
  intro v hv
  obtain ⟨t, hts, hvt, htc, hmeet⟩ := hinc v hv
  have htF : t ∈ F := (mem_minimalSectionFaces S k s t).mpr ⟨hts, htc, hmeet⟩
  let t0 : F := ⟨t, htF⟩
  have hsumlow : a / D ≤ ∑ r : F, w1 r v := by
    have ht0 : a / D ≤ w1 t0 v := by
      change a / D ≤ if v ∈ t then w0 t0 v else 0
      rw [if_pos hvt]
      exact hbound0 t0 v hvt
    exact ht0.trans (Finset.single_le_sum (fun r _ => hnonneg r v) (Finset.mem_univ t0))
  calc
    a / (D * (2 : Real) ^ s.card) ≤ a / (D * F.card) :=
      div_le_div_of_nonneg_left ha.le (mul_pos hD hcard)
        (mul_le_mul_of_nonneg_left hcardle hD.le)
    _ = (F.card : Real)⁻¹ * (a / D) := by ring
    _ ≤ (F.card : Real)⁻¹ * ∑ t : F, w1 t v :=
      mul_le_mul_of_nonneg_left hsumlow (inv_nonneg.mpr hcard.le)
    _ = w v := rfl

end Poincare.Topology
