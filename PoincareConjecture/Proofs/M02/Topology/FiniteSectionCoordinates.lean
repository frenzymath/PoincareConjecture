import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance









set_option autoImplicit false

open Set Metric
open scoped BigOperators

universe u

namespace PoincareConjecture.Proofs.M02.Topology

open scoped Classical in
theorem barycentric_coordinates_ge_of_opposite_face_gap
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (s : Finset E) (hs : 2 ≤ s.card) (S : Set E) (z : E) (hzS : z ∈ S)
    (w : E → Real) (hw : ∀ v ∈ s, 0 ≤ w v) (hwsum : ∑ v ∈ s, w v = 1)
    (hwz : ∑ v ∈ s, w v • v = z)
    (a D : Real) (hD : 0 < D)
    (hdiam : diam (convexHull Real (s : Set E)) ≤ D)
    (hgap : ∀ v ∈ s, ∀ y ∈ convexHull Real ((s.erase v : Finset E) : Set E),
      a ≤ infDist y S) :
    ∀ v ∈ s, a / D ≤ w v := by
  classical
  have hz : z ∈ convexHull Real (s : Set E) :=
    Finset.mem_convexHull'.mpr ⟨w, hw, hwsum, hwz⟩
  have hbounded := (s.finite_toSet.isCompact_convexHull Real).isBounded
  intro v hv
  have hwv : 0 ≤ w v := hw v hv
  have hsum : w v + ∑ u ∈ s.erase v, w u = 1 := by
    rw [Finset.add_sum_erase _ _ hv, hwsum]
  have hrestnonneg : 0 ≤ ∑ u ∈ s.erase v, w u :=
    Finset.sum_nonneg (fun u hu => hw u (Finset.mem_of_mem_erase hu))
  have hwvle : w v ≤ 1 := by linarith
  have hsumrest : ∑ u ∈ s.erase v, w u = 1 - w v := by linarith
  have hface (y : E) (hy : y ∈ convexHull Real ((s.erase v : Finset E) : Set E)) :
      y ∈ convexHull Real (s : Set E) := convexHull_mono (Finset.erase_subset _ _) hy
  have hvhull : v ∈ convexHull Real (s : Set E) := subset_convexHull Real _ hv
  apply (div_le_iff₀ hD).mpr
  rcases eq_or_lt_of_le hwvle with hvone | hvlt
  · have hsumzero : ∑ u ∈ s.erase v, w u = 0 := by linarith
    have hzero : ∀ u ∈ s.erase v, w u = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun u hu => hw u (Finset.mem_of_mem_erase hu))).mp hsumzero
    have hveczero : ∑ u ∈ s.erase v, w u • u = 0 :=
      Finset.sum_eq_zero (fun u hu => by rw [hzero u hu, zero_smul])
    have hzv : z = v := by
      rw [← hwz, ← Finset.add_sum_erase _ _ hv, hveczero, hvone, one_smul, add_zero]
    have hne : (s.erase v).Nonempty := by
      apply Finset.card_pos.mp
      have hcard := Finset.card_erase_add_one hv
      omega
    obtain ⟨y, hy⟩ := hne
    have hyhull := subset_convexHull Real (s.erase v : Set E) hy
    calc
      a ≤ infDist y S := hgap v hv y hyhull
      _ ≤ dist y z := infDist_le_dist_of_mem hzS
      _ ≤ D := (dist_le_diam_of_mem hbounded (hface y hyhull) hz).trans hdiam
      _ = w v * D := by rw [hvone, one_mul]
  · have hrestpos : 0 < ∑ u ∈ s.erase v, w u := by linarith
    let y : E := (s.erase v).centerMass w id
    have hy : y ∈ convexHull Real ((s.erase v : Finset E) : Set E) :=
      (s.erase v).centerMass_mem_convexHull
        (fun u hu => hw u (Finset.mem_of_mem_erase hu)) hrestpos (fun u hu => hu)
    have hmass : (1 - w v) • y = ∑ u ∈ s.erase v, w u • u := by
      dsimp [y, Finset.centerMass]
      rw [hsumrest, smul_smul, mul_inv_cancel₀ (by linarith : 1 - w v ≠ 0), one_smul]
    have hzdecomp : z = w v • v + (1 - w v) • y := by
      rw [hmass]
      exact hwz.symm.trans (Finset.add_sum_erase s (fun u => w u • u) hv).symm
    have hyz : y - z = w v • (y - v) := by
      rw [hzdecomp]
      module
    have hdist : dist y z = w v * dist y v := by
      rw [dist_eq_norm, hyz, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hwv, dist_eq_norm]
    calc
      a ≤ infDist y S := hgap v hv y hy
      _ ≤ dist y z := infDist_le_dist_of_mem hzS
      _ = w v * dist y v := hdist
      _ ≤ w v * D := mul_le_mul_of_nonneg_left
        ((dist_le_diam_of_mem hbounded (hface y hy) hvhull).trans hdiam) hwv

open scoped Classical in
theorem exists_barycentric_coordinates_of_opposite_face_gap
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (s : Finset E) (hs : 2 ≤ s.card) (S : Set E) (z : E)
    (hz : z ∈ convexHull Real (s : Set E)) (hzS : z ∈ S)
    (a D : Real) (hD : 0 < D)
    (hdiam : diam (convexHull Real (s : Set E)) ≤ D)
    (hgap : ∀ v ∈ s, ∀ y ∈ convexHull Real ((s.erase v : Finset E) : Set E),
      a ≤ infDist y S) :
    ∃ w : E → Real, (∀ v ∈ s, 0 ≤ w v) ∧ (∑ v ∈ s, w v) = 1 ∧
      (∑ v ∈ s, w v • v) = z ∧ ∀ v ∈ s, a / D ≤ w v := by
  obtain ⟨w, hw, hwsum, hwz⟩ := Finset.mem_convexHull'.mp hz
  exact ⟨w, hw, hwsum, hwz,
    barycentric_coordinates_ge_of_opposite_face_gap s hs S z hzS w hw hwsum hwz
      a D hD hdiam hgap⟩

end PoincareConjecture.Proofs.M02.Topology
