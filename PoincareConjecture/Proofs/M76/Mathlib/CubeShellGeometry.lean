import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarShear
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineSlabComplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false

open Set Geometry

namespace CubeShell

abbrev Ambient := (ℝ × ℝ) × ℝ

def coordinate (i : Fin 3) : Ambient →L[ℝ] ℝ :=
  ![(ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ),
    ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ] i

def vector (v : Fin 3 → ℝ) : Ambient := ((v 0, v 1), v 2)

theorem coordinate_vector (v : Fin 3 → ℝ) (i : Fin 3) :
    coordinate i (vector v) = v i := by
  fin_cases i <;> rfl

theorem vector_coordinate (x : Ambient) : vector (fun i => coordinate i x) = x := rfl

theorem norm_le_iff (x : Ambient) (r : ℝ) :
    ‖x‖ ≤ r ↔ ∀ i : Fin 3, |coordinate i x| ≤ r := by
  change max (max |x.1.1| |x.1.2|) |x.2| ≤ r ↔ _
  rw [max_le_iff, max_le_iff]
  constructor
  · intro h i
    fin_cases i
    · exact h.1.1
    · exact h.1.2
    · exact h.2
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩

theorem abs_coordinate_le_norm (x : Ambient) (i : Fin 3) :
    |coordinate i x| ≤ ‖x‖ := (norm_le_iff x ‖x‖).mp le_rfl i

theorem exists_abs_coordinate_eq_norm (x : Ambient) :
    ∃ i : Fin 3, |coordinate i x| = ‖x‖ := by
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image
    (fun j : Fin 3 => |coordinate j x|) Finset.univ_nonempty
  exact ⟨i, le_antisymm (abs_coordinate_le_norm x i)
    ((norm_le_iff x _).mpr (fun j => hi j (Finset.mem_univ j)))⟩

def signedCoordinate (i : Fin 3 ⊕ Fin 3) : Ambient →L[ℝ] ℝ :=
  match i with
  | .inl j => coordinate j
  | .inr j => -coordinate j

theorem signedCoordinate_le_norm (x : Ambient) (i : Fin 3 ⊕ Fin 3) :
    signedCoordinate i x ≤ ‖x‖ := by
  cases i with
  | inl j => exact (le_abs_self _).trans (abs_coordinate_le_norm x j)
  | inr j => exact (neg_le_abs _).trans (abs_coordinate_le_norm x j)

theorem exists_signedCoordinate_eq_norm (x : Ambient) :
    ∃ i : Fin 3 ⊕ Fin 3, signedCoordinate i x = ‖x‖ := by
  obtain ⟨i, hi⟩ := exists_abs_coordinate_eq_norm x
  rcases le_total 0 (coordinate i x) with h | h
  · exact ⟨.inl i, (abs_of_nonneg h).symm.trans hi⟩
  · exact ⟨.inr i, (abs_of_nonpos h).symm.trans hi⟩

theorem finitePiecewiseAffineOn_norm (K : SimplicialComplex ℝ Ambient)
    (hK : K.faces.Finite) : FinitePiecewiseAffineOn (norm : Ambient → ℝ) K.space := by
  have habs (i : Fin 3) : FinitePiecewiseAffineOn (fun x => |coordinate i x|) K.space := by
    have hpos := (K.affineOnFaces_affine
      (coordinate i).toContinuousAffineMap).finitePiecewiseAffineOn hK
    have hneg := (K.affineOnFaces_affine
      (-coordinate i).toContinuousAffineMap).finitePiecewiseAffineOn hK
    exact (hpos.max hneg).congr (fun x _ => (abs_eq_max_neg (a := coordinate i x)).symm)
  apply (((habs 0).max (habs 1)).max (habs 2)).congr
  intro x _
  rfl

def shell (a b : ℝ) : Set Ambient := {x | ‖x‖ ∈ Icc a b}

theorem exists_finite_shell_complex (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ K : SimplicialComplex ℝ Ambient, K.faces.Finite ∧ K.space = shell a b := by
  obtain ⟨_, C, _, _, _, e, he, _⟩ := CoordinateHalfBoxes.box_ballPair hb
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := he
  have hKball : K.space = Metric.closedBall (0 : Ambient) b :=
    hKs.trans (CoordinateHalfBoxes.box_eq_closedBall b)
  have hex (i : Fin 3 ⊕ Fin 3) := K.exists_finite_affineSlab_complex hK
    (signedCoordinate i).toLinearMap.toAffineMap a b
  choose J hJ hJs using hex
  obtain ⟨L, hL, hLs, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion J hJ
  refine ⟨L, hL, hLs.trans ?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    rw [hJs i, hKball] at hi
    exact ⟨hi.2.1.trans (signedCoordinate_le_norm x i),
      by simpa only [Metric.mem_closedBall, dist_zero_right] using hi.1⟩
  · intro hx
    obtain ⟨i, hi⟩ := exists_signedCoordinate_eq_norm x
    refine ⟨i, ?_⟩
    rw [hJs i, hKball]
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2
    · change signedCoordinate i x ∈ Icc a b
      rwa [hi]

end CubeShell
