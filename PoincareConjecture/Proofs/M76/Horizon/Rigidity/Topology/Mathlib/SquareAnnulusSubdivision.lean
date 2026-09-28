import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SquareAnnulusCount
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnularStripCharts
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusFinitePL
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.SharedBoundaryConeUnion











set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PLAnnularStrip

theorem exists_squareAnnulus_common_subdivision {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ (R : SimplicialComplex ℝ (ℝ × ℝ))
      (D : Fin 4 → SimplicialComplex ℝ (ℝ × ℝ))
      (U₀₁ U₂₃ W K : SimplicialComplex ℝ (ℝ × ℝ)),
      R.faces.Finite ∧
      (∀ i, (D i).faces.Finite ∧ (D i).space = stripRegion L d i ∧ D i ≤ R) ∧
      U₀₁.faces = (D 0).faces ∪ (D 1).faces ∧
      U₂₃.faces = (D 2).faces ∪ (D 3).faces ∧
      W.faces = ((D 0 ⊓ D 3).faces ∪ (D 1 ⊓ D 2).faces) ∧
      K.faces = U₀₁.faces ∪ U₂₃.faces ∧
      K.space = squareAnnulus L d := by
  classical
  have hwidth' : 2 * d < L := by linarith
  choose e he using exists_rotated_strip_charts hd hwidth
  choose f hf hfv using fun i => (he i).1
  have himage (i : Fin 4) : f i '' rectangle L d = stripRegion L d i := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hfv i ⟨x, hx⟩]
      exact (e i ⟨x, hx⟩).property
    · intro hy
      let x := (e i).symm ⟨y, hy⟩
      refine ⟨x, ?_, ?_⟩
      · exact x.property
      · rw [← hfv i x]
        exact congrArg Subtype.val ((e i).apply_symm_apply ⟨y, hy⟩)
  have himage' (i : Fin 4) :
      ∃ C : SimplicialComplex ℝ (ℝ × ℝ), C.faces.Finite ∧
        C.space = stripRegion L d i := by
    obtain ⟨C, hC, hCs⟩ := (hf i).exists_finite_triangulation_image
    exact ⟨C, hC, hCs.trans (himage i)⟩
  choose C hC hCs using himage'
  obtain ⟨K₀, hK₀, hK₀s, _⟩ :=
    Geometry.SimplicialComplex.exists_finite_triangulation_iUnion C hC
  have hCK : ∀ i, (C i).space ⊆ K₀.space := by
    intro i
    rw [hK₀s]
    exact subset_iUnion (fun j => (C j).space) i
  obtain ⟨R, D, hR, _, hD⟩ :=
    K₀.exists_subdivision_with_finite_full_polyhedra hK₀ C hC hCK
  have hcommon {C₁ C₂ : SimplicialComplex ℝ (ℝ × ℝ)}
      (hC₁ : C₁ ≤ R) (hC₂ : C₂ ≤ R) {s t : Finset (ℝ × ℝ)}
      (hs : s ∈ C₁.faces) (ht : t ∈ C₂.faces) :
      convexHull ℝ (s : Set (ℝ × ℝ)) ∩ convexHull ℝ (t : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ((s : Set (ℝ × ℝ)) ∩ t) := by
    exact R.inter_subset_convexHull (hC₁ hs) (hC₂ ht)
  let A : Fin 2 → SimplicialComplex ℝ (ℝ × ℝ) := ![D 0, D 1]
  have hAcompat : ∀ i j, ∀ s ∈ (A i).faces, ∀ t ∈ (A j).faces,
      convexHull ℝ (s : Set (ℝ × ℝ)) ∩ convexHull ℝ (t : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ((s : Set (ℝ × ℝ)) ∩ t) := by
    intro i j s hs t ht
    fin_cases i <;> fin_cases j <;>
      exact hcommon (hD _).1 (hD _).1 hs ht
  let B : Fin 2 → SimplicialComplex ℝ (ℝ × ℝ) := ![D 2, D 3]
  have hBcompat : ∀ i j, ∀ s ∈ (B i).faces, ∀ t ∈ (B j).faces,
      convexHull ℝ (s : Set (ℝ × ℝ)) ∩ convexHull ℝ (t : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ((s : Set (ℝ × ℝ)) ∩ t) := by
    intro i j s hs t ht
    fin_cases i <;> fin_cases j <;>
      exact hcommon (hD _).1 (hD _).1 hs ht
  let C' : Fin 2 → SimplicialComplex ℝ (ℝ × ℝ) :=
    ![D 0 ⊓ D 3, D 1 ⊓ D 2]
  have hC'compat : ∀ i j, ∀ s ∈ (C' i).faces, ∀ t ∈ (C' j).faces,
      convexHull ℝ (s : Set (ℝ × ℝ)) ∩ convexHull ℝ (t : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ((s : Set (ℝ × ℝ)) ∩ t) := by
    intro i j s hs t ht
    fin_cases i <;> fin_cases j <;>
      exact hcommon (le_trans inf_le_left (hD _).1)
        (le_trans inf_le_left (hD _).1) hs ht
  let U₀₁ := iUnionOfCompatible A hAcompat
  let U₂₃ := iUnionOfCompatible B hBcompat
  let W := iUnionOfCompatible C' hC'compat
  have hU₀₁R : U₀₁ ≤ R := by
    intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    fin_cases i
    · exact (hD 0).1 hi
    · exact (hD 1).1 hi
  have hU₂₃R : U₂₃ ≤ R := by
    intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    fin_cases i
    · exact (hD 2).1 hi
    · exact (hD 3).1 hi
  let E : Fin 2 → SimplicialComplex ℝ (ℝ × ℝ) := ![U₀₁, U₂₃]
  have hEcompat : ∀ i j, ∀ s ∈ (E i).faces, ∀ t ∈ (E j).faces,
      convexHull ℝ (s : Set (ℝ × ℝ)) ∩ convexHull ℝ (t : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ((s : Set (ℝ × ℝ)) ∩ t) := by
    intro i j s hs t ht
    fin_cases i <;> fin_cases j
    · exact hcommon hU₀₁R hU₀₁R hs ht
    · exact hcommon hU₀₁R hU₂₃R hs ht
    · exact hcommon hU₂₃R hU₀₁R hs ht
    · exact hcommon hU₂₃R hU₂₃R hs ht
  let K := iUnionOfCompatible E hEcompat
  have hRfinite : R.faces.Finite := hR
  have hDdata (i : Fin 4) : (D i).faces.Finite ∧
      (D i).space = stripRegion L d i ∧ D i ≤ R := by
    exact ⟨hR.subset (hD i).1, (hD i).2.1.trans (hCs i), (hD i).1⟩
  refine ⟨R, D, U₀₁, U₂₃, W, K, hRfinite, hDdata, ?_, ?_, ?_, ?_, ?_⟩
  · ext s
    simp [U₀₁, A, faces_iUnionOfCompatible, Fin.exists_fin_succ]
  · ext s
    simp [U₂₃, B, faces_iUnionOfCompatible, Fin.exists_fin_succ]
  · ext s
    simp [W, C', faces_iUnionOfCompatible, Fin.exists_fin_succ]
  · ext s
    simp [K, E, faces_iUnionOfCompatible, Fin.exists_fin_succ]
  · have hspace : K.space = ⋃ i : Fin 4, (D i).space := by
      ext x
      simp [K, E, U₀₁, U₂₃, A, B, space_iUnionOfCompatible,
        Fin.exists_fin_succ, or_assoc]
    rw [hspace]
    simp only [(hDdata _).2.1]
    ext x
    simpa [stripRegion, Fin.exists_fin_succ, or_assoc] using
      Set.ext_iff.mp (union_four_strips (L := L) (d := d) hd.le hwidth') x

end PLAnnularStrip
