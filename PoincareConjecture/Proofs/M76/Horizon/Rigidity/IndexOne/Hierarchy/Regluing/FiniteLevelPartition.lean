import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus




theorem exists_finite_three_level_cover
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {S : Set V} {t : V → ℝ} (ht : FinitePiecewiseAffineOn t S)
    {a b : ℝ} (_hab : a ≤ b) :
    ∃ J : Set (SimplicialComplex ℝ V), J.Finite ∧
      (∀ K ∈ J, K.faces.Finite ∧ K.space ⊆ S ∧
        (MapsTo t K.space (Iic a) ∨ MapsTo t K.space (Icc a b) ∨ MapsTo t K.space (Ici b))) ∧
      S ⊆ ⋃ K ∈ J, K.space := by
  classical
  obtain ⟨K, hK, hKS, htK⟩ := ht
  let : Finite K.faces := hK.to_subtype
  have hface (s : K.faces) : ∃ C : SimplicialComplex ℝ V,
      C.faces.Finite ∧ C.space = convexHull ℝ (s.val : Set V) := by
    obtain ⟨C, hC, hCs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
      (fun _ : Unit => s.val) (fun _ => K.indep s.property)
    exact ⟨C, hC, hCs.trans (by simp only [iUnion_const])⟩
  choose C hC hCs using hface
  choose ell hell using fun s : K.faces => htK s.val s.property
  let ca : V →ᵃ[ℝ] ℝ := AffineMap.const ℝ V a
  let cb : V →ᵃ[ℝ] ℝ := AffineMap.const ℝ V b
  let halfspaces (s : K.faces) (i : Fin 3) : Finset (V →ᵃ[ℝ] ℝ) :=
    if i = 0 then {ell s - ca} else if i = 1 then {ca - ell s, ell s - cb}
      else {cb - ell s}
  have hpieces (s : K.faces) (i : Fin 3) : ∃ P : SimplicialComplex ℝ V,
      P.faces.Finite ∧ P.space = (C s).space ∩ {x | ∀ A ∈ halfspaces s i, A x ≤ 0} :=
    (C s).exists_finite_triangulation_inter_halfspaces (hC s) (halfspaces s i)
  choose P hP hPs using hpieces
  have hsubset (s : K.faces) (i : Fin 3) : (P s i).space ⊆ S := by
    intro x hx
    exact hKS.subset (K.convexHull_subset_space s.property
      ((hCs s).subset ((hPs s i).subset hx).1))
  have hlevel (s : K.faces) (i : Fin 3) (x : V) : x ∈ (P s i).space ↔
      x ∈ convexHull ℝ (s.val : Set V) ∧
        (if i = 0 then t x ≤ a else if i = 1 then a ≤ t x ∧ t x ≤ b else b ≤ t x) := by
    rw [hPs, hCs]
    constructor
    · rintro ⟨hx, hh⟩
      have hv : ell s x = t x := (hell s hx).symm
      refine ⟨hx, ?_⟩
      fin_cases i <;> simpa [halfspaces, ca, cb, hv, sub_nonpos] using hh
    · rintro ⟨hx, hh⟩
      have hv : ell s x = t x := (hell s hx).symm
      refine ⟨hx, ?_⟩
      fin_cases i <;> simpa [halfspaces, ca, cb, hv, sub_nonpos] using hh
  let J := range (fun si : K.faces × Fin 3 => P si.1 si.2)
  refine ⟨J, finite_range _, ?_, ?_⟩
  · rintro L ⟨⟨s, i⟩, rfl⟩
    refine ⟨hP s i, hsubset s i, ?_⟩
    fin_cases i
    · left
      intro x hx
      exact (hlevel s 0 x).mp hx |>.2
    · right; left
      intro x hx
      exact (hlevel s 1 x).mp hx |>.2
    · right; right
      intro x hx
      exact (hlevel s 2 x).mp hx |>.2
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp (hKS.symm.subset hx)
    let s' : K.faces := ⟨s, hs⟩
    have hchoose : ∃ i : Fin 3, x ∈ (P s' i).space := by
      by_cases hlow : t x ≤ a
      · exact ⟨0, (hlevel s' 0 x).mpr ⟨hxs, hlow⟩⟩
      · by_cases hhigh : b ≤ t x
        · exact ⟨2, (hlevel s' 2 x).mpr ⟨hxs, hhigh⟩⟩
        · exact ⟨1, (hlevel s' 1 x).mpr ⟨hxs, (not_le.mp hlow).le, (not_le.mp hhigh).le⟩⟩
    obtain ⟨i, hi⟩ := hchoose
    exact mem_iUnion.mpr ⟨P s' i, mem_iUnion.mpr ⟨⟨(s', i), rfl⟩, hi⟩⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
