import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalSphereChartCarrier
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.CommonSubcomplexUnion









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem exists_finite_sphere_system_chart_carrier
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) :
    ∃ P : SimplicialComplex ℝ V3, P.faces.Finite ∧
      P.space = Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space ∧
      (∀ a ∈ P.faces, a.card ≤ 3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ ⋃ i, S i ↔ x ∈ P.space) ∧
      ∃ Pi : κ → SimplicialComplex ℝ V3,
        (∀ i, (Pi i).faces.Finite ∧
          (Pi i).space = Q '' (S i ∩ Q.source) ∩ J.space ∧
          (∀ a ∈ (Pi i).faces, a.card ≤ 3) ∧
          (∀ x ∈ J.space, Q.symm x ∈ S i ↔ x ∈ (Pi i).space) ∧ Pi i ≤ P) ∧
        (Pairwise fun i j => Disjoint (Pi i).space (Pi j).space) ∧
        P.faces = ⋃ i, (Pi i).faces ∧ P.space = ⋃ i, (Pi i).space := by
  classical
  choose Pi hPi hPis hPic hPilocal using
    fun i => (sS i).exists_finite_chart_carrier Q hQ J hJ hJQ
  have hPiJ (i : κ) : (Pi i).space ⊆ J.space :=
    (hPis i).subset.trans inter_subset_right
  have hPidis : Pairwise fun i j => Disjoint (Pi i).space (Pi j).space := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    exact disjoint_left.mp (hdisjoint hij)
      ((hPilocal i x (hPiJ i hxi)).mpr hxi)
      ((hPilocal j x (hPiJ j hxj)).mpr hxj)
  have hcross : ∀ i j, ∀ s ∈ (Pi i).faces, ∀ t ∈ (Pi j).faces,
      convexHull ℝ (s : Set V3) ∩ convexHull ℝ (t : Set V3) ⊆
        convexHull ℝ ((s : Set V3) ∩ t) := by
    intro i j s hs t ht
    by_cases hij : i = j
    · subst j
      exact (Pi i).inter_subset_convexHull hs ht
    · rintro x ⟨hxs, hxt⟩
      exact (disjoint_left.mp (hPidis hij)
        ((Pi i).convexHull_subset_space hs hxs)
        ((Pi j).convexHull_subset_space ht hxt)).elim
  let P := SimplicialComplex.iUnionOfCompatible Pi hcross
  have hPspace : P.space = ⋃ i, (Pi i).space :=
    SimplicialComplex.space_iUnionOfCompatible Pi hcross
  have hPfaces : P.faces = ⋃ i, (Pi i).faces := rfl
  have hwhole : P.space = Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space := by
    rw [hPspace]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨⟨y, ⟨hyS, hyQ⟩, rfl⟩, hyJ⟩ := (hPis i).subset hi
      exact ⟨⟨y, ⟨mem_iUnion.mpr ⟨i, hyS⟩, hyQ⟩, rfl⟩, hyJ⟩
    · rintro ⟨⟨y, ⟨hyS, hyQ⟩, rfl⟩, hyJ⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hyS
      exact mem_iUnion.mpr ⟨i, (hPis i).symm.subset ⟨⟨y, ⟨hi, hyQ⟩, rfl⟩, hyJ⟩⟩
  refine ⟨P, SimplicialComplex.finite_faces_iUnionOfCompatible Pi hcross hPi,
    hwhole, ?_, ?_, Pi, ?_, hPidis, hPfaces, hPspace⟩
  · intro a ha
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hPfaces.subset ha)
    exact hPic i a hi
  · intro x hx
    rw [hPspace, mem_iUnion, mem_iUnion]
    exact exists_congr (fun i => hPilocal i x hx)
  · intro i
    exact ⟨hPi i, hPis i, hPic i, hPilocal i,
      SimplicialComplex.le_iUnionOfCompatible Pi hcross i⟩

end PoincareConjecture.M76
