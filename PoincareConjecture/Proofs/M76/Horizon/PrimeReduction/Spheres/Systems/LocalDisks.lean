import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ChartCarrier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ClippedSphereDisks










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)

private theorem isOpen_on_finite_disjoint_union
    {E κ : Type*} [TopologicalSpace E] [Finite κ]
    (A : κ → Set E) (hclosed : ∀ i, IsClosed (A i))
    (hdisjoint : Pairwise fun i j => Disjoint (A i) (A j))
    {P D : Set E} (hP : P = ⋃ i, A i) (i : κ) (hD : D ⊆ A i)
    (hopen : IsOpen ((Subtype.val : A i → E) ⁻¹' D)) :
    IsOpen ((Subtype.val : P → E) ⁻¹' D) := by
  classical
  obtain ⟨O, hO, hOD⟩ := isOpen_induced_iff.mp hopen
  let bad : Set E := ⋃ j ∈ {j : κ | j ≠ i}, A j
  have hbad : IsClosed bad := (toFinite {j : κ | j ≠ i}).isClosed_biUnion
    (fun j _ => hclosed j)
  have hmem {x : E} (hx : x ∈ A i) : x ∈ O ↔ x ∈ D :=
    Set.ext_iff.mp hOD ⟨x, hx⟩
  have heq : (Subtype.val : P → E) ⁻¹' D =
      (Subtype.val : P → E) ⁻¹' (O ∩ badᶜ) := by
    ext x
    change (x : E) ∈ D ↔ (x : E) ∈ O ∩ badᶜ
    constructor
    · intro hx
      refine ⟨(hmem (hD hx)).mpr hx, ?_⟩
      intro hxbad
      obtain ⟨j, hji, hxj⟩ := mem_iUnion₂.mp hxbad
      exact disjoint_left.mp (hdisjoint (Ne.symm hji)) (hD hx) hxj
    · rintro ⟨hxO, hxnot⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp (hP.subset x.property)
      have hji : j = i := by
        by_contra hne
        exact hxnot (mem_iUnion₂.mpr ⟨j, hne, hxj⟩)
      exact (hmem (hji ▸ hxj)).mp hxO
  rw [heq]
  exact (hO.inter hbad.isOpen_compl).preimage continuous_subtype_val





theorem exists_finite_sphere_system_clipped_disk_neighborhood
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target)
    (hPs : P.space = Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space)
    {w : V3} (hw : w ∈ P.space) (hwJ : w ∈ interior J.space) :
    ∃ d q : Set V3, IsFinitePLBallPair V2 d q ∧ d ⊆ P.space ∧
      w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q)) := by
  obtain ⟨P₀, _, hP₀s, _, _, Pi, hPi, hPidis, _, hP₀union⟩ :=
    exists_finite_sphere_system_chart_carrier S sS hdisjoint Q hQ J hJ hJQ
  have hPunion : P.space = ⋃ i, (Pi i).space :=
    (hPs.trans hP₀s.symm).trans hP₀union
  obtain ⟨i, hwi⟩ := mem_iUnion.mp (hPunion.subset hw)
  obtain ⟨d, q, hd, hdi, hwd, hopen⟩ :=
    (sS i).exists_clipped_disk_neighborhood Q hQ J (Pi i) hJ hJQ
      (hPi i).1 (hPi i).2.1 hwi hwJ
  have hclosed (j : κ) : IsClosed (Pi j).space :=
    ((Pi j).isCompact_space_of_finite (hPi j).1).isClosed
  exact ⟨d, q, hd, hdi.trans ((subset_iUnion (fun j => (Pi j).space) i).trans
    hPunion.symm.subset), hwd,
    isOpen_on_finite_disjoint_union (fun j => (Pi j).space) hclosed hPidis
      hPunion i (sdiff_subset.trans hdi) hopen⟩

end PoincareConjecture.M76
