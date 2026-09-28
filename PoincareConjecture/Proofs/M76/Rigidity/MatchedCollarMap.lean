import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing









set_option autoImplicit false

open Set

namespace Geometry

variable {E F X : Type*}




noncomputable def matchedCollarMap (Q : E → F) (c : E × ℝ → X) (d : F × ℝ → X) :
    E × ℝ → X := fun z => if 0 ≤ z.2 then c z else d (Q z.1, -z.2)



theorem matchedCollarMap_nonneg (Q : E → F) (c : E × ℝ → X) (d : F × ℝ → X)
    {z : E × ℝ} (ht : 0 ≤ z.2) : matchedCollarMap Q c d z = c z := by
  simp only [matchedCollarMap, if_pos ht]



theorem matchedCollarMap_nonpos (Q : E → F) (c : E × ℝ → X) (d : F × ℝ → X)
    {L : Set E} (hzero : ∀ x ∈ L, c (x, 0) = d (Q x, 0))
    {z : E × ℝ} (hz : z.1 ∈ L) (ht : z.2 ≤ 0) :
    matchedCollarMap Q c d z = d (Q z.1, -z.2) := by
  by_cases hpos : 0 ≤ z.2
  · have htime : z.2 = 0 := le_antisymm ht hpos
    have heq : z = (z.1, 0) := Prod.ext rfl htime
    rw [heq, matchedCollarMap_nonneg Q c d le_rfl, neg_zero]
    exact hzero z.1 hz
  · simp only [matchedCollarMap, if_neg hpos]

variable {ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}




theorem PolyhedralPLInCharts.comp_negative_base_product
    {L : Set E} {K : Set F} {Q : E → F} {d : F × ℝ → X}
    (hd : PolyhedralPLInCharts e d (K ×ˢ Icc (0 : ℝ) 1))
    (hQ : FinitePiecewiseAffineOn Q L) (hQmap : MapsTo Q L K) :
    PolyhedralPLInCharts e (fun z => d (Q z.1, -z.2)) (L ×ˢ Icc (-1 : ℝ) 0) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (-1 : ℝ) < 0 by norm_num)
  let A : ℝ →ᴬ[ℝ] ℝ := -(ContinuousAffineMap.id ℝ ℝ)
  have hA : FinitePiecewiseAffineOn (fun t : ℝ => -t) (Icc (-1 : ℝ) 0) :=
    ⟨J, hJ, hJI, J.affineOnFaces_affine A⟩
  obtain ⟨P, hP, hPs, hPa⟩ := hQ.prodMap hA
  have hmap : MapsTo (Prod.map Q (fun t : ℝ => -t)) P.space
      (K ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz
    have h := hPs.subset hz
    exact ⟨hQmap h.1, by dsimp; linarith [h.2.2], by dsimp; linarith [h.2.1]⟩
  have h := hd.comp_finitePiecewiseAffineOn P hP ⟨P, hP, rfl, hPa⟩ hmap
  exact hPs ▸ h




theorem polyhedral_matchedCollarMap
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    {K : Set F} {Q : E → F} {c : E × ℝ → X} {d : F × ℝ → X}
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (0 : ℝ) 1))
    (hd : PolyhedralPLInCharts e d (K ×ˢ Icc (0 : ℝ) 1))
    (hQ : FinitePiecewiseAffineOn Q L.space) (hQmap : MapsTo Q L.space K)
    (hzero : ∀ x ∈ L.space, c (x, 0) = d (Q x, 0)) :
    PolyhedralPLInCharts e (matchedCollarMap Q c d) (L.space ×ˢ Icc (-1 : ℝ) 1) := by
  have hplus : PolyhedralPLInCharts e (matchedCollarMap Q c d)
      (L.space ×ˢ Icc (0 : ℝ) 1) :=
    hc.congr (fun z hz => (matchedCollarMap_nonneg Q c d hz.2.1).symm)
  have hminus : PolyhedralPLInCharts e (matchedCollarMap Q c d)
      (L.space ×ˢ Icc (-1 : ℝ) 0) :=
    (hd.comp_negative_base_product hQ hQmap).congr
      (fun z hz => (matchedCollarMap_nonpos Q c d hzero hz.1 hz.2.2).symm)
  have hclosed : IsClosed L.space := (L.isCompact_space_of_finite hL).isClosed
  have hcont : ContinuousOn (matchedCollarMap Q c d) (L.space ×ˢ Icc (-1 : ℝ) 1) := by
    apply (hminus.continuousOn.union_of_isClosed hplus.continuousOn
      (hclosed.prod isClosed_Icc) (hclosed.prod isClosed_Icc)).mono
    intro z hz
    by_cases ht : z.2 ≤ 0
    · exact Or.inl ⟨hz.1, hz.2.1, ht⟩
    · exact Or.inr ⟨hz.1, (not_le.mp ht).le, hz.2.2⟩
  obtain ⟨P, hP, hPs⟩ := L.exists_finite_interval_product hL
    (show (-1 : ℝ) < 1 by norm_num)
  obtain ⟨N, hN, hNs⟩ := L.exists_finite_interval_product hL
    (show (-1 : ℝ) < 0 by norm_num)
  obtain ⟨J, hJ, hJs⟩ := L.exists_finite_interval_product hL
    (show (0 : ℝ) < 1 by norm_num)
  let pieces : Bool → SimplicialComplex ℝ (E × ℝ)
    | false => N
    | true => J
  have hfinite (b : Bool) : (pieces b).faces.Finite := by
    cases b <;> assumption
  have hPL (b : Bool) : PolyhedralPLInCharts e (matchedCollarMap Q c d) (pieces b).space := by
    cases b
    · exact hNs.symm ▸ hminus
    · exact hJs.symm ▸ hplus
  have hcoverage : P.space ⊆ ⋃ b, (pieces b).space := by
    intro z hz
    have h := hPs.subset hz
    by_cases ht : z.2 ≤ 0
    · exact mem_iUnion.mpr ⟨false, hNs.symm.subset ⟨h.1, h.2.1, ht⟩⟩
    · exact mem_iUnion.mpr ⟨true, hJs.symm.subset ⟨h.1, (not_le.mp ht).le, h.2.2⟩⟩
  have h := polyhedralPLInCharts_of_finite_cover hcover hcompat P hP pieces hfinite
    (hPs.symm ▸ hcont) hPL hcoverage
  exact hPs ▸ h

end Geometry
