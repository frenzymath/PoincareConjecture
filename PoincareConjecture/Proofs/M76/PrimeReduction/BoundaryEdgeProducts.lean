import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryTriangleFibers
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryEdgeDualMarks
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskIntervalHalfProduct

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K L : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype L.faces]

local notation "I" => Icc (0 : ℝ) 1

theorem BoundaryTriangleFibers.exists_edge_product (F : BoundaryTriangleFibers K L)
    (hLK : L ≤ K) (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    (hfull : ∀ t ∈ K.faces, (∀ p ∈ t, p ∈ L.vertices) → t ∈ L.faces)
    {s : Finset E} (hs : s ∈ L.faces) (hscard : s.card = 2)
    (hends : (L.faceLink s).vertices.ncard = 2)
    (hI : IsFinitePLBallPair ℝ (K.faceLink s).space (L.faceLink s).space) :
    ∃ g : E × ℝ → E,
      FinitePiecewiseAffineOn g ((L.barycentricDualBlock s).space ×ˢ I) ∧
      InjOn g ((L.barycentricDualBlock s).space ×ˢ I) ∧
      g '' ((L.barycentricDualBlock s).space ×ˢ I) = (K.barycentricDualBlock s).space ∧
      (∀ x ∈ (L.barycentricDualBlock s).space, g (x, 0) = x) ∧
      (∀ t ∈ L.faces, s ⊆ t → t.card = 3 → ∀ r ∈ I,
        g (t.centroid ℝ id, r) = F.map t r) ∧
      (∀ x ∈ (L.barycentricDualBlock s).space ×ˢ I, g x ∈ L.space ↔ x.2 = 0) ∧
      ∀ x ∈ (L.barycentricDualBlock s).space ×ˢ I,
        g x ∈ ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space ↔
          x.1 ∈ (L.barycentricDualBlock s).space ∩
            ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space ∨ x.2 = 1 := by
  classical
  obtain ⟨hN, hcontact, t, u, ht, hu, htc, huc, hst, hsu, htu, hcofaces,
    hB, hW, _, hBW, htB, huB, _, _, hdis⟩ :=
    K.exists_boundary_edge_dual_marks L hLK hLcard hfull hs hscard hends hI
  let W := (L.barycentricDualBlock s).space
  let N := (K.barycentricDualBlock s).space
  let B := ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space
  let a : Bool → E := Bool.rec (t.centroid ℝ id) (u.centroid ℝ id)
  let f : Bool → ℝ → E := Bool.rec (F.map t) (F.map u)
  have ha : a false ≠ a true := by
    intro he
    have he' : (⟨t, ht⟩ : L.faces) = ⟨u, hu⟩ := L.faceCentroid_injective he
    exact htu (congrArg Subtype.val he')
  have hN' : IsFinitePLBallPair (ℝ × ℝ) N (W ∪ B) := by
    simpa only [union_comm] using hN
  have hWB : W ∩ B = {a false, a true} := by
    simpa only [inter_comm] using hBW
  have hf (i : Bool) : FinitePiecewiseAffineOn (f i) I := by
    cases i
    · exact F.piecewiseAffine t ht htc
    · exact F.piecewiseAffine u hu huc
  have hi (i : Bool) : InjOn (f i) I := by
    cases i
    · exact F.injective t ht htc
    · exact F.injective u hu huc
  have h0 (i : Bool) : f i 0 = a i := by
    cases i
    · exact F.central t ht htc
    · exact F.central u hu huc
  have hmaps (i : Bool) : f i '' I ⊆ B := by
    cases i
    · change F.map t '' I ⊆ B
      rw [F.image_eq t ht htc]
      exact htB
    · change F.map u '' I ⊆ B
      rw [F.image_eq u hu huc]
      exact huB
  have hdis' : Disjoint (f false '' I) (f true '' I) := by
    change Disjoint (F.map t '' I) (F.map u '' I)
    rw [F.image_eq t ht htc, F.image_eq u hu huc]
    exact hdis
  obtain ⟨H, hH, hH0, hHf, hHB, hHW⟩ :=
    PoincareConjecture.M76.HamiltonIndexOne.exists_interval_half_product a hW ha hN' hB hWB
      zero_lt_one f hf hi h0 hmaps hdis'
  obtain ⟨g, hg, hval⟩ := hH
  have hgi : InjOn g (W ×ˢ I) := by
    intro x hx y hy he
    have he' : H ⟨x, hx⟩ = H ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (hval ⟨x, hx⟩).trans (he.trans (hval ⟨y, hy⟩).symm)
    exact congrArg Subtype.val (H.injective he')
  have him : g '' (W ×ˢ I) = N := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hval ⟨x, hx⟩) ▸ (H ⟨x, hx⟩).property
    · intro y hy
      let x := H.symm ⟨y, hy⟩
      refine ⟨x, x.property, ?_⟩
      exact (hval x).symm.trans (congrArg Subtype.val (H.apply_symm_apply ⟨y, hy⟩))
  have haW (i : Bool) : a i ∈ W := by
    apply hW.1
    cases i <;> simp [a]
  have hkeep (i : Bool) (r : ℝ) (hr : r ∈ I) : g (a i, r) = f i r :=
    (hval ⟨(a i, r), haW i, hr⟩).symm.trans (hHf i ⟨r, hr⟩)
  have hphysical (y : E) (hy : y ∈ N) : y ∈ L.space ↔ y ∈ W :=
    ⟨fun h => hcontact.subset ⟨hy, h⟩, fun h => (hcontact.symm.subset h).2⟩
  refine ⟨g, hg, hgi, him, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hval ⟨(x, 0), hx, le_rfl, zero_le_one⟩).symm.trans (hH0 ⟨x, hx⟩)
  · intro v hv hsv hvc r hr
    rcases hcofaces v hv hsv hvc with rfl | rfl
    · exact hkeep false r hr
    · exact hkeep true r hr
  · intro x hx
    rw [← hval ⟨x, hx⟩]
    exact (hphysical _ (H ⟨x, hx⟩).property).trans (hHW ⟨x, hx⟩)
  · intro x hx
    change g x ∈ B ↔ x.1 ∈ W ∩ B ∨ x.2 = 1
    rw [← hval ⟨x, hx⟩, hWB]
    exact hHB ⟨x, hx⟩

end Geometry.SimplicialComplex
