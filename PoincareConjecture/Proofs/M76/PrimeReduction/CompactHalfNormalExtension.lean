import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set Geometry

namespace Set

private theorem finite_identity_of_ball
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s b : Set X} (hs : IsFinitePLBallPair V s b) :
    FinitePiecewiseAffineOn (id : X → X) s := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hs
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ X)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_compact_half_normal_extension
    {s q : Set E} (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (e : s ≃ₜ s) (he : e.IsFinitePL)
    (hfix : ∀ x : s, (x : E) ∈ q → e x = x) :
    ∃ H : (s ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)) ≃ₜ (s ×ˢ Icc (0 : ℝ) 1),
      H.IsFinitePL ∧
      (∀ x : s, (H ⟨((x : E), 0), x.property, le_rfl, zero_le_one⟩ : E × ℝ) =
        ((e x : E), 0)) ∧
      (∀ x : (s ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)),
        (x : E × ℝ).1 ∈ q ∨ (x : E × ℝ).2 = 1 → H x = x) ∧
      ∀ x : (s ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)),
        (H x : E × ℝ).2 = 0 ↔ (x : E × ℝ).2 = 0 := by
  let B : Set (E × ℝ) := s ×ˢ {(0 : ℝ)}
  let T : Set (E × ℝ) := (q ×ˢ Icc (0 : ℝ) 1) ∪ (s ×ˢ {(1 : ℝ)})
  have hsId := finite_identity_of_ball hs
  obtain ⟨K, hK, hKs, _⟩ := hsId
  let j : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hj : FinitePiecewiseAffineOn j s :=
    ⟨K, hK, hKs, K.affineOnFaces_affine j⟩
  have hji : InjOn j s := fun _ _ _ _ h => congrArg Prod.fst h
  have hjimage : j '' s = B := (Set.prod_singleton (s := s) (b := (0 : ℝ))).symm
  have hjex := hj.exists_homeomorph_image hji
  rw [hjimage] at hjex
  obtain ⟨J, hJ, hJval⟩ := hjex
  have hJinv (x : B) : J.symm x = ⟨(x : E × ℝ).1, x.property.1⟩ := by
    apply J.injective
    rw [J.apply_symm_apply]
    apply Subtype.ext
    rw [hJval]
    exact Prod.ext rfl x.property.2
  let eb : B ≃ₜ B := J.symm.trans (e.trans J)
  have heb : eb.IsFinitePL := hJ.symm.trans (he.trans hJ)
  have hebval (x : B) : (eb x : E × ℝ) =
      ((e ⟨(x : E × ℝ).1, x.property.1⟩ : E), 0) := by
    change (J (e (J.symm x)) : E × ℝ) = _
    rw [hJinv, hJval]
    rfl
  obtain ⟨n, P, _, hP, hPq⟩ := hs.exists_polygon_boundary
  have hqId : FinitePiecewiseAffineOn (id : E → E) q := by
    refine ⟨P.simplicialComplex hP, P.finite_simplicialComplex_faces hP,
      (P.simplicialComplex_space hP).trans hPq, ?_⟩
    exact (P.simplicialComplex hP).affineOnFaces_affine (ContinuousAffineMap.id ℝ E)
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  have hsideId : FinitePiecewiseAffineOn (id : E × ℝ → E × ℝ)
      (q ×ˢ Icc (0 : ℝ) 1) :=
    (hqId.prodMap (finite_identity_of_ball hI)).congr (fun _ _ => rfl)
  have hTId : (Homeomorph.refl T).IsFinitePL :=
    ⟨id, finitePiecewiseAffineOn_union hsideId
      (finite_identity_of_ball (hs.prod_singleton (1 : ℝ))), fun _ => rfl⟩
  have hBT (x : B) : (x : E × ℝ) ∈ T ↔ (x : E × ℝ).1 ∈ q := by
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact False.elim (zero_ne_one (x.property.2.symm.trans hx.2))
    · intro hx
      refine Or.inl ⟨hx, ?_⟩
      rw [show (x : E × ℝ).2 = 0 from x.property.2]
      exact ⟨le_rfl, zero_le_one⟩
  have heqmem (x : s) : (x : E) ∈ q ↔ (e x : E) ∈ q := by
    constructor
    · intro hx
      rw [hfix x hx]
      exact hx
    · intro hx
      have hh : e (e x) = e x := hfix (e x) hx
      have hexx : e x = x := e.injective hh
      rwa [hexx] at hx
  have hoverlap (x : B) : (x : E × ℝ) ∈ T ↔ (eb x : E × ℝ) ∈ T := by
    rw [hBT x, hBT (eb x), hebval]
    exact heqmem ⟨(x : E × ℝ).1, x.property.1⟩
  have hagree (x : E × ℝ) (hxB : x ∈ B) (hxT : x ∈ T) :
      (eb ⟨x, hxB⟩ : E × ℝ) = (Homeomorph.refl T) ⟨x, hxT⟩ := by
    rw [hebval, hfix _ ((hBT ⟨x, hxB⟩).mp hxT)]
    exact Prod.ext rfl hxB.2.symm
  obtain ⟨G, hG, hGB, hGT⟩ := Homeomorph.exists_union_finitePL
    eb (Homeomorph.refl T) heb hTId hoverlap hagree
  have hboundary : (q ×ˢ Icc (0 : ℝ) 1) ∪ (s ×ˢ ({0, 1} : Set ℝ)) = B ∪ T := by
    ext x
    simp only [B, T, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  have hball : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (s ×ˢ Icc (0 : ℝ) 1) (B ∪ T) := by
    rw [← hboundary]
    exact hs.prod hI
  obtain ⟨H, hH, hkeep, _⟩ := hball.exists_extension hball G hG
  have hHB (x : B) : H ⟨x, hball.1 (Or.inl x.property)⟩ =
      ⟨eb x, hball.1 (Or.inl (eb x).property)⟩ := by
    apply Subtype.ext
    exact (congrArg Subtype.val (hkeep ⟨x, Or.inl x.property⟩)).trans (hGB x)
  have hHT (x : T) : H ⟨x, hball.1 (Or.inr x.property)⟩ =
      ⟨x, hball.1 (Or.inr x.property)⟩ := by
    apply Subtype.ext
    exact (congrArg Subtype.val (hkeep ⟨x, Or.inr x.property⟩)).trans (hGT x)
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · intro x
    exact (congrArg Subtype.val (hHB ⟨((x : E), 0), x.property, rfl⟩)).trans
      (hebval ⟨((x : E), 0), x.property, rfl⟩)
  · intro x hx
    apply hHT ⟨x, ?_⟩
    exact hx.elim (fun h => Or.inl ⟨h, x.property.2⟩)
      (fun h => Or.inr ⟨x.property.1, h⟩)
  · intro x
    have hm := H.mem_subset_iff_of_extension eb
      (fun _ hx => hball.1 (Or.inl hx)) (fun _ hx => hball.1 (Or.inl hx)) hHB x
    simpa only [B, mem_prod, mem_singleton_iff, x.property.1,
      (H x).property.1, true_and] using hm.symm

end Set
