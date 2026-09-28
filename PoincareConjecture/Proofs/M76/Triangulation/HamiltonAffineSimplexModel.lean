import PoincareConjecture.Proofs.M76.Mathlib.ConvexCubeNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.SimplexRelativeInteriorCoordinates
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76





theorem exists_affine_simplex_cube_model
    (s : Finset (Fin 3 → ℝ)) (hs : s.Nonempty)
    (hindep : AffineIndependent ℝ ((↑) : s → (Fin 3 → ℝ))) :
    ∃ (J : Finset (Fin 3))
      (Phi : ((J → ℝ) × ({i : Fin 3 // i ∉ J} → ℝ)) ≃ᴬ[ℝ] (Fin 3 → ℝ))
      (D : Set (J → ℝ)) (h : closedBall (0 : J → ℝ) 1 ≃ₜ D),
      J.card + 1 = s.card ∧
      IsCompact D ∧ Convex ℝ D ∧ (interior D).Nonempty ∧ h.IsFinitePL ∧
      Phi '' (D ×ˢ ({0} : Set ({i : Fin 3 // i ∉ J} → ℝ))) =
        convexHull ℝ (s : Set (Fin 3 → ℝ)) ∧
      (∀ x : J → ℝ, Phi (x, 0) ∈
        intrinsicInterior ℝ (convexHull ℝ (s : Set (Fin 3 → ℝ))) ↔ x ∈ interior D) ∧
      ∀ x : closedBall (0 : J → ℝ) 1,
        Phi ((h x : J → ℝ), 0) ∈
          intrinsicFrontier ℝ (convexHull ℝ (s : Set (Fin 3 → ℝ))) ↔ ‖(x : J → ℝ)‖ = 1 := by
  classical
  let : Nonempty s := hs.to_subtype
  let A := affineSpan ℝ (s : Set (Fin 3 → ℝ))
  let L := A.direction
  have hLcard : Module.finrank ℝ L + 1 = s.card := by
    change Module.finrank ℝ (affineSpan ℝ (s : Set (Fin 3 → ℝ))).direction + 1 = s.card
    rw [direction_affineSpan]
    have h := hindep.finrank_vectorSpan_add_one
    have hrange : range ((↑) : s → (Fin 3 → ℝ)) = (s : Set (Fin 3 → ℝ)) := by
      ext x
      simp
    rw [hrange, Fintype.card_coe] at h
    exact h
  have hLle : Module.finrank ℝ L ≤ 3 := by
    simpa using (Submodule.finrank_le L)
  obtain ⟨J, _, hJ⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin 3))) (by simpa using hLle)
  let T := J → ℝ
  let N := {i : Fin 3 // i ∉ J} → ℝ
  obtain ⟨W, hLW⟩ := Submodule.exists_isCompl L
  have hW : Module.finrank ℝ W = 3 - J.card := by
    have h := Submodule.finrank_add_eq_of_isCompl hLW
    have hdim : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
    omega
  let eL : T ≃ₗ[ℝ] L := LinearEquiv.ofFinrankEq _ _ (by simp [T, hJ])
  let eW : N ≃ₗ[ℝ] W := LinearEquiv.ofFinrankEq _ _ (by
    simp [N, Fintype.card_subtype_compl, hW])
  let e := (eL.prodCongr eW).trans (L.prodEquivOfIsCompl W hLW)
  obtain ⟨p, hp⟩ := hs
  have hpA : p ∈ A := subset_affineSpan ℝ _ hp
  let Phi : (T × N) ≃ᴬ[ℝ] (Fin 3 → ℝ) :=
    e.toContinuousLinearEquiv.toContinuousAffineEquiv.trans
      (ContinuousAffineEquiv.constVAdd ℝ (Fin 3 → ℝ) p)
  have hPhi (x : T × N) : Phi x = e x + p := add_comm _ _
  have hplane (x : T × N) : Phi x ∈ A ↔ x.2 = 0 := by
    have he : e x ∈ L ↔ x.2 = 0 := by
      have h := (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero L W hLW
        (x := e x)).symm
      simpa only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.prodCongr_apply, eW.map_eq_zero_iff] using h
    rw [hPhi]
    change e x +ᵥ p ∈ A ↔ x.2 = 0
    rw [A.vadd_mem_iff_mem_direction _ hpA]
    exact he
  let a : T →ᵃ[ℝ] (Fin 3 → ℝ) :=
    Phi.toAffineMap.comp (LinearMap.inl ℝ T N).toAffineMap
  let v : s → T := fun y => (Phi.symm y).1
  have hvback (y : s) : a (v y) = y := by
    have hy : (Phi.symm y).2 = 0 := (hplane _).mp (by
      rw [Phi.apply_symm_apply]
      exact subset_affineSpan ℝ _ y.property)
    have heq : (v y, (0 : N)) = Phi.symm y := Prod.ext rfl hy.symm
    change Phi (v y, 0) = y
    rw [heq, Phi.apply_symm_apply]
  have hvinj : AffineIndependent ℝ v := by
    apply AffineIndependent.of_comp a
    have heq : a ∘ v = ((↑) : s → (Fin 3 → ℝ)) := funext hvback
    rwa [heq]
  have ha : Function.Injective a := by
    intro x y hxy
    exact congrArg Prod.fst (Phi.injective hxy)
  let D : Set T := convexHull ℝ (range v)
  have hD : IsCompact D := (finite_range v).isCompact_convexHull ℝ
  have hDcv : Convex ℝ D := convex_convexHull ℝ _
  have hvspan : affineSpan ℝ (range v) = ⊤ :=
    hvinj.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simp only [Fintype.card_coe]
      simpa [T, hJ] using hLcard.symm)
  have hDne : (interior D).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hvspan
  let basis : AffineBasis s ℝ T := ⟨v, hvinj, hvspan⟩
  have hDint : intrinsicInterior ℝ D = interior D := by
    apply Subset.antisymm
    · intro x hx
      exact basis.mem_interior_convexHull_of_mem_intrinsicInterior hx
    · exact interior_subset_intrinsicInterior
  have hDclosure : intrinsicClosure ℝ D = D :=
    (hD.isClosed.preimage continuous_subtype_val).intrinsicClosure
  have hDfront : intrinsicFrontier ℝ D = frontier D := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior (𝕜 := ℝ) D,
      hDclosure, hDint, hD.isClosed.frontier_eq]
  have haimage : a '' D = convexHull ℝ (s : Set (Fin 3 → ℝ)) := by
    rw [show D = convexHull ℝ (range v) from rfl, a.image_convexHull]
    congr 1
    rw [← range_comp, show a ∘ v = ((↑) : s → (Fin 3 → ℝ)) from funext hvback,
      Subtype.range_coe]
  have hcarrier : Phi '' (D ×ˢ ({0} : Set N)) =
      convexHull ℝ (s : Set (Fin 3 → ℝ)) := by
    rw [← haimage]
    ext y
    constructor
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
      simp only [mem_singleton_iff] at hz
      subst z
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
  have hinterior (x : T) : Phi (x, 0) ∈
      intrinsicInterior ℝ (convexHull ℝ (s : Set (Fin 3 → ℝ))) ↔ x ∈ interior D := by
    rw [← hcarrier, Phi.intrinsicInterior_image, intrinsicInterior_prod_eq,
      hDint, intrinsicInterior_singleton]
    simpa only [mem_prod, mem_singleton_iff, and_true] using
      (Phi.injective.mem_set_image (s := interior D ×ˢ ({0} : Set N))
        (a := (x, 0)))
  have hfrontier (x : T) : Phi (x, 0) ∈
      intrinsicFrontier ℝ (convexHull ℝ (s : Set (Fin 3 → ℝ))) ↔ x ∈ frontier D := by
    rw [← haimage, a.intrinsicFrontier_image_of_injOn D ha.injOn, hDfront]
    exact ha.mem_set_image
  let sv : Finset T := Finset.univ.image v
  have hsv : (sv : Set T) = range v := by simp [sv]
  have hsvindep : AffineIndependent ℝ ((↑) : sv → T) := by
    change AffineIndependent ℝ ((↑) : ↥(sv : Set T) → T)
    rw [hsv]
    exact hvinj.range
  obtain ⟨K, hK, hKD, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
      (fun _ : Unit => sv) (fun _ => hsvindep)
  have hKD' : K.space = D := by simpa only [iUnion_const, hsv] using hKD
  obtain ⟨h, hh, hhfront⟩ :
      ∃ h : closedBall (0 : T) 1 ≃ₜ D, h.IsFinitePL ∧
        ∀ x : closedBall (0 : T) 1, (h x : T) ∈ frontier D ↔ ‖(x : T)‖ = 1 := by
    rcases isEmpty_or_nonempty J with hJempty | hJnonempty
    · have hzero (x : T) : x = 0 := Subsingleton.elim _ _
      have hDuniv : D = univ := by
        obtain ⟨x, hx⟩ := hDne
        exact eq_univ_of_forall fun y => (Subsingleton.elim x y) ▸ interior_subset hx
      have hball : closedBall (0 : T) 1 = D := by
        ext x
        simp only [hDuniv, mem_univ, iff_true, mem_closedBall_zero_iff, hzero x, norm_zero]
        norm_num
      let h : closedBall (0 : T) 1 ≃ₜ D := Homeomorph.setCongr hball
      refine ⟨h, Homeomorph.isFinitePL_setCongr hball K hK (hKD'.trans hball.symm), ?_⟩
      intro x
      simp only [hDuniv, frontier_univ, mem_empty_iff_false, hzero (x : T), norm_zero]
      norm_num
    · obtain ⟨g, hg, hgfront⟩ := hD.exists_finitePL_cube_homeomorph hDcv hDne
        K hK hKD' (ContinuousLinearEquiv.refl ℝ T)
      refine ⟨g.symm, hg.symm, fun x => ?_⟩
      have hx := hgfront (g.symm x)
      rw [g.apply_symm_apply, frontier_closedBall _ one_ne_zero,
        mem_sphere_zero_iff_norm] at hx
      exact hx
  refine ⟨J, Phi, D, h, by omega, hD, hDcv, hDne, hh, hcarrier, hinterior, ?_⟩
  intro x
  exact (hfrontier (h x)).trans (hhfront x)

end PoincareConjecture.M76
