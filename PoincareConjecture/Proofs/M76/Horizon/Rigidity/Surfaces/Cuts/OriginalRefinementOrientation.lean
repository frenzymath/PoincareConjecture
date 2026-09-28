import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutCoherentSigns
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalOwnerIntersection

set_option autoImplicit false
open Set Geometry Classical
open AbstractSimplicialComplex PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem charted_refined_triangle_independent
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (F : (ℝ × ℝ) → E)
    (hF : L.AffineOnFaces F) {t : Finset (ℝ × ℝ)} (ht : t ∈ L.faces)
    (hi : InjOn F (convexHull ℝ (t : Set (ℝ × ℝ))))
    (R : E →ᴬ[ℝ] (ℝ × ℝ)) {T : Set E} (hRi : InjOn R T)
    (hmap : MapsTo F (convexHull ℝ (t : Set (ℝ × ℝ))) T)
    (p : Fin 3 → ℝ × ℝ) (hpi : Function.Injective p) (hpt : Finset.univ.image p = t) :
    AffineIndependent ℝ ((R ∘ F) ∘ p) := by
  let e : Fin 3 ↪ t := ⟨fun i ↦ ⟨p i, hpt ▸ Finset.mem_image.mpr
    ⟨i, Finset.mem_univ _, rfl⟩⟩, fun i j h ↦ hpi (congrArg Subtype.val h)⟩
  have hpind : AffineIndependent ℝ p := (L.indep ht).comp_embedding e
  have hpcontain : convexHull ℝ (range p) ⊆ convexHull ℝ (t : Set (ℝ × ℝ)) := by
    apply convexHull_mono
    rintro x ⟨i, rfl⟩
    exact hpt ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨a, ha⟩ := (hF.postcomp R) t ht
  have hai : InjOn a (convexHull ℝ (range p)) := by
    intro x hx y hy hxy
    exact hi (hpcontain hx) (hpcontain hy)
      (hRi (hmap (hpcontain hx)) (hmap (hpcontain hy))
        ((ha (hpcontain hx)).trans (hxy.trans (ha (hpcontain hy)).symm)))
  have hind := a.toAffineMap.affineIndependent_comp_of_injOn_convexHull hpind hai
  have he : a.toAffineMap ∘ p = (R ∘ F) ∘ p := by
    funext i
    exact (ha (hpcontain (subset_convexHull ℝ _ (mem_range_self i)))).symm
  rwa [he] at hind

private theorem parity_sum_of_negative_product (x y : ℝ) (h : x * y < 0) :
    orientationSignParity (SignType.sign x) + orientationSignParity (SignType.sign y) = 1 := by
  rcases mul_neg_iff.mp h with h | h
  · rw [sign_pos h.1, sign_neg h.2]
    norm_num [orientationSignParity]
  · rw [sign_neg h.1, sign_pos h.2]
    norm_num [orientationSignParity]

theorem charted_refined_cross_ne_zero
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (F : (ℝ × ℝ) → E)
    (hF : L.AffineOnFaces F) (a b x : ℝ × ℝ)
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x)
    (ht : {a, b, x} ∈ L.faces)
    (hi : InjOn F (convexHull ℝ ({a, b, x} : Set (ℝ × ℝ))))
    (R : E →ᴬ[ℝ] (ℝ × ℝ)) {T : Set E} (hRi : InjOn R T)
    (hmap : MapsTo F (convexHull ℝ ({a, b, x} : Set (ℝ × ℝ))) T) :
    planarCross (R (F b) - R (F a)) (R (F x) - R (F a)) ≠ 0 := by
  have hp : Function.Injective ![a, b, x] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have himage : Finset.univ.image ![a, b, x] = {a, b, x} := by
    ext z
    simp [Fin.exists_fin_succ, eq_comm]
  have hind := charted_refined_triangle_independent L F hF ht
    (by simpa only [Finset.coe_insert, Finset.coe_singleton] using hi) R hRi
    (by simpa only [Finset.coe_insert, Finset.coe_singleton] using hmap)
    ![a, b, x] hp himage
  exact planar_triangle_cross_ne_zero _ hind

theorem charted_refined_cofaces_cancel
    (K : SimplicialComplex ℝ E) (number : E → ℕ) (sourceSign : Finset E → ZMod 2)
    (charts : Finset E → E →ᴬ[ℝ] (ℝ × ℝ))
    (hcharts : ∀ T ∈ K.faces, T.card = 3 →
      InjOn (charts T) (convexHull ℝ (T : Set E)) ∧
      ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c →
        orientationSignParity (SignType.sign
          (planarCross (charts T b - charts T a) (charts T c - charts T a))) =
          Dehn.orderedCofaceParity number T a b)
    (hcancel : ∀ T ∈ K.faces, ∀ U ∈ K.faces, T.card = 3 → U.card = 3 → T ≠ U →
      ∀ a b : E, a ≠ b → {a, b} ⊆ T → {a, b} ⊆ U →
      (sourceSign T + boundaryFaceParity number T {a, b}) +
        (sourceSign U + boundaryFaceParity number U {a, b}) = 1)
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (F : (ℝ × ℝ) → E)
    (hF : L.AffineOnFaces F) (a b x y : ℝ × ℝ)
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (ht : {a, x, b} ∈ L.faces) (hu : {a, b, y} ∈ L.faces)
    (hi : InjOn F (convexHull ℝ ({a, x, b} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({a, b, y} : Set (ℝ × ℝ))))
    (T U : Finset E) (hTf : T ∈ K.faces) (hUf : U ∈ K.faces)
    (hTc : T.card = 3) (hUc : U.card = 3)
    (hT : MapsTo F (convexHull ℝ ({a, x, b} : Set (ℝ × ℝ)))
      (convexHull ℝ (T : Set E)))
    (hU : MapsTo F (convexHull ℝ ({a, b, y} : Set (ℝ × ℝ)))
      (convexHull ℝ (U : Set E))) :
    (sourceSign T + orientationSignParity (SignType.sign
      (planarCross (charts T (F b) - charts T (F a))
        (charts T (F x) - charts T (F a))))) +
    (sourceSign U + orientationSignParity (SignType.sign
      (planarCross (charts U (F b) - charts U (F a))
        (charts U (F y) - charts U (F a))))) = 1 := by
  have haT : a ∈ convexHull ℝ ({a, x, b} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have hbT : b ∈ convexHull ℝ ({a, x, b} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have hxT : x ∈ convexHull ℝ ({a, x, b} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have haU : a ∈ convexHull ℝ ({a, b, y} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have hbU : b ∈ convexHull ℝ ({a, b, y} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have hyU : y ∈ convexHull ℝ ({a, b, y} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  by_cases hTU : T = U
  · subst U
    have hmap : MapsTo F (convexHull ℝ ({a, x, b} : Set (ℝ × ℝ)) ∪
        convexHull ℝ ({a, b, y} : Set (ℝ × ℝ))) (convexHull ℝ (T : Set E)) :=
      fun _ hz ↦ hz.elim (fun h ↦ hT h) (fun h ↦ hU h)
    have hpair := mapped_paired_edge_cross_product L (charts T ∘ F)
      (hF.postcomp (charts T)) a b x y hab hax hay hbx hby hxy ht hu
      ((hcharts T hTf hTc).1.comp hi hmap)
    have hp := parity_sum_of_negative_product _ _ hpair
    dsimp only [Function.comp_apply] at hp
    linear_combination (norm := ring_nf) hp
    simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, sub_zero]
  · obtain ⟨v, w, c, d, hvw, hcv, hcw, hdv, hdw, hTv, hUv, havw, hbvw⟩ :=
      K.exists_common_owner_edge hTf hUf hTc hUc hTU
        (hT haT) (hU haU) (hT hbT) (hU hbU)
        (fun h ↦ hab (hi (Or.inl haT) (Or.inl hbT) h))
    have hset : ({a, b, x} : Set (ℝ × ℝ)) = {a, x, b} := by
      ext z; simp [or_comm, or_left_comm]
    have hfin : ({a, b, x} : Finset (ℝ × ℝ)) = {a, x, b} := by
      ext z; simp [or_comm, or_left_comm]
    have hRn := charted_refined_cross_ne_zero L F hF a b x hab hax hbx
      (hfin.symm ▸ ht) (by rw [hset]; exact hi.mono subset_union_left)
      (charts T) (hcharts T hTf hTc).1 (by rw [hset]; exact hT)
    have hSn := charted_refined_cross_ne_zero L F hF a b y hab hay hby hu
      (hi.mono subset_union_right) (charts U) (hcharts U hUf hUc).1 hU
    apply refined_original_cofaces_cancel number T U (sourceSign T) (sourceSign U)
      (charts T) (charts U) v w c d (F a) (F b) (F x) (F y) havw hbvw
    · simpa only [hTv, Finset.coe_insert, Finset.coe_singleton] using hT hxT
    · simpa only [hUv, Finset.coe_insert, Finset.coe_singleton] using hU hyU
    · exact (hcharts T hTf hTc).2 v (by simp [hTv]) w (by simp [hTv])
        c (by simp [hTv]) hvw hcv.symm hcw.symm
    · exact (hcharts U hUf hUc).2 v (by simp [hUv]) w (by simp [hUv])
        d (by simp [hUv]) hvw hdv.symm hdw.symm
    · exact hRn
    · exact hSn
    · exact hcancel T hTf U hUf hTc hUc hTU v w hvw
        (by simp [hTv]) (by simp [hUv])

theorem original_refined_pair_cancellation
    (sourceSign : Finset E → ZMod 2) (number : E → ℕ)
    {T U s : Finset E} {a b : E} (hs : s = {a, b})
    (hcancel : (sourceSign T + boundaryFaceParity number T s) +
      (sourceSign U + boundaryFaceParity number U s) = 1)
    {rT rU : ZMod 2}
    (hT : rT = sourceSign T)
    (hU : rU = sourceSign U) :
    (rT + boundaryFaceParity number T s) +
      (rU + boundaryFaceParity number U s) = 1 := by
  subst s
  rw [hT, hU]
  exact hcancel

end PoincareConjecture.M76.OriginalTriangleCopies
