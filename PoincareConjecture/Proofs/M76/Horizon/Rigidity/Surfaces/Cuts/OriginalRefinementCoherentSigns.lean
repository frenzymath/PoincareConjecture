import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalRefinementOrientation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalRefinementPairInjectivity

set_option autoImplicit false

open Set Geometry Classical AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem original_refined_sorted_cross_cancellation
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
    (hF : L.AffineOnFaces F) (refinedNumber : (ℝ × ℝ) → ℕ)
    {t u s : Finset (ℝ × ℝ)} (ht : t ∈ L.faces) (hu : u ∈ L.faces)
    (htc : t.card = 3) (huc : u.card = 3) (htu : t ≠ u)
    (hsc : s.card = 2) (hst : s ⊆ t) (hsu : s ⊆ u)
    (hi : InjOn F (convexHull ℝ (t : Set (ℝ × ℝ)) ∪
      convexHull ℝ (u : Set (ℝ × ℝ))))
    (T U : Finset E) (hTf : T ∈ K.faces) (hUf : U ∈ K.faces)
    (hTc : T.card = 3) (hUc : U.card = 3)
    (hT : MapsTo F (convexHull ℝ (t : Set (ℝ × ℝ)))
      (convexHull ℝ (T : Set E)))
    (hU : MapsTo F (convexHull ℝ (u : Set (ℝ × ℝ)))
      (convexHull ℝ (U : Set E)))
    (p q : Fin 3 → ℝ × ℝ) (hpi : Function.Injective p) (hqi : Function.Injective q)
    (hpt : Finset.univ.image p = t) (hqu : Finset.univ.image q = u)
    (hpn : StrictMono (refinedNumber ∘ p)) (hqn : StrictMono (refinedNumber ∘ q)) :
    ((sourceSign T + orientationSignParity (SignType.sign
        (planarCross (charts T (F (p 1)) - charts T (F (p 0)))
          (charts T (F (p 2)) - charts T (F (p 0)))))) +
      boundaryFaceParity refinedNumber t s) +
    ((sourceSign U + orientationSignParity (SignType.sign
        (planarCross (charts U (F (q 1)) - charts U (F (q 0)))
          (charts U (F (q 2)) - charts U (F (q 0)))))) +
      boundaryFaceParity refinedNumber u s) = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hsc
  obtain ⟨x, hx, hxt⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hst, by simp [hab, htc]⟩
  obtain ⟨y, hy, hyu⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hsu, by simp [hab, huc]⟩
  have hxne : x ≠ a ∧ x ≠ b := by simpa using hx
  have hyne : y ≠ a ∧ y ≠ b := by simpa using hy
  have hxy : x ≠ y := by intro h; exact htu (hxt.symm.trans (h ▸ hyu))
  have htx : ({a, x, b} : Finset (ℝ × ℝ)) = t := by
    rw [← hxt]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have huy : ({a, b, y} : Finset (ℝ × ℝ)) = u := by
    rw [← hyu]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have htxs : ({a, x, b} : Set (ℝ × ℝ)) = (t : Set (ℝ × ℝ)) := by
    rw [← htx]
    simp
  have huys : ({a, b, y} : Set (ℝ × ℝ)) = (u : Set (ℝ × ℝ)) := by
    rw [← huy]
    simp
  have hpind := charted_refined_triangle_independent L F hF ht
    (hi.mono subset_union_left) (charts T) (hcharts T hTf hTc).1 hT p hpi hpt
  have hqind := charted_refined_triangle_independent L F hF hu
    (hi.mono subset_union_right) (charts U) (hcharts U hUf hUc).1 hU q hqi hqu
  have hpa := mapped_numbered_edge_apex_parity refinedNumber p hpi hpn (charts T ∘ F)
    (planar_triangle_cross_ne_zero _ hpind) a b x
    (hpt.symm ▸ hst (by simp)) (hpt.symm ▸ hst (by simp))
    (hpt.symm ▸ hxt ▸ Finset.mem_insert_self _ _) hab hxne.1.symm hxne.2.symm
  have hqa := mapped_numbered_edge_apex_parity refinedNumber q hqi hqn (charts U ∘ F)
    (planar_triangle_cross_ne_zero _ hqind) a b y
    (hqu.symm ▸ hsu (by simp)) (hqu.symm ▸ hsu (by simp))
    (hqu.symm ▸ hyu ▸ Finset.mem_insert_self _ _) hab hyne.1.symm hyne.2.symm
  have hsign := charted_refined_cofaces_cancel K number sourceSign charts hcharts hcancel
    L F hF a b x y hab hxne.1.symm hyne.1.symm hxne.2.symm hyne.2.symm hxy
    (htx.symm ▸ ht) (huy.symm ▸ hu) (by rwa [htxs, huys])
    T U hTf hUf hTc hUc (by rwa [htxs]) (by rwa [huys])
  dsimp only [Function.comp_apply] at hpa hqa
  rw [hpa, hqa, hpt, hqu] at hsign
  unfold Dehn.orderedCofaceParity at hsign
  linear_combination (norm := ring_nf) hsign
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, neg_zero]

structure OriginalRefinementCoherentSigns
    (K : SimplicialComplex ℝ E) (number : E → ℕ) (sourceSign : Finset E → ZMod 2)
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (refinedNumber : (ℝ × ℝ) → ℕ)
    (F : (ℝ × ℝ) → E) where
  charts : Finset E → E →ᴬ[ℝ] (ℝ × ℝ)
  charts_spec : ∀ T ∈ K.faces, T.card = 3 →
    InjOn (charts T) (convexHull ℝ (T : Set E)) ∧
    ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c →
      orientationSignParity (SignType.sign
        (planarCross (charts T b - charts T a) (charts T c - charts T a))) =
        Dehn.orderedCofaceParity number T a b
  owner : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3} →
    {T : Finset E // T ∈ K.faces ∧ T.card = 3}
  owner_mapsTo : ∀ t, MapsTo F (convexHull ℝ (t.val : Set (ℝ × ℝ)))
    (convexHull ℝ ((owner t).val : Set E))
  enumeration : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3} → Fin 3 → ℝ × ℝ
  enumeration_spec : ∀ t, Function.Injective (enumeration t) ∧
    Finset.univ.image (enumeration t) = t.val ∧ StrictMono (refinedNumber ∘ enumeration t)
  mapped_enumeration_independent : ∀ t,
    AffineIndependent ℝ ((charts (owner t).val ∘ F) ∘ enumeration t)
  sign : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3} → ZMod 2
  sign_eq : ∀ t, sign t = sourceSign (owner t).val + orientationSignParity (SignType.sign
    (planarCross
      (charts (owner t).val (F (enumeration t 1)) - charts (owner t).val (F (enumeration t 0)))
      (charts (owner t).val (F (enumeration t 2)) - charts (owner t).val (F (enumeration t 0)))))
  coherent : ∀ t u, t ≠ u → ∀ s : Finset (ℝ × ℝ),
    s.card = 2 → s ⊆ t.val → s ⊆ u.val →
    (sign t + boundaryFaceParity refinedNumber t.val s) +
      (sign u + boundaryFaceParity refinedNumber u.val s) = 1

theorem nonempty_originalRefinementCoherentSigns
    (K : SimplicialComplex ℝ E) (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sourceSign : Finset E → ZMod 2)
    (hcancel : ∀ T ∈ K.faces, ∀ U ∈ K.faces, T.card = 3 → U.card = 3 → T ≠ U →
      ∀ a b : E, a ≠ b → {a, b} ⊆ T → {a, b} ⊆ U →
      (sourceSign T + boundaryFaceParity number T {a, b}) +
        (sourceSign U + boundaryFaceParity number U {a, b}) = 1)
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (refinedNumber : (ℝ × ℝ) → ℕ)
    (hrefinedNumber : InjOn refinedNumber L.vertices)
    (F : (ℝ × ℝ) → E) (hF : L.AffineOnFaces F)
    (howners : ∀ t ∈ L.faces, ∃ T ∈ K.faces, T.card = 3 ∧
      MapsTo F (convexHull ℝ (t : Set (ℝ × ℝ))) (convexHull ℝ (T : Set E)))
    (hfaces : ∀ t ∈ L.faces, InjOn F (convexHull ℝ (t : Set (ℝ × ℝ))))
    (hpairs : ∀ (s t u : Finset (ℝ × ℝ)), s.card = 2 → t ∈ L.faces → u ∈ L.faces →
      t.card = 3 → u.card = 3 → s ⊆ t → s ⊆ u → t ≠ u →
      InjOn F (convexHull ℝ (t : Set (ℝ × ℝ)) ∪
        convexHull ℝ (u : Set (ℝ × ℝ)))) :
    Nonempty (OriginalRefinementCoherentSigns K number sourceSign L refinedNumber F) := by
  have hchart (T : Finset E) : ∃ R : E →ᴬ[ℝ] (ℝ × ℝ),
      T ∈ K.faces → T.card = 3 → InjOn R (convexHull ℝ (T : Set E)) ∧
      ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c →
        orientationSignParity (SignType.sign
          (planarCross (R b - R a) (R c - R a))) =
          Dehn.orderedCofaceParity number T a b := by
    by_cases hT : T ∈ K.faces ∧ T.card = 3
    · obtain ⟨R, hR⟩ := exists_original_triangle_orientation_chart K number hnumber hT.1 hT.2
      exact ⟨R, fun _ _ ↦ hR⟩
    · exact ⟨0, fun hTf hTc ↦ (hT ⟨hTf, hTc⟩).elim⟩
  choose charts hcharts using hchart
  let Tri := {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3}
  have howner (t : Tri) : ∃ T : {T : Finset E // T ∈ K.faces ∧ T.card = 3},
      MapsTo F (convexHull ℝ (t.val : Set (ℝ × ℝ))) (convexHull ℝ (T.val : Set E)) := by
    obtain ⟨T, hTf, hTc, hm⟩ := howners t.val t.property.1
    exact ⟨⟨T, hTf, hTc⟩, hm⟩
  choose owner howner using howner
  obtain ⟨p, _, hp, _, _⟩ := exists_planar_sorted_cross_signs L refinedNumber hrefinedNumber
  let sign : Tri → ZMod 2 := fun t ↦ sourceSign (owner t).val +
    orientationSignParity (SignType.sign
      (planarCross (charts (owner t).val (F (p t 1)) - charts (owner t).val (F (p t 0)))
        (charts (owner t).val (F (p t 2)) - charts (owner t).val (F (p t 0)))))
  have hmapind (t : Tri) : AffineIndependent ℝ ((charts (owner t).val ∘ F) ∘ p t) :=
    charted_refined_triangle_independent L F hF t.property.1 (hfaces _ t.property.1)
      (charts (owner t).val) (hcharts _ (owner t).property.1 (owner t).property.2).1
      (howner t) (p t) (hp t).1 (hp t).2.1
  refine ⟨⟨charts, hcharts, owner, howner, p,
    fun t ↦ ⟨(hp t).1, (hp t).2.1, (hp t).2.2.1⟩,
    hmapind, sign, fun _ ↦ rfl, ?_⟩⟩
  intro t u htu s hsc hst hsu
  have htu' : t.val ≠ u.val := fun h ↦ htu (Subtype.ext h)
  exact original_refined_sorted_cross_cancellation K number sourceSign charts hcharts hcancel
    L F hF refinedNumber t.property.1 u.property.1 t.property.2 u.property.2 htu'
    hsc hst hsu
    (hpairs s t.val u.val hsc t.property.1 u.property.1 t.property.2 u.property.2 hst hsu htu')
    (owner t).val (owner u).val (owner t).property.1 (owner u).property.1
    (owner t).property.2 (owner u).property.2 (howner t) (howner u)
    (p t) (p u) (hp t).1 (hp u).1 (hp t).2.1 (hp u).2.1 (hp t).2.2.1 (hp u).2.2.1

omit [FiniteDimensional ℝ E] in

theorem OriginalRefinementCoherentSigns.signed_edge_cross_eq
    {K : SimplicialComplex ℝ E} {number : E → ℕ} {sourceSign : Finset E → ZMod 2}
    {L : SimplicialComplex ℝ (ℝ × ℝ)} {refinedNumber : (ℝ × ℝ) → ℕ}
    {F : (ℝ × ℝ) → E}
    (O : OriginalRefinementCoherentSigns K number sourceSign L refinedNumber F)
    (t : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3})
    (a b x : ℝ × ℝ) (ha : a ∈ t.val) (hb : b ∈ t.val) (hx : x ∈ t.val)
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x) :
    O.sign t + Dehn.orderedCofaceParity refinedNumber t.val a b =
      sourceSign (O.owner t).val + orientationSignParity (SignType.sign
        (planarCross (O.charts (O.owner t).val (F b) - O.charts (O.owner t).val (F a))
          (O.charts (O.owner t).val (F x) - O.charts (O.owner t).val (F a)))) := by
  have h := mapped_numbered_edge_apex_parity refinedNumber (O.enumeration t)
    (O.enumeration_spec t).1 (O.enumeration_spec t).2.2
    (O.charts (O.owner t).val ∘ F)
    (planar_triangle_cross_ne_zero _ (O.mapped_enumeration_independent t)) a b x
    ((O.enumeration_spec t).2.1.symm ▸ ha) ((O.enumeration_spec t).2.1.symm ▸ hb)
    ((O.enumeration_spec t).2.1.symm ▸ hx) hab hax hbx
  rw [(O.enumeration_spec t).2.1] at h
  dsimp only [Function.comp_apply] at h
  rw [O.sign_eq, h]
  exact add_assoc _ _ _

omit [FiniteDimensional ℝ E] in

theorem OriginalRefinementCoherentSigns.edge_cross_ne_zero
    {K : SimplicialComplex ℝ E} {number : E → ℕ} {sourceSign : Finset E → ZMod 2}
    {L : SimplicialComplex ℝ (ℝ × ℝ)} {refinedNumber : (ℝ × ℝ) → ℕ}
    {F : (ℝ × ℝ) → E}
    (O : OriginalRefinementCoherentSigns K number sourceSign L refinedNumber F)
    (t : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3})
    (a b x : ℝ × ℝ) (ha : a ∈ t.val) (hb : b ∈ t.val) (hx : x ∈ t.val)
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x) :
    planarCross (O.charts (O.owner t).val (F b) - O.charts (O.owner t).val (F a))
      (O.charts (O.owner t).val (F x) - O.charts (O.owner t).val (F a)) ≠ 0 := by
  obtain ⟨ia, _, hia⟩ := Finset.mem_image.mp ((O.enumeration_spec t).2.1.symm ▸ ha)
  obtain ⟨ib, _, hib⟩ := Finset.mem_image.mp ((O.enumeration_spec t).2.1.symm ▸ hb)
  obtain ⟨ix, _, hix⟩ := Finset.mem_image.mp ((O.enumeration_spec t).2.1.symm ▸ hx)
  have hiab : ia ≠ ib := fun h ↦ hab (hia.symm.trans ((congrArg (O.enumeration t) h).trans hib))
  have hiax : ia ≠ ix := fun h ↦ hax (hia.symm.trans ((congrArg (O.enumeration t) h).trans hix))
  have hibx : ib ≠ ix := fun h ↦ hbx (hib.symm.trans ((congrArg (O.enumeration t) h).trans hix))
  let p : Fin 3 → Fin 3 := ![ia, ib, ix]
  have hpi : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  have hind := (O.mapped_enumeration_independent t).comp_embedding ⟨p, hpi⟩
  simpa [Function.comp_def, p, hia, hib, hix] using planar_triangle_cross_ne_zero _ hind

omit [FiniteDimensional ℝ E] in

theorem OriginalRefinementCoherentSigns.signed_edge_scalar_parity
    {K : SimplicialComplex ℝ E} {number : E → ℕ} {sourceSign : Finset E → ZMod 2}
    {L : SimplicialComplex ℝ (ℝ × ℝ)} {refinedNumber : (ℝ × ℝ) → ℕ}
    {F : (ℝ × ℝ) → E}
    (O : OriginalRefinementCoherentSigns K number sourceSign L refinedNumber F)
    (t : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3})
    (a b x : ℝ × ℝ) (ha : a ∈ t.val) (hb : b ∈ t.val) (hx : x ∈ t.val)
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x)
    (v w c : E) (howner : (O.owner t).val = {v, w, c})
    (hvw : v ≠ w) (hvc : v ≠ c) (hwc : w ≠ c)
    (r s : ℝ) (har : F a - v = r • (w - v)) (hbs : F b - v = s • (w - v)) :
    s - r ≠ 0 ∧
      O.sign t + Dehn.orderedCofaceParity refinedNumber t.val a b =
        sourceSign (O.owner t).val + Dehn.orderedCofaceParity number (O.owner t).val v w +
          orientationSignParity (SignType.sign (s - r)) := by
  have hcross := O.edge_cross_ne_zero t a b x ha hb hx hab hax hbx
  have hxowner : F x ∈ convexHull ℝ ({v, w, c} : Set E) := by
    simpa only [howner, Finset.coe_insert, Finset.coe_singleton] using
      O.owner_mapsTo t (subset_convexHull ℝ _ hx)
  have hsign := refined_original_edge_cross_sign (O.charts (O.owner t).val)
    v w c (F a) (F b) (F x) r s har hbs hxowner hcross
  have hn : SignType.sign (s - r) * SignType.sign
      (planarCross (O.charts (O.owner t).val w - O.charts (O.owner t).val v)
        (O.charts (O.owner t).val c - O.charts (O.owner t).val v)) ≠ 0 := by
    rw [← hsign]
    exact sign_ne_zero.mpr hcross
  have hpar := (O.charts_spec _ (O.owner t).property.1 (O.owner t).property.2).2
    v (by simp [howner]) w (by simp [howner]) c (by simp [howner]) hvw hvc hwc
  refine ⟨sign_ne_zero.mp (mul_ne_zero_iff.mp hn).1, ?_⟩
  rw [O.signed_edge_cross_eq t a b x ha hb hx hab hax hbx, hsign,
    orientationSignParity_mul_nonzero _ _ (mul_ne_zero_iff.mp hn).1
      (mul_ne_zero_iff.mp hn).2, hpar]
  ac_rfl

end PoincareConjecture.M76.OriginalTriangleCopies

namespace PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)
  (hbound : ∀ s ∈ K.faces, s.card ≤ 3)

include hbound

theorem exists_marked_planar_original_refinement_with_orientation
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 3)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sourceSign : Finset E → ZMod 2)
    (hcancel : ∀ T ∈ K.faces, ∀ U ∈ K.faces, T.card = 3 → U.card = 3 → T ≠ U →
      ∀ a b : E, a ≠ b → {a, b} ⊆ T → {a, b} ⊆ U →
      (sourceSign T + boundaryFaceParity number T {a, b}) +
        (sourceSign U + boundaryFaceParity number U {a, b}) = 1) :
    ∃ C : (PeriodicSquare.squareCarrier 1) ≃ₜ A.carrier, C.IsFinitePL ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 0 ↔ x.val.2 = 0) ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 2 ↔ x.val.2 = 1) ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 3 ↔ x.val.1 = 0) ∧
      (∀ x, (C x).val ∈ A.longBoundaryArc 1 ↔ x.val.1 = 1) ∧
      ∃ (f : (ℝ × ℝ) →
          ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)))
        (L : SimplicialComplex ℝ (ℝ × ℝ)),
        (∀ x, f x.val = (C x).val) ∧ L.faces.Finite ∧
        L.space = PeriodicSquare.squareCarrier 1 ∧ L.AffineOnFaces f ∧
        L.AffineOnFaces (A.sourceMap ∘ f) ∧
        (∀ t ∈ L.faces, InjOn (A.sourceMap ∘ f)
          (convexHull ℝ (t : Set (ℝ × ℝ)))) ∧
        (A.sourceMap ∘ f) '' L.space = K.space ∧
        ∀ refinedNumber : (ℝ × ℝ) → ℕ, InjOn refinedNumber L.vertices →
          Nonempty (OriginalRefinementCoherentSigns K number sourceSign L refinedNumber
            (A.sourceMap ∘ f)) := by
  obtain ⟨C, hC, hbottom, htop, hleft, hright, f, F, L, hval, hF,
    hf, _, hfinite, hspace, hFL, himage, hfaces, _, howners⟩ :=
    A.exists_marked_planar_original_refinement hbound hpure
  subst F
  refine ⟨C, hC, hbottom, htop, hleft, hright, f, L,
    hval, hfinite, hspace, hf, hFL, hfaces, himage, ?_⟩
  intro refinedNumber hrefinedNumber
  apply nonempty_originalRefinementCoherentSigns K number hnumber sourceSign hcancel
    L refinedNumber hrefinedNumber (A.sourceMap ∘ f) hFL howners hfaces
  intro s t u hs ht hu htc huc hst hsu htu
  exact A.sourceMap_comp_injOn_triangle_pair hbound C hbottom htop hleft hright L hspace
    f (fun x ↦ (hval x).symm) hf s t u hs ht hu htc huc hst hsu htu

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
